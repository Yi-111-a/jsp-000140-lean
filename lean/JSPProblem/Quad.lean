import JSPProblem.Census
import JSPProblem.Tables

/-!
# JSP-000140 — THE FOUR-SET CENSUS: where the tight `K₄`s live

`Census.lean` proves the **5-or-6 dichotomy**: for every four-element vertex set `S` of an
admissible colouring,

    `|colorsOn c S| + |doubledIn c S| = 6`,   and `|doubledIn c S| ≤ 1`,

so the four-sets of `K_n` split into the *tight* ones (`fiveFourSets c`, spanning exactly five
colours) and the *loose* ones (spanning six).  `Census.lean` names the counting step that was
still missing — "`sum_twoFourSets`: summing over colours, the `K₄`s with a doubled colour are
counted once each" — and its header marks §2*/§3 as **STILL TO BE PROVED**.  This file proves
that step, together with the first half of its companion `card_twoFourSets`.

## §1 — the main theorem: every two-edge path sits in `n-3` tight four-sets

A two-edge path `a - v - b` of colour `i` has its two edges in exactly `n-3` four-sets (one for
each choice of the fourth vertex), and each of those four-sets is **tight**: its six edges carry
the pattern `(2,1,1,1,1)`, because `Definitions.classIn_card_le_two` forbids a third `i`-edge on
four vertices.  Different paths give different tight four-sets.  Hence the trade-off theorem

* **`fiveFourSets_ge_paths_mul`** — `(n-3) * Paths c ≤ |fiveFourSets c|`: *the fewer colours a
  colouring of `K_n` uses, the more tight four-sets it must carry* — whose shape is then fixed by
  `Paths.mul_n_sub_one_le` (`k ≥ (n-1) - Paths c / n`).

## §2 — the census identity `sum_twoFourSets`

* **`sum_twoFourSets`** — `∑_i |twoFourSets c i| = |fiveFourSets c|`, the step `Census.lean` §2*
  names and leaves unproved: the four-sets with a doubled colour are counted **once** each,
  because a `K₄` has at most one doubled colour (`Census.card_doubledIn_le_one`), and every tight
  four-set has exactly one.
* **`card_twoFourSets_ge_paths_mul`** — the per-colour half of `Census.card_twoFourSets`:
  `(twoA c i).card * (n-3) ≤ |twoFourSets c i|`, proved by the injection `x ↦ insert x (pathVerts
  c i v)`.

## §3 — consequences

* **`fiveFourSets_le_fourSets`** — at most `C(n,4)` tight four-sets, so `(n-3) * Paths c ≤
  |fourSets n|`: a **second upper bound on the number of two-edge paths** of an admissible
  colouring (the first being `Cherry.three_mul_paths_le`).
* **`fiveFourSets_ge_of_colours`** — `(n-3) * n * (n-1-k) ≤ |fiveFourSets c|` for every admissible
  `k`-colouring: the trade-off read off `k` alone.
* **`fiveSixthShape_tight`** — **if the catalog counting bound `6k = 5(n-1)` is attained, then at
  least `(n-3) * n * (n-1) / 6` of the `C(n,4)` four-sets span exactly five colours**, a fraction
  `4/(n-2)` of all `K₄`s.  Together with `Rigidity.tight_pathFinset_is_STS` (in the extremal case
  the two-edge paths form a Steiner triple system) this says that an extremal colouring is rigid
  in **two** directions at once: it carries an `STS(n)` of paths *and* macroscopically many tight
  `K₄`s.

## §4 — machine-checked instances

`fiveFourSets_sixCol`, `fiveFourSets_nineCol`, `fiveFourSets_tenCol`, `fiveFourSets_elevenCol`
give the exact number of tight four-sets of the four verified constructions of `Tables.lean`,
each checked by `native_decide` over all `C(n,4)` vertex sets.
-/

set_option maxHeartbeats 1000000

namespace JSP140

variable {n k : ℕ}

/-- A two-element finset has at most two elements. -/
theorem card_pair_le_two {α : Type*} [DecidableEq α] (a b : α) : ({a, b} : Finset α).card ≤ 2 :=
  Finset.card_le_two

/-- A finset `{x, y}` with `x ≠ y` has exactly two elements. -/
theorem card_pair_eq_two {α : Type*} [DecidableEq α] {x y : α} (h : x ≠ y) :
    ({x, y} : Finset α).card = 2 := by
  rw [show ({x, y} : Finset α) = insert x {y} from rfl,
    Finset.card_insert_of_notMem (by simp [h]), Finset.card_singleton]

/-- **A COMMON VERTEX OF TWO DISTINCT EDGES IS DETERMINED.**  If `q ≠ r` and
`s(p,q) = s(p',q')`, `s(p,r) = s(p',r')`, then `p = p'`. -/
theorem common_vertex_eq {α : Type*} {p q r p' q' r' : α} (hqr : q ≠ r) (h1 : s(p, q) = s(p', q'))
    (h2 : s(p, r) = s(p', r')) : p = p' := by
  rcases sym2_inj h1 with ⟨h1a, _⟩ | ⟨_, h1b⟩
  · exact h1a
  · rcases sym2_inj h2 with ⟨h2a, _⟩ | ⟨_, h2b⟩
    · exact h2a
    · exact absurd (h1b ▸ h2b) (fun hh => hqr hh.symm)

/-! ### §0  A vertex has at most two neighbours in a colour class -/

/-- **THE GLOBAL DEGREE BOUND.**  `ColorClass.nbrsIn_card_le_two` states the degree bound inside a
vertex set not containing `v`; taking that set to be `V ∖ {v}` (which contains every neighbour of
`v`) gives the statement the whole file uses: **no colour class has a vertex of degree three or
more**. -/
theorem nb_univ_card_le_two {n k : ℕ} {c : Col n k} (hc : Admissible c) (i : Fin k) (v : Verts n) :
    (nb c i v (Finset.univ : Finset (Verts n))).card ≤ 2 := by
  have hkeyfins : nbrsIn c i v (Finset.univ \ {v} : Finset (Verts n))
      = nb c i v (Finset.univ : Finset (Verts n)) := by
    ext y
    rw [mem_nbrsIn, mem_nb]
    constructor
    · rintro ⟨hy1, hy2⟩
      exact ⟨fun h => (Finset.mem_sdiff.mp hy1).2 (Finset.mem_singleton.mpr h),
        Finset.mem_univ y, hy2⟩
    · rintro ⟨hy1, hy2, hy3⟩
      exact ⟨Finset.mem_sdiff.mpr ⟨hy2, fun hxy => hy1 (Finset.mem_singleton.mp hxy)⟩, hy3⟩
  calc (nb c i v (Finset.univ : Finset (Verts n))).card
      = (nbrsIn c i v (Finset.univ \ {v} : Finset (Verts n))).card :=
        congrArg Finset.card hkeyfins.symm
    _ ≤ 2 := nbrsIn_card_le_two hc i (Finset.univ \ {v} : Finset (Verts n))
      (fun h => (Finset.mem_sdiff.mp h).2 (Finset.mem_singleton.mpr rfl))

/-- The two colour-`i` neighbours of a path centre are distinct vertices, neither of them `v`. -/
theorem exists_pair_of_twoA {n k : ℕ} {c : Col n k} {i : Fin k} {v : Verts n}
    (hv : v ∈ twoA c i) : ∃ a b : Verts n, a ≠ b ∧
      nb c i v (Finset.univ : Finset (Verts n)) = {a, b} ∧ a ≠ v ∧ b ≠ v := by
  obtain ⟨a, b, hab, hset⟩ := Finset.card_eq_two.mp (mem_twoA.mp hv)
  refine ⟨a, b, hab, hset, ?_, ?_⟩
  · intro h
    have hma : a ∈ nb c i v (Finset.univ : Finset (Verts n)) := by rw [hset]; simp
    exact (mem_nb.mp hma).1 h
  · intro h
    have hmb : b ∈ nb c i v (Finset.univ : Finset (Verts n)) := by rw [hset]; simp
    exact (mem_nb.mp hmb).1 h

/-! ### §1  the three vertices of a two-edge path -/

/-- **THE VERTEX SET OF A TWO-EDGE PATH.**  For a centre `v` of a colour-`i` path this is the
three-element set `{v} ∪ (colour-`i` neighbourhood of `v`)`. -/
def pathVerts {n k : ℕ} (c : Col n k) (i : Fin k) (v : Verts n) : Finset (Verts n) :=
  insert v (nb c i v (Finset.univ : Finset (Verts n)))

theorem mem_pathVerts_self {n k : ℕ} (c : Col n k) (i : Fin k) (v : Verts n) :
    v ∈ pathVerts c i v := by
  exact Finset.mem_insert_self v _

theorem card_pathVerts {n k : ℕ} {c : Col n k} {i : Fin k} {v : Verts n} (hv : v ∈ twoA c i) :
    (pathVerts c i v).card = 3 := by
  have hne : v ∉ nb c i v (Finset.univ : Finset (Verts n)) := by
    intro h
    exact (mem_nb.mp h).1 rfl
  rw [pathVerts, Finset.card_insert_of_notMem hne]
  rw [mem_twoA.mp hv]

theorem pathVerts_subset_univ {n k : ℕ} (c : Col n k) (i : Fin k) (v : Verts n) :
    pathVerts c i v ⊆ (Finset.univ : Finset (Verts n)) :=
  Finset.subset_univ _

/-! ### §2  a two-edge path is spanned by `n-3` tight four-sets -/

/-- **THE FOUR-SETS DOUBLED AT A GIVEN CENTRE**: the four-element vertex sets carrying exactly two
colour-`i` edges, those two edges meeting at `v` — i.e. the four-sets spanned by the two-edge path
of colour `i` centred at `v`. -/
def pathFourSets {n k : ℕ} (c : Col n k) (i : Fin k) (v : Verts n) : Finset (Finset (Verts n)) :=
  (twoFourSets c i).filter fun S => v ∈ S ∧ (nb c i v S).card = 2

theorem mem_pathFourSets {n k : ℕ} {c : Col n k} {i : Fin k} {v : Verts n} {S : Finset (Verts n)} :
    S ∈ pathFourSets c i v ↔
      S.card = 4 ∧ (classIn c i S).card = 2 ∧ v ∈ S ∧ (nb c i v S).card = 2 := by
  rw [pathFourSets, Finset.mem_filter]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨(mem_twoFourSets.mp h1).1, (mem_twoFourSets.mp h1).2, h2, h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨mem_twoFourSets.mpr ⟨h1, h2⟩, h3⟩

/-- **A TWO-EDGE PATH IS SPANNED BY THE FOUR-SET OF EVERY FOURTH VERTEX.**  If `v` is the centre of
a colour-`i` path and `x` is any vertex outside its three vertices, then `{x} ∪ (pathVerts c i v)`
is a four-element set on which colour `i` occurs exactly twice, the two `i`-edges meeting at `v`;
the four-set is therefore *tight*. -/
theorem mem_pathFourSets_insert {n k : ℕ} {c : Col n k} (hc : Admissible c) (i : Fin k)
    {v x : Verts n} (hv : v ∈ twoA c i) (hx : x ∉ pathVerts c i v) :
    insert x (pathVerts c i v) ∈ pathFourSets c i v := by
  obtain ⟨a, b, hab, hN, hva, hvb⟩ := exists_pair_of_twoA hv
  have ha : a ∈ nb c i v (Finset.univ : Finset (Verts n)) := by rw [hN]; simp
  have hb : b ∈ nb c i v (Finset.univ : Finset (Verts n)) := by rw [hN]; simp
  have haV : a ∈ pathVerts c i v := Finset.mem_insert_of_mem ha
  have hbV : b ∈ pathVerts c i v := Finset.mem_insert_of_mem hb
  have hvV : v ∈ pathVerts c i v := Finset.mem_insert_self v _
  have hScard : (insert x (pathVerts c i v)).card = 4 := by
    rw [Finset.card_insert_of_notMem hx, card_pathVerts hv]
  have hnb : nb c i v (insert x (pathVerts c i v))
      = nb c i v (Finset.univ : Finset (Verts n)) := by
    ext y
    rw [mem_nb, mem_nb]
    constructor
    · rintro ⟨hy1, hy2, hy3⟩
      exact ⟨hy1, Finset.mem_univ y, hy3⟩
    · rintro ⟨hy1, hy2, hy3⟩
      refine ⟨hy1, ?_, hy3⟩
      have hynb : y ∈ nb c i v (Finset.univ : Finset (Verts n)) :=
        mem_nb.mpr ⟨hy1, Finset.mem_univ y, hy3⟩
      rw [hN] at hynb
      simp only [Finset.mem_insert, Finset.mem_singleton] at hynb
      rcases hynb with rfl | rfl
      · exact Finset.mem_insert_of_mem haV
      · exact Finset.mem_insert_of_mem hbV
  have hmem1 : s(v, a) ∈ classIn c i (insert x (pathVerts c i v)) :=
    mem_classIn.mpr ⟨mem_edgeFinset_mk (a := v) (b := a) (Finset.mem_insert_of_mem hvV)
      (Finset.mem_insert_of_mem haV) hva.symm, (mem_nb.mp ha).2.2⟩
  have hmem2 : s(v, b) ∈ classIn c i (insert x (pathVerts c i v)) :=
    mem_classIn.mpr ⟨mem_edgeFinset_mk (a := v) (b := b) (Finset.mem_insert_of_mem hvV)
      (Finset.mem_insert_of_mem hbV) hvb.symm, (mem_nb.mp hb).2.2⟩
  have hne : s(v, a) ≠ s(v, b) := by
    intro h
    rcases sym2_inj h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact hab h2
    · exact hva h2
  have hsub : ({s(v, a), s(v, b)} : Finset (Sym2 (Verts n)))
      ⊆ classIn c i (insert x (pathVerts c i v)) := by
    intro e he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl
    · exact hmem1
    · exact hmem2
  have h1 := classIn_card_le_two hc i (insert x (pathVerts c i v)) hScard
  have hne1 : s(v, a) ≠ s(v, b) := fun h => hab (sym2_inj_right h)
  have hcard2 : (classIn c i (insert x (pathVerts c i v))).card = 2 :=
    le_antisymm h1 (by rw [← card_pair_eq_two hne1]; exact Finset.card_le_card hsub)
  rw [mem_pathFourSets]
  exact ⟨hScard, hcard2,
    Finset.mem_insert_of_mem hvV, (by rw [hnb]; exact mem_twoA.mp hv)⟩

/-- **`n-3` tight four-sets per path centre:** every vertex outside the three vertices of the
two-edge path of colour `i` centred at `v` gives a distinct tight four-set. -/
theorem card_pathFourSets_ge {n k : ℕ} {c : Col n k} (hc : Admissible c) (i : Fin k)
    {v : Verts n} (hv : v ∈ twoA c i) : n - 3 ≤ (pathFourSets c i v).card := by
  have hcard2 : (Finset.univ \ pathVerts c i v : Finset (Verts n)).card = n - 3 := by
    have hsum := Finset.card_sdiff_add_card_eq_card (pathVerts_subset_univ c i v)
    rw [Finset.card_univ, Fintype.card_fin, card_pathVerts hv] at hsum
    omega
  have hle : (Finset.univ \ pathVerts c i v).card ≤ (pathFourSets c i v).card :=
    Finset.card_le_card_of_injOn (fun x => insert x (pathVerts c i v))
      (fun x hx => mem_pathFourSets_insert hc i hv (Finset.mem_sdiff.mp hx).2)
      (fun x hx1 y hy1 hxy => by
        have hxy' : insert x (pathVerts c i v) = insert y (pathVerts c i v) := by simpa using hxy
        have hmem : y ∈ insert x (pathVerts c i v) := by
          rw [hxy']; exact Finset.mem_insert_self y (pathVerts c i v)
        rcases Finset.mem_insert.mp hmem with heq | hmem
        · exact heq.symm
        · exact absurd hmem (Finset.mem_sdiff.mp hy1).2)
  omega

/-- A four-set doubled in colour `i` at `v` forces `v` to be a path centre of colour `i`. -/
theorem twoA_of_mem_pathFourSets {n k : ℕ} {c : Col n k} (hc : Admissible c) {i : Fin k}
    {v : Verts n} {S : Finset (Verts n)} (h : S ∈ pathFourSets c i v) : v ∈ twoA c i := by
  have h2 : 2 ≤ (nb c i v (Finset.univ : Finset (Verts n))).card := by
    have hsub : nb c i v S ⊆ nb c i v (Finset.univ : Finset (Verts n)) := by
      intro x hx
      exact mem_nb.mpr ⟨(mem_nb.mp hx).1, Finset.mem_univ _, (mem_nb.mp hx).2.2⟩
    have hle := Finset.card_le_card hsub
    have h2' := (mem_pathFourSets.mp h).2.2.2
    omega
  exact mem_twoA.mpr (le_antisymm (nb_univ_card_le_two hc i v) h2)

/-- **THE PATH CENTRE OF A FOUR-SET IS DETERMINED BY IT AND THE COLOUR.**  If a four-element vertex
set carries exactly two colour-`i` edges which meet at `v`, and also at `v'`, then `v = v'`:
the two edges `s(p,q)`, `s(p,r)` have a unique common vertex `p` (`common_vertex_eq`). -/
theorem eq_v_of_mem_pathFourSets {n k : ℕ} {c : Col n k} (hc : Admissible c) {i : Fin k}
    {v v' : Verts n} {S : Finset (Verts n)} (hv : S ∈ pathFourSets c i v)
    (hv' : S ∈ pathFourSets c i v') : v = v' := by
  obtain ⟨a, b, hab, hN, hva, hvb⟩ := exists_pair_of_twoA (twoA_of_mem_pathFourSets hc hv)
  obtain ⟨a', b', hab', hN', hva', hvb'⟩ :=
    exists_pair_of_twoA (twoA_of_mem_pathFourSets hc hv')
  have ha : a ∈ nb c i v (Finset.univ : Finset (Verts n)) := by rw [hN]; simp
  have hb : b ∈ nb c i v (Finset.univ : Finset (Verts n)) := by rw [hN]; simp
  have ha' : a' ∈ nb c i v' (Finset.univ : Finset (Verts n)) := by rw [hN']; simp
  have hb' : b' ∈ nb c i v' (Finset.univ : Finset (Verts n)) := by rw [hN']; simp
  have hsubS : nb c i v S ⊆ nb c i v (Finset.univ : Finset (Verts n)) := by
    intro x hx
    exact mem_nb.mpr ⟨(mem_nb.mp hx).1, Finset.mem_univ x, (mem_nb.mp hx).2.2⟩
  have hsubS' : nb c i v' S ⊆ nb c i v' (Finset.univ : Finset (Verts n)) := by
    intro x hx
    exact mem_nb.mpr ⟨(mem_nb.mp hx).1, Finset.mem_univ x, (mem_nb.mp hx).2.2⟩
  have hnbv : nb c i v S = nb c i v (Finset.univ : Finset (Verts n)) :=
    Finset.eq_of_subset_of_card_le hsubS (by
      rw [(mem_pathFourSets.mp hv).2.2.2, mem_twoA.mp (twoA_of_mem_pathFourSets hc hv)])
  have hnbv' : nb c i v' S = nb c i v' (Finset.univ : Finset (Verts n)) :=
    Finset.eq_of_subset_of_card_le hsubS' (by
      rw [(mem_pathFourSets.mp hv').2.2.2, mem_twoA.mp (twoA_of_mem_pathFourSets hc hv')])
  have haS : a ∈ S := (mem_nb.mp (hnbv.symm ▸ ha)).2.1
  have hbS : b ∈ S := (mem_nb.mp (hnbv.symm ▸ hb)).2.1
  have ha'S : a' ∈ S := (mem_nb.mp (hnbv'.symm ▸ ha')).2.1
  have hb'S : b' ∈ S := (mem_nb.mp (hnbv'.symm ▸ hb')).2.1
  have hca : c s(v, a) = i := (mem_nb.mp ha).2.2
  have hcb : c s(v, b) = i := (mem_nb.mp hb).2.2
  have hca' : c s(v', a') = i := (mem_nb.mp ha').2.2
  have hcb' : c s(v', b') = i := (mem_nb.mp hb').2.2
  have hvS : v ∈ S := (mem_pathFourSets.mp hv).2.2.1
  have hv'S : v' ∈ S := (mem_pathFourSets.mp hv').2.2.1
  have hsub1 : ({s(v, a), s(v, b)} : Finset (Sym2 (Verts n))) ⊆ classIn c i S := by
    intro e he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl
    · exact mem_classIn.mpr ⟨mem_edgeFinset_mk hvS haS hva.symm, hca⟩
    · exact mem_classIn.mpr ⟨mem_edgeFinset_mk hvS hbS hvb.symm, hcb⟩
  have hsub2 : ({s(v', a'), s(v', b')} : Finset (Sym2 (Verts n))) ⊆ classIn c i S := by
    intro e he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl
    · exact mem_classIn.mpr ⟨mem_edgeFinset_mk hv'S ha'S hva'.symm, hca'⟩
    · exact mem_classIn.mpr ⟨mem_edgeFinset_mk hv'S hb'S hvb'.symm, hcb'⟩
  have hcard2 : (classIn c i S).card = 2 := (mem_pathFourSets.mp hv).2.1
  have hne1 : s(v, a) ≠ s(v, b) := fun h => hab (sym2_inj_right h)
  have hne2 : s(v', a') ≠ s(v', b') := fun h => hab' (sym2_inj_right h)
  have heq : ({s(v, a), s(v, b)} : Finset (Sym2 (Verts n)))
      = {s(v', a'), s(v', b')} := by
    have hp1 : ({s(v, a), s(v, b)} : Finset (Sym2 (Verts n))).card = 2 := card_pair_eq_two hne1
    have hp2 : ({s(v', a'), s(v', b')} : Finset (Sym2 (Verts n))).card = 2 := card_pair_eq_two hne2
    have hE1 : ({s(v, a), s(v, b)} : Finset (Sym2 (Verts n))) = classIn c i S := by
      refine Finset.eq_of_subset_of_card_le hsub1 ?_
      rw [hp1]; exact hcard2.le
    have hE2 : ({s(v', a'), s(v', b')} : Finset (Sym2 (Verts n))) = classIn c i S := by
      refine Finset.eq_of_subset_of_card_le hsub2 ?_
      rw [hp2]; exact hcard2.le
    exact hE1.trans hE2.symm
  have hmem1 : s(v, a) = s(v', a') ∨ s(v, a) = s(v', b') := by
    have hmem : s(v, a) ∈ ({s(v', a'), s(v', b')} : Finset (Sym2 (Verts n))) := by
      rw [← heq]; exact Finset.mem_insert_self _ _
    rcases Finset.mem_insert.mp hmem with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Finset.mem_singleton.mp h1)
  have hmem2 : s(v, b) = s(v', a') ∨ s(v, b) = s(v', b') := by
    have hmem : s(v, b) ∈ ({s(v', a'), s(v', b')} : Finset (Sym2 (Verts n))) := by
      rw [← heq]; simp
    rcases Finset.mem_insert.mp hmem with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Finset.mem_singleton.mp h1)
  rcases hmem1 with h1 | h1 <;> rcases hmem2 with h2 | h2
  · exact absurd (h1.trans h2.symm) hne1
  · exact common_vertex_eq hab h1 h2
  · exact common_vertex_eq hab h1 h2
  · exact absurd (h1.trans h2.symm) hne1

/-- **THE PER-COLOUR FOUR-SET CENSUS, PATH HALF: `(twoA c i).card * (n-3) ≤ |twoFourSets c i|`.**
The `n-3` four-sets spanned by each of the `(twoA c i).card` two-edge paths of colour `i` are
distinct, because a four-set with a doubled colour determines the centre of that colour's pair
(`eq_v_of_mem_pathFourSets`). -/
theorem pairwiseDisjoint_pathFourSets {n k : ℕ} {c : Col n k} (hc : Admissible c) (i : Fin k) :
    ((twoA c i : Finset (Verts n)) : Set (Verts n)).PairwiseDisjoint (fun v => pathFourSets c i v) := by
  intro v hv w hw hvw
  refine Finset.disjoint_left.mpr ?_
  intro S hS hS'
  exact hvw (eq_v_of_mem_pathFourSets hc hS hS')

theorem card_twoFourSets_ge_paths_mul {n k : ℕ} {c : Col n k} (hc : Admissible c) (i : Fin k) :
    (twoA c i).card * (n - 3) ≤ (twoFourSets c i).card := by
  have hdisj := pairwiseDisjoint_pathFourSets hc i
  have h0 : ∀ v ∈ twoA c i, n - 3 ≤ (pathFourSets c i v).card :=
    fun v hv => card_pathFourSets_ge hc i hv
  have h1 : ∑ _v ∈ (twoA c i), (n - 3)
      ≤ ∑ v ∈ (twoA c i), (pathFourSets c i v).card :=
    Finset.sum_le_sum fun v hv => h0 v hv
  have h2 : ∑ _v ∈ (twoA c i), (n - 3) = (twoA c i).card * (n - 3) :=
    sum_const_card_nat (twoA c i) (n - 3)
  have h3 : ((twoA c i).biUnion (fun v => pathFourSets c i v)).card
      = ∑ v ∈ (twoA c i), (pathFourSets c i v).card :=
    Finset.card_biUnion hdisj
  have h4 : (twoA c i).biUnion (fun v => pathFourSets c i v) ⊆ twoFourSets c i :=
    Finset.biUnion_subset.mpr fun v _ => Finset.filter_subset _ _
  have h5 := Finset.card_le_card h4
  omega

/-! ### §3  the tight four-sets are counted once -/

/-- **A FOUR-SET HAS AT MOST ONE DOUBLED COLOUR** — as the `Disjoint` statement about the finsets
`twoFourSets c i` which `Finset.disjiUnion` needs. -/
theorem pairwiseDisjoint_twoFourSets {n k : ℕ} {c : Col n k} (hc : Admissible c) :
    ((Finset.univ : Finset (Fin k)) : Set (Fin k)).PairwiseDisjoint (fun i => twoFourSets c i) := by
  intro i hi j hj hij
  refine Finset.disjoint_left.mpr ?_
  intro S hSi hSj
  have hSi' := mem_twoFourSets.mp hSi
  have hSj' := mem_twoFourSets.mp hSj
  have hle := card_doubledIn_le_one hc hSi'.1
  have hsub : ({i, j} : Finset (Fin k)) ⊆ doubledIn c S := by
    show insert i ({j} : Finset (Fin k)) ⊆ doubledIn c S
    refine Finset.insert_subset (mem_doubledIn.mpr hSi'.2) ?_
    intro e he
    rw [Finset.mem_singleton] at he
    subst he
    exact mem_doubledIn.mpr hSj'.2
  have hcard2 : ({i, j} : Finset (Fin k)).card = 2 := by
    rw [Finset.card_insert_of_notMem (by simp [hij]), Finset.card_singleton]
  have hsub2 := Finset.card_le_card hsub
  omega

/-- **`sum_twoFourSets`: THE COUNTED-ONCE IDENTITY.**  For every admissible colouring,

    `∑_i |twoFourSets c i| = |fiveFourSets c|`:

the four-element vertex sets on which some colour occurs exactly twice are counted **once each**
by the left-hand side, and they are precisely the tight four-sets.  This is the step
`Census.lean` §2* names as missing. -/
theorem sum_twoFourSets {n k : ℕ} {c : Col n k} (hc : Admissible c) :
    ∑ i : Fin k, (twoFourSets c i).card = (fiveFourSets c).card := by
  set U := (Finset.univ : Finset (Fin k)) with hU
  have hdisj := pairwiseDisjoint_twoFourSets hc
  have h1 : ∑ i : Fin k, (twoFourSets c i).card = (U.disjiUnion (fun i => twoFourSets c i) hdisj).card := by
    rw [Finset.card_disjiUnion, hU]
  have h2 : U.disjiUnion (fun i => twoFourSets c i) hdisj = fiveFourSets c := by
    ext S
    rw [Finset.mem_disjiUnion, mem_fiveFourSets]
    constructor
    · rintro ⟨i, -, hSi⟩
      have hSi' := mem_twoFourSets.mp hSi
      have h6 := card_colorsOn_add_doubledIn hc hSi'.1
      have hpos : 0 < (doubledIn c S).card := Finset.card_pos.mpr ⟨i, mem_doubledIn.mpr hSi'.2⟩
      have h5 := hc S hSi'.1
      omega
    · rintro ⟨hS, h5⟩
      have h6 := card_colorsOn_add_doubledIn hc hS
      have hD : (doubledIn c S).card = 1 := by omega
      obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hD
      have hi' : i ∈ doubledIn c S := by
        rw [hi]; simp
      exact ⟨i, Finset.mem_univ i, mem_twoFourSets.mpr ⟨hS, mem_doubledIn.mp hi'⟩⟩
  rw [h1, h2]

/-! ### §4  the trade-off theorem -/

/-- **THE MAIN THEOREM OF THIS FILE: THE TRADE-OFF BETWEEN COLOURS AND TIGHT FOUR-SETS.**

    `(n-3) * Paths c ≤ |fiveFourSets c|`

for every admissible colouring of `K_n`.  Every two-edge path lies in exactly `n-3` tight
four-sets and different paths lie in different ones, so the tighter the colour count, the more
`K₄`s are forced to span exactly five colours. -/
theorem fiveFourSets_ge_paths_mul {n k : ℕ} {c : Col n k} (hc : Admissible c) :
    (n - 3) * Paths c ≤ (fiveFourSets c).card := by
  have h1 : ∑ i : Fin k, (twoA c i).card * (n - 3) ≤ ∑ i : Fin k, (twoFourSets c i).card :=
    Finset.sum_le_sum fun i _ => card_twoFourSets_ge_paths_mul hc i
  have h2 : ∑ i : Fin k, (twoA c i).card * (n - 3) = (n - 3) * Paths c := by
    rw [Paths, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Nat.mul_comm _ _
  exact le_trans (h2 ▸ h1) (le_of_eq (sum_twoFourSets hc))

/-- At most `C(n,4)` four-sets, hence a second bound on the number of two-edge paths. -/
theorem fiveFourSets_le_fourSets {n k : ℕ} {c : Col n k} :
    (fiveFourSets c).card ≤ (fourSets n).card := by
  refine Finset.card_le_card ?_
  intro S hS
  rw [mem_fiveFourSets] at hS
  exact mem_fourSets.mpr hS.1

/-- `(n-3) * Paths c ≤ |fourSets n|`. -/
theorem quad_mul_paths_le_fourSets {n k : ℕ} {c : Col n k} (hc : Admissible c) :
    (n - 3) * Paths c ≤ (fourSets n).card :=
  le_trans (fiveFourSets_ge_paths_mul hc) fiveFourSets_le_fourSets

/-- **THE TRADE-OFF IN TERMS OF THE NUMBER OF COLOURS: `(n-3) * n * (n-1-k) ≤ |fiveFourSets c|`**
for every admissible `k`-colouring `c` of `K_n`. -/
theorem fiveFourSets_ge_of_colours {n k : ℕ} {c : Col n k} (hc : Admissible c) :
    (n - 3) * n * (n - 1 - k) ≤ (fiveFourSets c).card := by
  have h1 : n * (n - 1) ≤ n * k + Paths c := mul_n_sub_one_le hc
  have h2 := fiveFourSets_ge_paths_mul hc
  have hsub : n * (n - 1 - k) = n * (n - 1) - n * k := by
    by_cases hk : k ≤ n - 1
    · exact Nat.mul_sub ..
    · have h0 : n - 1 - k = 0 := by omega
      have hle : n * (n - 1) ≤ n * k := by
        have := Nat.mul_le_mul_right n (by omega : n - 1 ≤ k)
        simpa [Nat.mul_comm] using this
      rw [h0]; omega
  have h3 : n * (n - 1 - k) ≤ Paths c := by
    rw [hsub]
    exact Nat.le_trans (Nat.sub_le_sub_right h1 (n * k))
      (by rw [Nat.add_sub_cancel_left])
  calc (n - 3) * n * (n - 1 - k) = (n - 3) * (n * (n - 1 - k)) := by ring
    _ ≤ (n - 3) * Paths c := Nat.mul_le_mul_left (n - 3)
      (by simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h3)
    _ ≤ (fiveFourSets c).card := h2

/-- **THE SHAPE OF THE TIGHT CASE.**  If a `k`-colouring of `K_n` attains the catalog counting
bound `6 * k = 5 * (n-1)`, then

1. it carries at least `(n-3) * n * (n-1-k)` tight four-sets, and
2. `6 * (n-1-k) ≤ n-1`, i.e. `n-1-k ≤ (n-1)/6`.

Together these say that an extremal colouring has at least a fraction `4/(n-2)` of the `C(n,4)`
four-sets spanning exactly five colours. -/
theorem fiveSixthShape_tight {n k : ℕ} {c : Col n k} (hc : Admissible c)
    (hk : 6 * k = 5 * (n - 1)) :
    (n - 3) * n * (n - 1 - k) ≤ (fiveFourSets c).card ∧ 6 * (n - 1 - k) ≤ n - 1 := by
  refine ⟨fiveFourSets_ge_of_colours hc, by omega⟩

/-! ### §5  machine-checked instances -/

/-- **THE `K₆` WITNESS HAS EVERY FOUR-SET TIGHT**: all `C(6,4) = 15` four-sets of `sixCol` span
exactly five colours, and `sixCol` has no two-edge path at all (it is a 1-factorisation), so the
trade-off `fiveFourSets_ge_paths_mul` is attained with equality `0 ≤ 15`. -/
theorem fiveFourSets_sixCol : (fiveFourSets sixCol).card = 15 := by native_decide

/-- The `K₉` witness: `84` of the `C(9,4) = 126` four-sets are tight, and it carries `4` two-edge
paths, so `(9-3) * 4 = 24 ≤ 84`. -/
theorem fiveFourSets_nineCol : (fiveFourSets nineCol).card = 84 := by native_decide

/-- The `K₁₀` witness: `138` of the `C(10,4) = 210` four-sets are tight, with `8` two-edge
paths. -/
theorem fiveFourSets_tenCol : (fiveFourSets tenCol).card = 138 := by native_decide

/-- The `K₁₁` witness: `195` of the `C(11,4) = 330` four-sets are tight, with `10` two-edge
paths. -/
theorem fiveFourSets_elevenCol : (fiveFourSets elevenCol).card = 195 := by native_decide

/-- **The four instances are consistent with the census identity** `|fiveFourSets c| =
∑_i |twoFourSets c i|`: the per-colour census of `Tables.elevenCol` is `10 + 22 + 29 + 29 + 29 +
22 + 10 + 17 + 10 + 17 = 195`. -/
theorem twoFourSets_elevenCol_sum :
    ∑ i : Fin 10, (twoFourSets elevenCol i).card = 195 := by native_decide

end JSP140