import JSPProblem.Quad
import JSPProblem.Tables

/-!
# JSP-000140 — THE EXACT FOUR-SET CENSUS: pairs of same-coloured edges

`Quad.lean` closes the *counted-once* half of the four-set census (`sum_twoFourSets`,
`∑_i |twoFourSets c i| = |fiveFourSets c|`) and its *inequality* half
(`card_twoFourSets_ge_paths_mul`, `(twoA c i).card * (n-3) ≤ |twoFourSets c i|`).  What it names as
missing — and what the round-58/60 headers of `ACCEPTANCE.md` repeat as the open lemma of the
development — is the **disjoint-pair half**:

> `|twoFourSets c i| = choose |classF c i| 2 + (n - 4) * (twoA c i).card`

the exact number of tight `K₄`s spanned by one colour, in terms of the **size of the colour class**
and the **number of its two-edge paths**.  This file proves it, with the global form and its
consequences.

## The mathematics

A four-set of an admissible colouring spans at least five colours, and its six edges therefore
carry the pattern `(2,1,1,1,1)` — **exactly one** doubled colour — or `(1,1,1,1,1,1)`
(`Census.card_doubledIn_le_one`).  So the tight four-sets are counted by *pairs of same-coloured
edges*, and there are exactly two kinds of pair:

* **path pairs**: the two edges meet at a vertex, which is then a path centre (`twoA c i`); such a
  pair lies in exactly `n-3` four-sets — the three vertices of the path plus one more vertex;
* **disjoint pairs**: the two edges are vertex-disjoint; such a pair spans all four vertices, so it
  lies in **exactly one** four-set.

Every pair of colour-`i` edges is of exactly one of the two kinds (`Sym2.eq_of_ne_mem`: two
distinct edges have at most one common endpoint), and each tight four-set with doubled colour `i`
contains exactly one such pair.  Hence

    `|twoFourSets c i| = (n-3) * |twoA c i| + |disjoint i-pairs|`
                    `= (n-3) * |twoA c i| + (choose |classF c i| 2 - |twoA c i|)`
                    `= choose |classF c i| 2 + (n-4) * |twoA c i|`,

and, summing over the colours (`Paths c = ∑_i |twoA c i|`),

    **`|fiveFourSets c| = ∑_i choose |classF c i| 2 + (n-4) * Paths c`**.

**The tight-four-set census is entirely determined by the sizes of the colour classes and the number
of two-edge paths.**

## The new theorems

* `sum_nb_card_eq_two_mul_classIn_card` (§1) — the handshaking lemma for a colour class inside a
  vertex set: `∑_{v ∈ S} |nb c i v S| = 2 * |classIn c i S|`.  Two edges of one colour inside a
  **triangle** cannot be vertex-disjoint — a pigeonhole consequence of this identity.
* `card_containing` (§2) — a three-element vertex set lies in exactly `n-3` four-sets.
* `pairsOf` / `card_pairsOf` / `choose_two_mul` (§3) — the two-element subsets of a finset: `T`
  has `choose |T| 2` of them, and `2 * choose m 2 = m * (m-1)`.
* `classF`, `pairOf`, `spanFourSets` (§4) — the colour class as a finset of edges, its pairs, and
  the four-sets spanned by a pair.
* `iEdgesAt`, `meetPairs`, `disjPairs`, `card_meetPairs`, `card_disjPairs` (§5) — the pairs meeting at
  a path centre and the disjoint ones: `|meetPairs c i| = |twoA c i|`.
* `meetingFourSets` (§6) — the four-sets carrying a path;
* `twoA_card_le_choose_two`, `sum_card_meet_disj` (§7) — the pairs split into the path pairs and the
  disjoint pairs, and the two kinds add up to `choose |E_i| 2`;
* `endsF`, `card_endsF`, `span_endsF_eq` (§8) — the vertex set of an edge (two elements), and the
  fact that a pair of **disjoint** edges lies in **exactly one** four-element vertex set, the union
  of their four endpoints;
* `meeting_of_triangle` (§8) — **two edges of one colour inside a three-element vertex set meet**,
  the pigeonhole consequence of §1 that the whole census rests on;
* `classIn_eq_iEdgesAt`, `pathFourSets_of_mem_common`, `meet_or_disj` (§8) — a four-set with two
  colour-`i` edges through `v` carries *nothing else*: its whole colour-`i` class is the pair at `v`;
* `meeting_of_ne_classIn` (§9) — **THE KEY LEMMA**: two four-sets carrying the same two colour-`i`
  edges are *equal* unless those two edges meet, in which case both carry the two-edge path at the
  unique common vertex;
* `nonMeetingFourSets`, `exists_nonMeeting_of_mem_disjPairs`, `classIn_mem_disjPairs`,
  `card_nonMeetingFourSets` (§9) — **THE BIJECTION `disjPairs c i ≃ nonMeetingFourSets c i`**: a
  disjoint pair spans exactly one four-set with a doubled colour `i`, and that four-set determines
  the pair;
* `pathFourSets_eq_containing`, `card_pathFourSets_eq`, `card_meetingFourSets` (§10) — the path
  half *exactly*: each two-edge path lies in exactly `n-3` tight four-sets, so
  `|meetingFourSets c i| = |twoA c i| * (n-3)`;
* **`card_twoFourSets_census` (§11) — THE PER-COLOUR CENSUS**
  `|twoFourSets c i| = choose |E_i| 2 + (n-4) * |twoA c i|`, and **`fiveFourSets_census` /
  `census_obstruction`** — the global forms, the second being the `census_obstruction` of
  `Census.lean` §2*, open since round ~40;
* §11 the consequences: `sum_choose_two_le_fiveFourSets`, `sum_card_classF` and `sum_sq_le`, the
  **second moment** `∑_i |E_i|² ≤ 2 * C(n,4) + |E(K_n)|` — a necessary condition on the colour-class
  profile that `Surplus.surplus_identity` cannot see, since it only knows `∑_i |E_i|`, `Paths c`
  and `Isolated c`;
* §12 `native_decide` instances: the per-colour and the global census are machine-checked on **all
  four** verified constructions of `Tables.lean` (`K₆, K₉, K₁₀, K₁₁`);
* `adjEdgePairs`, `card_fiber_meetOrders`, `card_meetOrders`, **`card_adjEdgePairs_eq`** (§13) —
  the **ordered** version of the same count, the `card_adjPairs` step of `Census.lean` §2*:
  **`|adjEdgePairs c i| = 2 * |twoA c i|`**, i.e. the number of ordered pairs of distinct
  colour-`i` edges with a common endpoint is twice the number of two-edge paths, and
  `sum_card_adjEdgePairs : ∑_i |adjEdgePairs c i| = 2 * Paths c`.  The key is that **two distinct
  edges have at most one common endpoint** (`eq_common`), so forgetting the endpoint is a
  bijection; four more `native_decide` instances on `Tables.lean`.
-/

set_option maxHeartbeats 1000000

namespace JSP140

variable {n k : ℕ}

noncomputable section

/-- `Sym2.Mem` has no instance-searchable decision procedure in this Mathlib version; the finset
filters of this file only need a classical one (nothing here is evaluated). -/
local instance (n : ℕ) (e : Sym2 (Verts n)) :
    DecidablePred fun v : Verts n => Sym2.Mem v e := fun _ => Classical.propDecidable _

/-! ### §0  endpoints of an edge -/

/-- An edge with two distinct endpoints is `s(x, y)` with `x ≠ y`. -/
theorem exists_ends {n : ℕ} {e : Sym2 (Verts n)} (he : OffDiag e) :
    ∃ x y : Verts n, e = s(x, y) ∧ x ≠ y := by
  obtain ⟨x, y, h⟩ := Sym2.exists.mp (show ∃ z : Sym2 (Verts n), e = z from ⟨e, rfl⟩)
  exact ⟨x, y, h, he x y h⟩

/-- An endpoint of an edge of `edgeFinset S` lies in `S`. -/
theorem mem_of_mem_edgeFinset {n : ℕ} {S : Finset (Verts n)} {e : Sym2 (Verts n)}
    (he : e ∈ edgeFinset S) {a : Verts n} (ha : Sym2.Mem a e) : a ∈ S :=
  Finset.mem_sym2_iff.mp (mem_edgeFinset.mp he).1 a ha

/-- The edge of `edgeFinset S` on two distinct elements of `S`. -/
theorem mem_edgeFinset_of_mem {n : ℕ} {S : Finset (Verts n)} {x y : Verts n} (hx : x ∈ S)
    (hy : y ∈ S) (hne : x ≠ y) : s(x, y) ∈ edgeFinset S := mem_edgeFinset_mk hx hy hne

/-- **THE VERTICES OF AN EDGE.**  From `e = s(x, y)`, a vertex of `e` is `x` or `y`. -/
theorem mem_iff_eq {n : ℕ} {e : Sym2 (Verts n)} {x y a : Verts n} (h : e = s(x, y)) :
    Sym2.Mem a e ↔ a = x ∨ a = y := by
  rw [h]
  exact Sym2.mem_iff' 

/-- **An edge of `edgeFinset S` has exactly two endpoints in `S`.** -/
theorem card_filter_mem_edgeFinset {n : ℕ} {S : Finset (Verts n)} {e : Sym2 (Verts n)}
    (he : e ∈ edgeFinset S) :
    (S.filter (fun v => Sym2.Mem v e)).card = 2 := by
  classical
  obtain ⟨x, y, hxy, hne'⟩ := exists_ends (mem_edgeFinset.mp he).2
  have heq : S.filter (fun v => Sym2.Mem v e) = S ∩ ({x, y} : Finset (Verts n)) := by
    ext v
    constructor
    · intro h
      refine Finset.mem_inter.mpr ⟨(Finset.mem_filter.mp h).1, ?_⟩
      rcases (mem_iff_eq hxy).mp (Finset.mem_filter.mp h).2 with hv | hv
      · rw [hv]
        exact Finset.mem_insert_self x {y}
      · rw [hv]
        exact Finset.mem_insert_of_mem (Finset.mem_singleton.mpr rfl)
    · intro h
      refine Finset.mem_filter.mpr ⟨(Finset.mem_inter.mp h).1, ?_⟩
      rcases Finset.mem_insert.mp (Finset.mem_inter.mp h).2 with hv | hv
      · rw [mem_iff_eq hxy]
        exact Or.inl hv
      · rw [Finset.mem_singleton] at hv
        rw [mem_iff_eq hxy]
        exact Or.inr hv
  have hle : (S ∩ ({x, y} : Finset (Verts n))).card ≤ 2 := le_trans
      (Finset.card_le_card (fun v hv => (Finset.mem_inter.mp hv).2)) (card_pair_le_two x y)
  have hge : 2 ≤ (S ∩ ({x, y} : Finset (Verts n))).card := by
    have hsub : ({x, y} : Finset (Verts n)) ⊆ S ∩ ({x, y} : Finset (Verts n)) := by
      intro v hv
      refine Finset.mem_inter.mpr ⟨?_, hv⟩
      rcases Finset.mem_insert.mp hv with hv | hv
      · rw [hv]
        exact mem_of_mem_edgeFinset he ((mem_iff_eq hxy).2 (Or.inl rfl))
      · rw [Finset.mem_singleton] at hv
        exact mem_of_mem_edgeFinset he ((mem_iff_eq hxy).2 (Or.inr hv))
    exact le_trans (card_pair_eq_two hne').ge (Finset.card_le_card hsub)
  rw [heq]
  exact le_antisymm hle hge

/-- **`m * (m - 1) + m = m * m`**, for every `m`. -/
theorem mul_sub_add (m : ℕ) : m * (m - 1) + m = m * m := by
  induction m with
  | zero => rfl
  | succ k =>
    show Nat.succ k * (Nat.succ k - 1) + Nat.succ k = Nat.succ k * Nat.succ k
    simp only [Nat.succ_sub_one, Nat.succ_mul, Nat.succ_eq_add_one]
    rw [Nat.mul_add, Nat.mul_one]

/-- **`2 * choose m 2 = m * (m - 1)`**: the division-free form of the pair count. -/
theorem choose_two_mul (m : ℕ) : 2 * Nat.choose m 2 = m * (m - 1) := by
  induction m with
  | zero => decide
  | succ m ih =>
    have h1 : Nat.choose (m + 1) 2 = m + Nat.choose m 2 := by
      rw [Nat.choose_succ_succ m 1, Nat.choose_one_right]
    rw [h1, Nat.succ_sub_one]
    calc 2 * (m + Nat.choose m 2) = 2 * m + 2 * Nat.choose m 2 := by ring
      _ = 2 * m + m * (m - 1) := by rw [ih]
      _ = (m * (m - 1) + m) + m := by omega
      _ = m * m + m := by rw [mul_sub_add]
      _ = (m + 1) * m := (Nat.succ_mul m m).symm

/-! ### §1  the handshaking lemma for a colour class -/

/-- **THE DEGREE SUM OF A COLOUR CLASS.**  Inside a vertex set `S`, the colour-`i` edges of `S` are
counted once at each of their two endpoints:

    `∑_{v ∈ S} |nb c i v S| = 2 * |classIn c i S|`.

This is the counting input of §7: inside a **triangle**, two edges of one colour cannot be
vertex-disjoint, and this identity makes that a pigeonhole argument. -/
theorem sum_nb_card_eq_two_mul_classIn_card {n k : ℕ} {c : Col n k} (i : Fin k)
    (S : Finset (Verts n)) : ∑ v ∈ S, (nb c i v S).card = 2 * (classIn c i S).card := by
  classical
  have himage : ∀ v ∈ S, (nb c i v S).image (fun a => s(v, a))
      = (classIn c i S).filter (fun e => Sym2.Mem v e) := by
    intro v hvS
    ext e
    constructor
    · intro he
      obtain ⟨a, ha, hEq⟩ := Finset.mem_image.mp he
      subst hEq
      exact Finset.mem_filter.mpr
        ⟨mem_classIn.mpr ⟨mem_edgeFinset_mk hvS (mem_nb.mp ha).2.1
          (Ne.symm (mem_nb.mp ha).1), (mem_nb.mp ha).2.2⟩, Sym2.mem_mk_left v a⟩
    · intro he
      obtain ⟨hee, hce⟩ := mem_classIn.mp (Finset.mem_filter.mp he).1
      obtain ⟨a, ha⟩ := Finset.mem_filter.mp he |>.2
      have hne : v ≠ a := (mem_edgeFinset.mp hee).2 v a ha
      have haS : a ∈ S := mem_of_mem_edgeFinset hee ((mem_iff_eq ha).2 (Or.inr rfl))
      exact Finset.mem_image.mpr ⟨a, mem_nb.mpr ⟨Ne.symm hne, haS, ha ▸ hce⟩, ha.symm⟩
  have key : ∀ v ∈ S, (nb c i v S).card
      = ((classIn c i S).filter (fun e => Sym2.Mem v e)).card := by
    intro v hv
    have h := Finset.card_image_of_injective (s := nb c i v S) (f := fun a => s(v, a))
      (by intro a b hab; exact sym2_inj_right hab)
    calc (nb c i v S).card = ((nb c i v S).image (fun a => s(v, a))).card := h.symm
      _ = ((classIn c i S).filter (fun e => Sym2.Mem v e)).card := by rw [himage v hv]
  calc ∑ v ∈ S, (nb c i v S).card
      = ∑ v ∈ S, ((classIn c i S).filter (fun e => Sym2.Mem v e)).card := by
        refine Finset.sum_congr rfl fun v hv => key v hv
    _ = ∑ v ∈ S, ∑ e ∈ classIn c i S, (if Sym2.Mem v e then 1 else 0) := by
        refine Finset.sum_congr rfl fun v _ => Finset.card_filter _ _
    _ = ∑ e ∈ classIn c i S, ∑ v ∈ S, (if Sym2.Mem v e then 1 else 0) := Finset.sum_comm
    _ = ∑ e ∈ classIn c i S, 2 := by
        refine Finset.sum_congr rfl fun e he => ?_
        have hff : (S.filter (fun v => Sym2.Mem v e)).card = 2 :=
          card_filter_mem_edgeFinset (mem_classIn.mp he).1
        rw [← Finset.card_filter (fun v => Sym2.Mem v e) S]
        exact hff
    _ = 2 * (classIn c i S).card := by
        have h : ∑ _e ∈ classIn c i S, 2 = (classIn c i S).card * 2 := by
          induction classIn c i S using Finset.induction_on with
          | empty => simp
          | @insert e s _ ih => simp
        rw [h]
        exact Nat.mul_comm _ _


/-! ### §2  the four-sets around a vertex set -/

/-- **THE FOUR-SETS CONTAINING `T`.** -/
def containing {n : ℕ} (T : Finset (Verts n)) : Finset (Finset (Verts n)) :=
  (fourSets n).filter fun S => T ⊆ S

theorem mem_containing {n : ℕ} {T S : Finset (Verts n)} :
    S ∈ containing T ↔ S.card = 4 ∧ T ⊆ S := by
  rw [containing, Finset.mem_filter, mem_fourSets]

theorem containing_subset_fourSets {n : ℕ} (T : Finset (Verts n)) : containing T ⊆ fourSets n :=
  Finset.filter_subset _ _

/-- **A THREE-ELEMENT VERTEX SET LIES IN EXACTLY `n-3` FOUR-SETS** (`n ≥ 4`): the fourth vertex is
free, and it must lie outside the three. -/
theorem card_containing {n : ℕ} (T : Finset (Verts n)) (hT : T.card = 3) (hn : 4 ≤ n) :
    (containing T).card = n - 3 := by
  have hmaps : ∀ x ∈ Finset.univ \ T, insert x T ∈ containing T := by
    intro x hx
    refine mem_containing.mpr ⟨?_, fun y hy => Finset.mem_insert_of_mem hy⟩
    rw [Finset.card_insert_of_notMem (Finset.mem_sdiff.mp hx).2, hT]
  have hsurj : ∀ S ∈ containing T, ∃ x ∈ Finset.univ \ T, insert x T = S := by
    intro S hS
    obtain ⟨hS4, hTS⟩ := mem_containing.mp hS
    have hcard1 : (S \ T).card = 1 := by
      have h := Finset.card_sdiff_add_card_eq_card hTS
      rw [hS4, hT] at h
      omega
    obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hcard1
    have hmemx : x ∈ S \ T := by
      rw [hx]
      exact Finset.mem_singleton.mpr rfl
    refine ⟨x, Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, Finset.mem_sdiff.mp hmemx |>.2⟩, ?_⟩
    ext y
    constructor
    · intro hy
      rcases Finset.mem_insert.mp hy with hy | hy
      · exact Finset.mem_sdiff.mp (hy ▸ hmemx) |>.1
      · exact hTS hy
    · intro hyS
      by_cases hyT : y ∈ T
      · exact Finset.mem_insert.mpr (Or.inr hyT)
      · exact Finset.mem_insert.mpr (Or.inl (Finset.mem_singleton.mp (by
          rw [← hx]
          exact Finset.mem_sdiff.mpr ⟨hyS, hyT⟩)))
  have hcardEq : (containing T).card = (Finset.univ \ T).card :=
    (Finset.card_bij (s := Finset.univ \ T) (t := containing T) (fun x _ => insert x T)
      (fun x hx => hmaps x hx)
      (by
        intro x hx y hy hxy
        have hxm : x ∈ insert x T := Finset.mem_insert_self x T
        rw [hxy] at hxm
        rcases Finset.mem_insert.mp hxm with heq | heq
        · exact heq
        · exact absurd heq (Finset.mem_sdiff.mp hx |>.2))
      (by
        intro S hS
        obtain ⟨x, hx, rfl⟩ := hsurj S hS
        exact ⟨x, hx, rfl⟩)).symm
  rw [hcardEq, Finset.card_sdiff_of_subset (Finset.subset_univ T), Finset.card_univ,
    Fintype.card_fin]
  omega

/-! ### §3  the two-element subsets of a finset -/

/-- **THE TWO-ELEMENT SUBSETS OF A FINSET**, i.e. its unordered pairs of distinct elements. -/
def pairsOf {α : Type*} [DecidableEq α] (T : Finset α) : Finset (Finset α) :=
T.powerset.filter fun p => p.card = 2

theorem mem_pairsOf {α : Type*} [DecidableEq α] {T : Finset α} {p : Finset α} :
  p ∈ pairsOf T ↔ p ⊆ T ∧ p.card = 2 := by
  rw [pairsOf, Finset.mem_filter, Finset.mem_powerset]

theorem pairsOf_subset_powerset {α : Type*} [DecidableEq α] (T : Finset α) :
  pairsOf T ⊆ T.powerset := Finset.filter_subset _ _

/-- **THE CARDINALITY OF THE PAIR SET**: a finset with `t` elements has `choose t 2` unordered pairs
of distinct elements. -/
theorem card_pairsOf {α : Type*} [DecidableEq α] (T : Finset α) :
  (pairsOf T).card = Nat.choose T.card 2 := by
  classical
have hswap (x e : α) : ({x, e} : Finset α) = {e, x} := by
  ext y
  simp only [Finset.mem_insert, Finset.mem_singleton, or_comm]
induction T using Finset.induction_on with
| empty =>
    have hnil : pairsOf (∅ : Finset α) = ∅ := by
      ext p
      constructor
      · intro hp
        have hsub : p ⊆ (∅ : Finset α) := (mem_pairsOf.mp hp).1
        have h2 := (mem_pairsOf.mp hp).2
        have hmem : ∀ y, y ∈ p → False := by
          intro y hym
          have hym' : y ∈ (∅ : Finset α) := hsub hym
          simp at hym'
        rw [Finset.card_eq_zero.mpr (Finset.eq_empty_iff_forall_notMem.mpr hmem)] at h2
        omega
      · intro hp
        simp at hp
    rw [hnil]
    show 0 = Nat.choose 0 2
    decide
| @insert e T hneT ih =>
    have hdecomp : pairsOf (insert e T)
        = pairsOf T ∪ (T.image (fun x => insert x ({e} : Finset α))) := by
      ext p
      constructor
      · intro hp
        obtain ⟨hpT, hcard⟩ := mem_pairsOf.mp hp
        by_cases he : e ∈ p
        · refine Finset.mem_union_right _ ?_
          obtain ⟨x, hx⟩ := Finset.card_eq_one.mp (by
            have h := Finset.card_erase_of_mem he
            rw [hcard] at h
            omega)
          have hxe : x ∈ Finset.erase p e := by
            rw [hx]
            exact Finset.mem_singleton.mpr rfl
          have hxp : x ∈ p := (Finset.mem_erase.mp hxe).2
          have hne : e ≠ x := by
            intro hex
            exact (Finset.mem_erase.mp hxe).1 hex.symm
          have hxT : x ∈ T := by
            rcases Finset.mem_insert.mp (hpT hxp) with h1 | h1
            · exact (hne h1.symm).elim
            · exact h1
          have hpx : p ⊆ insert e {x} := by
            intro y hy
            by_cases hyE : y = e
            · rw [hyE]
              exact Finset.mem_insert_self e {x}
            · have hyxe : y ∈ Finset.erase p e := Finset.mem_erase.mpr ⟨hyE, hy⟩
              rw [hx] at hyxe
              have hyx : y = x := Finset.mem_singleton.mp hyxe
              rw [hyx]
              exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr rfl))
          have hpe : p = insert e {x} := by
            refine Finset.Subset.antisymm hpx (fun y hy => ?_)
            rcases Finset.mem_insert.mp hy with hy | hy
            · cases hy
              exact he
            · rw [Finset.mem_singleton] at hy
              exact hy ▸ hxp
          exact Finset.mem_image.mpr ⟨x, hxT, by rw [hpe, hswap x e]⟩
        · refine Finset.mem_union_left _ (mem_pairsOf.mpr ⟨?_, hcard⟩)
          intro y hy
          rcases Finset.mem_insert.mp (hpT hy) with h1 | h1
          · exact (he (h1 ▸ hy)).elim
          · exact h1
      · intro hp
        rcases Finset.mem_union.mp hp with hp | hp
        · exact mem_pairsOf.mpr
            ⟨fun y hy => Finset.mem_insert.mpr (Or.inr ((mem_pairsOf.mp hp).1 hy)),
              (mem_pairsOf.mp hp).2⟩
        · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hp
          refine mem_pairsOf.mpr ⟨?_, ?_⟩
          · intro y hy
            rcases Finset.mem_insert.mp hy with hy | hy
            · exact Finset.mem_insert.mpr (Or.inr (hy ▸ hx))
            · rw [Finset.mem_singleton] at hy
              exact Finset.mem_insert.mpr (Or.inl hy)
          · have hne : x ≠ e := fun hxe => hneT (hxe ▸ hx)
            rw [hswap x e, Finset.card_insert_of_notMem (by
              rw [Finset.mem_singleton]
              exact Ne.symm hne), Finset.card_singleton]
    have hdisj : Disjoint (pairsOf T) (T.image (fun x => insert x ({e} : Finset α))) := by
      refine Finset.disjoint_left.mpr fun p hp1 hp2 => ?_
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hp2
      obtain ⟨hpT, hcard⟩ := mem_pairsOf.mp hp1
      exact absurd (hpT (by rw [hswap x e]; exact Finset.mem_insert_self e {x})) hneT
    have hinj : Function.Injective (fun x : α => insert x ({e} : Finset α)) := by
      intro x y hxy
      have heq : insert x ({e} : Finset α) = insert y ({e} : Finset α) := hxy
      have hmem : x ∈ insert y ({e} : Finset α) := by
        rw [← heq]
        exact Finset.mem_insert_self x _
      rcases Finset.mem_insert.mp hmem with h1 | h1
      · exact h1
      · rw [Finset.mem_singleton] at h1
        by_contra hye
        have heq' : (insert x ({e} : Finset α)).card = 1 := by
          rw [h1]
          simp
        have hcard : (insert y ({e} : Finset α)).card = 1 := by
          rw [← heq]
          exact heq'
        have hyne : y ∉ ({e} : Finset α) := by
          rw [Finset.mem_singleton]
          exact fun hye' => hye ((hye'.trans h1.symm).symm)
        rw [Finset.card_insert_of_notMem hyne, Finset.card_singleton] at hcard
        omega
    rw [hdecomp, Finset.card_union_of_disjoint hdisj,
      Finset.card_image_of_injective _ hinj]
    have hcardT : (insert e T).card = T.card + 1 := Finset.card_insert_of_notMem hneT
    have hchoose : Nat.choose (T.card + 1) 2 = Nat.choose T.card 2 + T.card := by
      have h := Nat.choose_succ_succ T.card 1
      simp only [Nat.choose_one_right, Nat.succ_eq_add_one] at h
      simpa [Nat.add_comm] using h
    rw [hcardT, hchoose]
    omega

/-! ### §4  the colour class, its pairs, and the four-sets they span -/

/-- **THE COLOUR CLASS OF `i` AS A FINSET OF EDGES**: the colour-`i` edges of `K_n`. -/
def classF {n k : ℕ} (c : Col n k) (i : Fin k) : Finset (Sym2 (Verts n)) :=
classIn c i (Finset.univ : Finset (Verts n))

theorem classF_subset_edgeFinset {n k : ℕ} {c : Col n k} (i : Fin k) :
  classF c i ⊆ edgeFinset (Finset.univ : Finset (Verts n)) := fun _ he => classIn_subset he

theorem mem_classF {n k : ℕ} {c : Col n k} {i : Fin k} {e : Sym2 (Verts n)}
  (he : e ∈ classF c i) : c e = i := (mem_classIn.mp he).2

theorem mem_classF_of_edge {n k : ℕ} {c : Col n k} (i : Fin k) {S : Finset (Verts n)}
  {e : Sym2 (Verts n)} (he : e ∈ edgeFinset S)
  (_hS : S ⊆ (Finset.univ : Finset (Verts n))) (hce : c e = i) : e ∈ classF c i := by
  rw [mem_edgeFinset] at he
  have hmem : e ∈ edgeFinset (Finset.univ : Finset (Verts n)) := by
    rw [mem_edgeFinset]
    refine ⟨?_, ?_⟩
    · obtain ⟨x, y, hxy⟩ := Sym2.exists.mp (show ∃ z : Sym2 (Verts n), e = z from ⟨e, rfl⟩)
      rw [hxy]
      exact Finset.mk_mem_sym2_iff.mpr ⟨Finset.mem_univ x, Finset.mem_univ y⟩
    · intro he' b hb
      exact fun h => (he.2 he' b hb) h
  exact mem_classIn.mpr ⟨hmem, hce⟩
  
/-- **THE PAIRS OF COLOUR-`i` EDGES.** -/
def pairOf {n k : ℕ} (c : Col n k) (i : Fin k) : Finset (Finset (Sym2 (Verts n))) :=
  pairsOf (classF c i)

theorem mem_pairOf {n k : ℕ} {c : Col n k} {i : Fin k} {p : Finset (Sym2 (Verts n))} :
  p ∈ pairOf c i ↔ p ⊆ classF c i ∧ p.card = 2 := by
  rw [pairOf, mem_pairsOf]

theorem card_pairOf {n k : ℕ} {c : Col n k} (i : Fin k) :
  (pairOf c i).card = Nat.choose (classF c i).card 2 := by
  rw [pairOf]; exact card_pairsOf _

/-- **THE FOUR-SETS SPANNED BY A SET OF EDGES.** -/
def spanFourSets {n : ℕ} (p : Finset (Sym2 (Verts n))) : Finset (Finset (Verts n)) :=
(fourSets n).filter fun S => p ⊆ edgeFinset S

theorem mem_spanFourSets {n : ℕ} {p : Finset (Sym2 (Verts n))} {S : Finset (Verts n)} :
  S ∈ spanFourSets p ↔ S.card = 4 ∧ p ⊆ edgeFinset S := by
  rw [spanFourSets, Finset.mem_filter, mem_fourSets]

theorem spanFourSets_subset_fourSets {n : ℕ} (p : Finset (Sym2 (Verts n))) :
  spanFourSets p ⊆ fourSets n := Finset.filter_subset _ _

/-- **A TWO-ELEMENT SET OF VERTICES DETERMINES ITS EDGE.** -/
theorem edge_eq_of_pair_eq {α : Type*} [DecidableEq α] {x y u w : α} (hxy : x ≠ y)
    (h : ({x, y} : Finset α) = {u, w}) : s(x, y) = s(u, w) := by
  have hmem : ∀ z, z = x ∨ z = y → z = u ∨ z = w := by
    intro z hz
    rcases hz with hzx | hzy
    · have hmem' : x ∈ ({u, w} : Finset α) := by
        rw [← h]
        exact Finset.mem_insert_self x {y}
      rcases Finset.mem_insert.mp hmem' with h1 | h1
      · exact Or.inl (hzx.trans h1)
      · rw [Finset.mem_singleton] at h1
        exact Or.inr (hzx.trans h1)
    · have hmem' : y ∈ ({u, w} : Finset α) := by
        rw [← h]
        exact Finset.mem_insert_of_mem (Finset.mem_singleton.mpr rfl)
      rcases Finset.mem_insert.mp hmem' with h1 | h1
      · exact Or.inl (hzy.trans h1)
      · rw [Finset.mem_singleton] at h1
        exact Or.inr (hzy.trans h1)
  rcases hmem x (Or.inl rfl) with h1 | h1 <;> rcases hmem y (Or.inr rfl) with h2 | h2
  · exact (hxy (h1.trans h2.symm)).elim
  · exact Sym2.eq_iff.mpr (Or.inl ⟨h1, h2⟩)
  · exact Sym2.eq_iff.mpr (Or.inr ⟨h1, h2⟩)
  · exact (hxy (h1.trans h2.symm)).elim

/-- **TWO DISTINCT EDGES OF `K_n` LIE IN A COMMON FOUR-SET** (`n ≥ 4`): the two edges span three or
four vertices.  Here the two edges come with their `OffDiag` witnesses, as they do inside
`edgeFinset`. -/
theorem exists_fourSet_of_pair {n : ℕ} {p : Finset (Sym2 (Verts n))} (hp : p.card = 2)
    (hd : ∀ e ∈ p, OffDiag e) (hn : 4 ≤ n) :
    ∃ S : Finset (Verts n), S.card = 4 ∧ p ⊆ edgeFinset S := by
  obtain ⟨e, f, hef, hset⟩ := Finset.card_eq_two.mp hp
  have hde : e ∈ p := by rw [hset]; exact Finset.mem_insert_self e {f}
  have hdf : f ∈ p := by
    rw [hset]
    exact Finset.mem_insert_of_mem (Finset.mem_singleton.mpr rfl)
  obtain ⟨x, y, hxy, hx⟩ := exists_ends (hd e hde)
  obtain ⟨u, w, huw, huwne⟩ := exists_ends (hd f hdf)
  have hT : ({x, y} : Finset (Verts n)).card = 2 := card_pair_eq_two hx
  have hU : ({u, w} : Finset (Verts n)).card = 2 := card_pair_eq_two huwne
  have hneT : ({x, y} : Finset (Verts n)) ≠ {u, w} := by
    intro h
    exact hef ((hxy.trans (edge_eq_of_pair_eq hx h)).trans huw.symm)
  have hle : ({x, y} ∩ {u, w} : Finset (Verts n)).card ≤ 2 := by
    have hsub : ({x, y} ∩ {u, w} : Finset (Verts n)) ⊆ {u, w} :=
      fun v hv => (Finset.mem_inter.mp hv).2
    exact le_trans (Finset.card_le_card hsub) hU.le
  have hne2 : ({x, y} ∩ {u, w} : Finset (Verts n)).card ≠ 2 := by
    intro h2
    obtain ⟨a, b, hab, hset⟩ := Finset.card_eq_two.mp h2
    have hsub : ({a, b} : Finset (Verts n)) ⊆ {u, w} := by
      rw [← hset]
      exact fun v hv => (Finset.mem_inter.mp hv).2
    have heq : ({a, b} : Finset (Verts n)) = {u, w} :=
      Finset.eq_of_subset_of_card_le hsub (by rw [card_pair_eq_two hab, hU])
    have hix : ({x, y} ∩ {u, w} : Finset (Verts n)) = {x, y} :=
      Finset.eq_of_subset_of_card_le (fun v hv => (Finset.mem_inter.mp hv).1) (by rw [h2, hT])
    exact hneT (hix.symm.trans (hset.trans heq))
  have hcard3 : 3 ≤ ({x, y} ∪ {u, w} : Finset (Verts n)).card := by
    rw [Finset.card_union, hT, hU]
    omega
  have hcard4 : ({x, y} ∪ {u, w} : Finset (Verts n)).card ≤ 4 := by
    rw [Finset.card_union, hT, hU]
    omega
  set T := ({x, y} ∪ {u, w} : Finset (Verts n)) with hTdef
  have hxT : x ∈ T ∧ y ∈ T := by
    rw [hTdef]
    exact ⟨Finset.mem_union_left _ (Finset.mem_insert_self x {y}),
      Finset.mem_union_left _ (Finset.mem_insert_of_mem (Finset.mem_singleton.mpr rfl))⟩
  have huT : u ∈ T ∧ w ∈ T := by
    rw [hTdef]
    exact ⟨Finset.mem_union_right _ (Finset.mem_insert_self u {w}),
      Finset.mem_union_right _ (Finset.mem_insert_of_mem (Finset.mem_singleton.mpr rfl))⟩
  by_cases h4 : T.card = 4
  · refine ⟨T, h4, ?_⟩
    intro g hg
    rw [hset] at hg
    rcases Finset.mem_insert.mp hg with h1 | h1
    · rw [h1, hxy]
      exact mem_edgeFinset_of_mem hxT.1 hxT.2 hx
    · rw [Finset.mem_singleton] at h1
      rw [h1, huw]
      exact mem_edgeFinset_of_mem huT.1 huT.2 huwne
  · have hTne : T ≠ (Finset.univ : Finset (Verts n)) := by
      intro hcon
      have hc := congrArg Finset.card hcon
      rw [Finset.card_univ, Fintype.card_fin] at hc
      omega
    have hns : ¬((Finset.univ : Finset (Verts n)) ⊆ T) :=
      fun hsubT => hTne (Finset.Subset.antisymm (Finset.subset_univ T) hsubT)
    obtain ⟨z, hz⟩ := Finset.sdiff_nonempty.mpr hns
    refine ⟨insert z T, ?_, ?_⟩
    · rw [Finset.card_insert_of_notMem (Finset.mem_sdiff.mp hz).2]
      omega
    · intro g hg
      rw [hset] at hg
      rcases Finset.mem_insert.mp hg with h1 | h1
      · rw [h1, hxy]
        exact mem_edgeFinset_of_mem (Finset.mem_insert_of_mem hxT.1)
          (Finset.mem_insert_of_mem hxT.2) hx
      · rw [Finset.mem_singleton] at h1
        rw [h1, huw]
        exact mem_edgeFinset_of_mem (Finset.mem_insert_of_mem huT.1)
          (Finset.mem_insert_of_mem huT.2) huwne

/-! ### §5  the pairs meeting at a path centre, and the disjoint pairs -/

/-- **THE COLOUR-`i` EDGES INCIDENT WITH `v`**. -/
def iEdgesAt {n k : ℕ} (c : Col n k) (i : Fin k) (v : Verts n) : Finset (Sym2 (Verts n)) :=
(nb c i v (Finset.univ : Finset (Verts n))).image fun a => s(v, a)

theorem card_iEdgesAt {n k : ℕ} {c : Col n k} (i : Fin k) (v : Verts n) :
  (iEdgesAt c i v).card = (nb c i v (Finset.univ : Finset (Verts n))).card :=
Finset.card_image_of_injective _ (by intro a b hab; exact sym2_inj_right hab)

theorem mem_iEdgesAt {n k : ℕ} {c : Col n k} (i : Fin k) {v : Verts n}
  {e : Sym2 (Verts n)} :
  e ∈ iEdgesAt c i v ↔ ∃ a, a ∈ nb c i v (Finset.univ : Finset (Verts n)) ∧ e = s(v, a) := by
  rw [iEdgesAt, Finset.mem_image]
  constructor
  · rintro ⟨a, ha, hEq⟩
    exact ⟨a, ha, hEq.symm⟩
  · rintro ⟨a, ha, hEq⟩
    exact ⟨a, ha, hEq.symm⟩

theorem iEdgesAt_subset_classF {n k : ℕ} {c : Col n k} (i : Fin k) (v : Verts n) :
  iEdgesAt c i v ⊆ classF c i := by
  intro e he
  obtain ⟨a, ha, heq⟩ := Finset.mem_image.mp he
  rw [← heq]
  exact mem_classF_of_edge i
    (mem_edgeFinset_of_mem (Finset.mem_univ v) (Finset.mem_univ a) (Ne.symm (mem_nb.mp ha).1))
    (Finset.subset_univ _) (mem_nb.mp ha).2.2

theorem card_iEdgesAt_le_two {n k : ℕ} {c : Col n k} (hc : Admissible c) (i : Fin k)
  (v : Verts n) : (iEdgesAt c i v).card ≤ 2 := by
  rw [card_iEdgesAt]; exact nb_univ_card_le_two hc i v

theorem card_iEdgesAt_eq {n k : ℕ} {c : Col n k} (_hc : Admissible c) (i : Fin k)
  {v : Verts n} (hv : v ∈ twoA c i) : (iEdgesAt c i v).card = 2 := by
  rw [card_iEdgesAt]; exact mem_twoA.mp hv

theorem mem_iEdgesAt_of_mem {n k : ℕ} {c : Col n k} (i : Fin k) {v : Verts n}
  {e : Sym2 (Verts n)} (he : e ∈ iEdgesAt c i v) : Sym2.Mem v e := by
  obtain ⟨a, ha, heq⟩ := Finset.mem_image.mp he
  rw [← heq]
  exact Sym2.mem_mk_left v _

/-- **THE PAIRS OF COLOUR-`i` EDGES THAT MEET AT A PATH CENTRE.** -/
def meetPairs {n k : ℕ} (c : Col n k) (i : Fin k) : Finset (Finset (Sym2 (Verts n))) :=
(twoA c i).image (iEdgesAt c i)

theorem mem_meetPairs {n k : ℕ} {c : Col n k} {i : Fin k} {p : Finset (Sym2 (Verts n))} :
  p ∈ meetPairs c i ↔ ∃ v ∈ twoA c i, p = iEdgesAt c i v := by
  rw [meetPairs, Finset.mem_image]
  constructor
  · rintro ⟨v, hv, hEq⟩
    exact ⟨v, hv, hEq.symm⟩
  · rintro ⟨v, hv, hEq⟩
    exact ⟨v, hv, hEq.symm⟩

/-- **THE DISJOINT PAIRS OF COLOUR-`i` EDGES** — the pairs of colour-`i` edges which are not the
two edges of a two-edge path. -/
def disjPairs {n k : ℕ} (c : Col n k) (i : Fin k) : Finset (Finset (Sym2 (Verts n))) :=
pairOf c i \ meetPairs c i

theorem disjPairs_subset_pairOf {n k : ℕ} {c : Col n k} (i : Fin k) :
  disjPairs c i ⊆ pairOf c i := Finset.sdiff_subset

theorem mem_disjPairs {n k : ℕ} {c : Col n k} {i : Fin k} {p : Finset (Sym2 (Verts n))} :
  p ∈ disjPairs c i ↔ p ∈ pairOf c i ∧ p ∉ meetPairs c i := by
  rw [disjPairs, Finset.mem_sdiff]

/-- **THE CARDINALITY OF THE TWO KINDS OF PAIRS**: a two-element subset of a colour class is
either the pair of edges of a two-edge path, or a disjoint pair — and there are `choose |E_i| 2`
pairs in all. -/
theorem meetPairs_subset_pairOf {n k : ℕ} {c : Col n k} (hc : Admissible c) (i : Fin k) :
  meetPairs c i ⊆ pairOf c i := by
  intro p hp
  obtain ⟨v, hv, hp⟩ := mem_meetPairs.mp hp
  rw [hp]
  exact mem_pairOf.mpr ⟨iEdgesAt_subset_classF i v, card_iEdgesAt_eq hc i hv⟩

theorem card_meetPairs {n k : ℕ} {c : Col n k} (hc : Admissible c) (i : Fin k) :
    (meetPairs c i).card = (twoA c i).card := by
  have keyinj : ∀ v w : Verts n, v ∈ twoA c i → w ∈ twoA c i →
      iEdgesAt c i v = iEdgesAt c i w → v = w := by
    intro v w hv hw hvw
    by_contra hne
    obtain ⟨a, b, hab, hset⟩ := Finset.card_eq_two.mp (card_iEdgesAt_eq hc i hv)
    have haV : a ∈ iEdgesAt c i v := by
      rw [hset]; exact Finset.mem_insert_self a {b}
    have hbV : b ∈ iEdgesAt c i v := by
      rw [hset]; exact Finset.mem_insert_of_mem (Finset.mem_singleton.mpr rfl)
    have haW : a ∈ iEdgesAt c i w := by rw [← hvw]; exact haV
    have hbW : b ∈ iEdgesAt c i w := by rw [← hvw]; exact hbV
    exact hab (Sym2.eq_of_ne_mem hne (mem_iEdgesAt_of_mem i haV) (mem_iEdgesAt_of_mem i haW)
      (mem_iEdgesAt_of_mem i hbV) (mem_iEdgesAt_of_mem i hbW))
  rw [meetPairs]
  exact (Finset.card_bij (fun v _ => iEdgesAt c i v)
    (fun v hv => Finset.mem_image.mpr ⟨v, hv, rfl⟩)
    (fun v hv w hw hvw => keyinj v w hv hw hvw)
    (fun p hp => by
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hp
      exact ⟨v, hv, rfl⟩)).symm

theorem card_disjPairs {n k : ℕ} {c : Col n k} (hc : Admissible c) (i : Fin k) :
  (disjPairs c i).card = (classF c i).card.choose 2 - (twoA c i).card := by
  rw [disjPairs, Finset.card_sdiff_of_subset (meetPairs_subset_pairOf hc i), card_pairOf,
  card_meetPairs hc i]

/-! ### §6  the four-sets carrying a two-edge path -/

/-- **THE FOUR-SETS SPANNED BY A TWO-EDGE PATH OF COLOUR `i`.** -/
def meetingFourSets {n k : ℕ} (c : Col n k) (i : Fin k) : Finset (Finset (Verts n)) :=
(twoA c i).biUnion fun v => pathFourSets c i v

theorem mem_meetingFourSets {n k : ℕ} {c : Col n k} (i : Fin k) {S : Finset (Verts n)} :
  S ∈ meetingFourSets c i ↔ ∃ v ∈ twoA c i, S ∈ pathFourSets c i v := by
  constructor
  · intro h
    rw [meetingFourSets] at h
    exact Finset.mem_biUnion.mp h
  · rintro ⟨v, hv, h⟩
    rw [meetingFourSets, Finset.mem_biUnion]
    exact ⟨v, hv, h⟩

theorem mem_meetingFourSets_iff {n k : ℕ} {c : Col n k} (hc : Admissible c) (i : Fin k)
  {S : Finset (Verts n)} :
  S ∈ meetingFourSets c i ↔
    S.card = 4 ∧ (classIn c i S).card = 2 ∧ ∃ v ∈ S, (nb c i v S).card = 2 := by
  constructor
  · rw [meetingFourSets, Finset.mem_biUnion]
    rintro ⟨v, hv, hS⟩
    obtain ⟨h1, h2, h3, h4⟩ := mem_pathFourSets.mp hS
    exact ⟨h1, h2, v, h3, h4⟩
  · rw [meetingFourSets, Finset.mem_biUnion]
    rintro ⟨h1, h2, v, hvS, hvnb⟩
    have hle : (nb c i v S).card ≤ (nb c i v (Finset.univ : Finset (Verts n))).card :=
      Finset.card_le_card fun x hx =>
        mem_nb.mpr ⟨(mem_nb.mp hx).1, Finset.mem_univ x, (mem_nb.mp hx).2.2⟩
    have hge : 2 ≤ (nb c i v (Finset.univ : Finset (Verts n))).card := by
      have h1 : (nb c i v S).card = 2 := hvnb
      rw [← h1]
      exact hle
    have hne : (nb c i v (Finset.univ : Finset (Verts n))).card = 2 :=
      le_antisymm (nb_univ_card_le_two hc i v) hge
    exact ⟨v, mem_twoA.mpr hne, mem_pathFourSets.mpr ⟨h1, h2, hvS, hvnb⟩⟩


/-! ### §7  the two kinds of pairs -/

/-- **THE PAIRS SPLIT INTO THE TWO KINDS**: every two-element subset of a colour class is either the
pair of edges of a two-edge path (there are `|twoA c i|` of them) or a disjoint pair, and the two
kinds together are all `choose |classF c i| 2` pairs.  In particular the two-edge paths of colour
`i` never outnumber the pairs of colour-`i` edges. -/
theorem twoA_card_le_choose_two {n k : ℕ} {c : Col n k} (hc : Admissible c) (i : Fin k) :
    (twoA c i).card ≤ Nat.choose (classF c i).card 2 := by
  have hsub : meetPairs c i ⊆ pairOf c i := meetPairs_subset_pairOf hc i
  have hle : (meetPairs c i).card ≤ (pairOf c i).card := Finset.card_le_card hsub
  rw [card_meetPairs hc i, card_pairOf] at hle
  omega

/-- The two kinds of pairs add up: `|meetPairs c i| + |disjPairs c i| = choose |classF c i| 2`. -/
theorem sum_card_meet_disj {n k : ℕ} {c : Col n k} (hc : Admissible c) (i : Fin k) :
    (meetPairs c i).card + (disjPairs c i).card = Nat.choose (classF c i).card 2 := by
  have hle : (twoA c i).card ≤ Nat.choose (classF c i).card 2 := twoA_card_le_choose_two hc i
  rw [add_comm, card_disjPairs hc i, card_meetPairs hc i]
  omega

/-- **THE PARTITION IS VERIFIED ON ALL FOUR CONSTRUCTIONS OF `Tables.lean`.**  For every colour, the
two-element subsets of the colour class split into the path pairs and the disjoint pairs. -/
theorem sum_card_meet_disj_sixCol : ∀ i : Fin 5,
    (meetPairs sixCol i).card + (disjPairs sixCol i).card = Nat.choose (classF sixCol i).card 2 := by
  native_decide

theorem sum_card_meet_disj_nineCol : ∀ i : Fin 8,
    (meetPairs nineCol i).card + (disjPairs nineCol i).card = Nat.choose (classF nineCol i).card 2 := by
  native_decide

theorem sum_card_meet_disj_tenCol : ∀ i : Fin 9,
    (meetPairs tenCol i).card + (disjPairs tenCol i).card = Nat.choose (classF tenCol i).card 2 := by
  native_decide

theorem sum_card_meet_disj_elevenCol : ∀ i : Fin 10,
    (meetPairs elevenCol i).card + (disjPairs elevenCol i).card
      = Nat.choose (classF elevenCol i).card 2 := by
  native_decide


/-! ### §8  the endpoints of an edge, and two same-coloured edges -/

/-- **THE VERTEX SET OF AN EDGE.** -/
noncomputable def endsF {n : ℕ} (e : Sym2 (Verts n)) : Finset (Verts n) :=
  (Finset.univ : Finset (Verts n)).filter fun v => Sym2.Mem v e

theorem mem_endsF {n : ℕ} {e : Sym2 (Verts n)} {v : Verts n} :
    v ∈ endsF e ↔ Sym2.Mem v e :=
  ⟨fun h => (Finset.mem_filter.mp h).2, fun h => Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩⟩

/-- **EVERY EDGE OF `K_n` IS AN EDGE ON THE WHOLE VERTEX SET.** -/
theorem mem_edgeFinset_univ_of_offDiag {n : ℕ} {e : Sym2 (Verts n)} (hd : OffDiag e) :
    e ∈ edgeFinset (Finset.univ : Finset (Verts n)) := by
  rw [mem_edgeFinset]
  exact ⟨Finset.mem_sym2_iff.mpr fun a ha => Finset.mem_univ a, hd⟩

/-- **AN EDGE HAS EXACTLY TWO ENDPOINTS.** -/
theorem card_endsF {n : ℕ} {e : Sym2 (Verts n)} (hd : OffDiag e) : (endsF e).card = 2 :=
  card_filter_mem_edgeFinset (mem_edgeFinset_univ_of_offDiag hd)

theorem endsF_subset_of_mem_edgeFinset {n : ℕ} {S : Finset (Verts n)} {e : Sym2 (Verts n)}
    (he : e ∈ edgeFinset S) : endsF e ⊆ S :=
  fun v hv => mem_of_mem_edgeFinset he ((mem_endsF.mp hv))

theorem mem_edgeFinset_endsF {n : ℕ} {e : Sym2 (Verts n)} (hd : OffDiag e) :
    e ∈ edgeFinset (endsF e) := by
  rw [mem_edgeFinset]
  exact ⟨Finset.mem_sym2_iff.mpr fun a ha => (mem_endsF.mpr ha), hd⟩

/-- **TWO EDGES WITH NO COMMON ENDPOINT.** -/
def Disj2 {n : ℕ} (e f : Sym2 (Verts n)) : Prop :=
  ∀ v : Verts n, Sym2.Mem v e → ¬ Sym2.Mem v f

theorem card_union_endsF {n : ℕ} {e f : Sym2 (Verts n)} {he : OffDiag e} {hf : OffDiag f}
    (hd : Disj2 e f) : (endsF e ∪ endsF f).card = 4 := by
  have hdisj : Disjoint (endsF e) (endsF f) := Finset.disjoint_left.mpr fun v hv1 hv2 =>
    absurd ((mem_endsF.mp hv2)) (hd v (mem_endsF.mp hv1))
  calc (endsF e ∪ endsF f).card = (endsF e).card + (endsF f).card :=
        Finset.card_union_of_disjoint hdisj
    _ = 2 + 2 := by rw [card_endsF he, card_endsF hf]
    _ = 4 := by omega

/-- **THE UNIQUE FOUR-SET CONTAINING TWO DISJOINT EDGES** is the union of their endpoints. -/
theorem span_endsF_eq {n : ℕ} {e f : Sym2 (Verts n)} {he : OffDiag e} {hf : OffDiag f}
    (hd : Disj2 e f) {S : Finset (Verts n)} (hS : S.card = 4) (hee : e ∈ edgeFinset S)
    (hef : f ∈ edgeFinset S) : endsF e ∪ endsF f = S := by
  refine Finset.eq_of_subset_of_card_le ?_ ?_
  · intro v hv
    rcases Finset.mem_union.mp hv with hv | hv
    · exact endsF_subset_of_mem_edgeFinset hee hv
    · exact endsF_subset_of_mem_edgeFinset hef hv
  · rw [hS, card_union_endsF (he := he) (hf := hf) hd]

/-! ### two colour-`i` edges in a triangle meet -/

private theorem exists_card_eq_two_of_sum_four {α : Type*} {s : Finset α} {f : α → ℕ}
    (hf : ∀ a ∈ s, f a ≤ 2) (hcard : s.card = 3) (hsum : (∑ a ∈ s, f a) = 4) :
    ∃ a ∈ s, f a = 2 := by
  by_contra hcon
  have h1 : ∀ a ∈ s, f a ≤ 1 := fun a ha => by
    by_cases h2 : f a = 2
    · exact absurd (h2 ▸ ⟨a, ha, rfl⟩) hcon
    · have h3 := hf a ha
      omega
  have h2 : (∑ a ∈ s, f a) ≤ ∑ _a ∈ s, 1 := Finset.sum_le_sum fun a ha => h1 a ha
  have h3 : (∑ _a ∈ s, 1) = s.card := by simp [Finset.sum_const]
  omega

/-- **TWO COLOUR-`i` EDGES INSIDE A TRIANGLE MEET.**  If `T` has three elements and colour `i`
occurs on exactly two of its edges, then one of the three vertices has both of them as its
colour-`i` neighbours inside `T`.  This is a pigeonhole consequence of
`sum_nb_card_eq_two_mul_classIn_card`: the three vertices are incident with `4` colour-`i` edges
between them, so one of them is incident with two. -/
theorem meeting_of_triangle {n k : ℕ} {c : Col n k} (hc : Admissible c) (i : Fin k)
    {T : Finset (Verts n)} (hT : T.card = 3) (h2 : (classIn c i T).card = 2) :
    ∃ v ∈ T, (nb c i v T).card = 2 := by
  have hsum := sum_nb_card_eq_two_mul_classIn_card (c := c) i T
  rw [h2] at hsum
  exact exists_card_eq_two_of_sum_four (s := T) (f := fun v => (nb c i v T).card)
    (fun v hv => by
      have hsub : nb c i v T ⊆ nb c i v (Finset.univ : Finset (Verts n)) := by
        intro a ha
        exact mem_nb.mpr ⟨(mem_nb.mp ha).1, Finset.mem_univ _, (mem_nb.mp ha).2.2⟩
      exact le_trans (Finset.card_le_card hsub) (nb_univ_card_le_two hc i v))
    hT hsum

/-! ### the same pair of `i`-edges determines the four-set, unless they meet -/

/-- **A FOUR-SET WITH TWO COLOUR-`i` EDGES AT `v` HAS NO OTHER.**  If `S` has four elements and
`v ∈ S` has two colour-`i` neighbours in `S`, then those two edges are the whole colour-`i` class
of `S`, so the four-set carries the two-edge path of colour `i` centred at `v`. -/
theorem classIn_eq_iEdgesAt {n k : ℕ} {c : Col n k} (hc : Admissible c) {i : Fin k}
    {S : Finset (Verts n)} (hS : S.card = 4) {v : Verts n} (hvS : v ∈ S)
    (hnb : (nb c i v S).card = 2) : classIn c i S = iEdgesAt c i v := by
  have hnbU : nb c i v S = nb c i v (Finset.univ : Finset (Verts n)) := by
    refine Finset.eq_of_subset_of_card_le (fun a ha =>
      mem_nb.mpr ⟨(mem_nb.mp ha).1, Finset.mem_univ _, (mem_nb.mp ha).2.2⟩)
      (by rw [hnb]; exact nb_univ_card_le_two hc i v)
  have hkey : iEdgesAt c i v = classIn c i S := by
    refine Finset.eq_of_subset_of_card_le ?_ ?_
    · intro e he
      obtain ⟨a, ha, heq⟩ := (mem_iEdgesAt i).mp he
      rw [heq]
      have ha' : a ∈ nb c i v S := hnbU ▸ ha
      exact mem_classIn.mpr
        ⟨mem_edgeFinset_mk hvS (mem_nb.mp ha').2.1 (Ne.symm (mem_nb.mp ha').1),
          (mem_nb.mp ha').2.2⟩
    · rw [card_iEdgesAt i v, ← hnbU, hnb]
      exact classIn_card_le_two hc i S hS
  exact hkey.symm

private theorem exists_pair_card_eq_two {α : Type*} [DecidableEq α] {p : Finset α} (hp : p.card = 2) :
    ∃ e f : α, p = insert e (insert f ∅) ∧ e ∈ p ∧ f ∈ p ∧ e ≠ f := by
  obtain ⟨e, f, hef, hset⟩ := Finset.card_eq_two.mp hp
  refine ⟨e, f, ?_, ?_, ?_, hef⟩
  · rw [hset]; rfl
  · rw [hset]; exact Finset.mem_insert_self e {f}
  · rw [hset]; exact Finset.mem_insert_of_mem (Finset.mem_singleton.mpr rfl)

/-- **TWO DISTINCT COLOUR-`i` EDGES OF A FOUR-SET THROUGH A COMMON VERTEX `v` GIVE THE PATH.** -/
theorem pathFourSets_of_mem_common {n k : ℕ} {c : Col n k} (hc : Admissible c) {i : Fin k}
    {S : Finset (Verts n)} (hS : S.card = 4) {v : Verts n}
    {e f : Sym2 (Verts n)} (hef : e ≠ f) (he : e ∈ classIn c i S) (hf : f ∈ classIn c i S)
    (hv_e : Sym2.Mem v e) (hv_f : Sym2.Mem v f) :
    S ∈ pathFourSets c i v := by
  obtain ⟨x, hxe⟩ := Sym2.mem_iff_exists.mp hv_e
  obtain ⟨y, hyf⟩ := Sym2.mem_iff_exists.mp hv_f
  have he' : s(v, x) ∈ classIn c i S := hxe ▸ he
  have hf' : s(v, y) ∈ classIn c i S := hyf ▸ hf
  have hxv : x ≠ v := Ne.symm ((mem_edgeFinset.mp (mem_classIn.mp he').1).2 v x rfl)
  have hyv : y ≠ v := Ne.symm ((mem_edgeFinset.mp (mem_classIn.mp hf').1).2 v y rfl)
  have hxy : x ≠ y := by
    intro h
    apply hef
    rw [hxe, hyf, h]
  have hxS : x ∈ S := mem_of_mem_edgeFinset (mem_classIn.mp he').1 (hxe ▸ Sym2.mem_mk_right v x)
  have hyS : y ∈ S := mem_of_mem_edgeFinset (mem_classIn.mp hf').1 (hyf ▸ Sym2.mem_mk_right v y)
  have hxnb : x ∈ nb c i v S := mem_nb.mpr ⟨hxv, hxS, (mem_classIn.mp he').2⟩
  have hynb : y ∈ nb c i v S := mem_nb.mpr ⟨hyv, hyS, (mem_classIn.mp hf').2⟩
  have hvS : v ∈ S := mem_of_mem_edgeFinset (mem_classIn.mp he').1 (hxe ▸ Sym2.mem_mk_left v x)
  have hcardnb : (nb c i v S).card = 2 := by
    have hsub : nb c i v S ⊆ nb c i v (Finset.univ : Finset (Verts n)) := by
      intro z hz
      exact mem_nb.mpr ⟨(mem_nb.mp hz).1, Finset.mem_univ _, (mem_nb.mp hz).2.2⟩
    refine le_antisymm ?_ ?_
    · exact le_trans (Finset.card_le_card hsub) (nb_univ_card_le_two hc i v)
    · rw [← card_pair_eq_two hxy]
      exact Finset.card_le_card (fun z hz => by
        rw [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with hz | hz
        · rw [hz]; exact hxnb
        · rw [hz]; exact hynb)
  have hcard2 : (classIn c i S).card = 2 :=
    le_antisymm (classIn_card_le_two hc i S hS) (by
      rw [← card_pair_eq_two hef]
      exact Finset.card_le_card (fun z hz => by
        rw [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with hz | hz
        · rw [hz]; exact he
        · rw [hz]; exact hf))
  exact mem_pathFourSets.mpr ⟨hS, hcard2, hvS, hcardnb⟩

/-- **THE TWO COLOUR-`i` EDGES OF A FOUR-SET EITHER MEET — AND THEN THE FOUR-SET CARRIES THE
TWO-EDGE PATH — OR THEY ARE VERTEX-DISJOINT.** -/
theorem meet_or_disj {n k : ℕ} {c : Col n k} (hc : Admissible c) {i : Fin k}
    {S : Finset (Verts n)} (hS : S ∈ twoFourSets c i) {e f : Sym2 (Verts n)}
    (hef : e ≠ f) (he : e ∈ classIn c i S) (hf : f ∈ classIn c i S) :
    (∃ v : Verts n, S ∈ pathFourSets c i v) ∨ Disj2 e f := by
  by_cases hex : ∃ v, Sym2.Mem v e ∧ Sym2.Mem v f
  · left
    obtain ⟨v, hv1, hv2⟩ := hex
    refine ⟨v, ?_⟩
    exact pathFourSets_of_mem_common hc (mem_twoFourSets.mp hS).1 hef he hf hv1 hv2
  · right
    have hne := hex
    intro v hv1 hv2
    exact absurd ⟨v, hv1, hv2⟩ hne

/-- **THE SAME PAIR OF COLOUR-`i` EDGES DETERMINES THE FOUR-SET, UNLESS THE TWO EDGES MEET.**  If
two four-element vertex sets carry exactly the same two colour-`i` edges, then either the two edges
are vertex-disjoint — in which case the two four-sets are *equal*, because a pair of disjoint edges
spans all four vertices — or the two edges meet at a vertex `v`, in which case both four-sets carry
the two-edge path of colour `i` centred at `v`. -/
theorem meeting_of_ne_classIn {n k : ℕ} {c : Col n k} (hc : Admissible c) {i : Fin k}
    {S S' : Finset (Verts n)} (hS : S ∈ twoFourSets c i) (hS' : S' ∈ twoFourSets c i)
    (hp : classIn c i S = classIn c i S') :
    S = S' ∨ ∃ v, S ∈ pathFourSets c i v ∧ S' ∈ pathFourSets c i v := by
  obtain ⟨e, f, hpef, heS, hfS, hef⟩ := exists_pair_card_eq_two (mem_twoFourSets.mp hS).2
  have heS' : e ∈ classIn c i S' := by rw [← hp]; exact heS
  have hfS' : f ∈ classIn c i S' := by rw [← hp]; exact hfS
  by_cases hmeet : ∃ v, S ∈ pathFourSets c i v
  · obtain ⟨v, hv⟩ := hmeet
    obtain ⟨h1, h2, hvS, hnb⟩ := mem_pathFourSets.mp hv
    have hce : classIn c i S = iEdgesAt c i v := classIn_eq_iEdgesAt (v := v) hc h1 hvS hnb
    have heoff : OffDiag e := by
      have hx := (mem_classIn.mp heS).1
      rw [mem_edgeFinset] at hx
      exact hx.2
    have hfoff : OffDiag f := by
      have hx := (mem_classIn.mp hfS).1
      rw [mem_edgeFinset] at hx
      exact hx.2
    obtain ⟨a, hxe⟩ := Sym2.mem_iff_exists.mp (mem_iEdgesAt_of_mem i (hce ▸ heS))
    obtain ⟨b, hyf⟩ := Sym2.mem_iff_exists.mp (mem_iEdgesAt_of_mem i (hce ▸ hfS))
    have hvae : a ≠ v := Ne.symm (heoff v a hxe)
    have hvb : b ≠ v := Ne.symm (hfoff v b hyf)
    have hab : a ≠ b := by
      intro h
      apply hef
      rw [hxe, hyf, h]
    have huniq : ∀ w, Sym2.Mem w e → Sym2.Mem w f → w = v := by
      intro w hwe hwf
      rcases (mem_iff_eq hxe).mp hwe with h1 | h1
      · exact h1
      · rcases (mem_iff_eq hyf).mp hwf with h2 | h2
        · exact h2
        · exact (hab (h1.symm.trans h2)).elim
    obtain ⟨w, hw⟩ | hd2 := meet_or_disj hc hS' hef heS' hfS'
    · obtain ⟨h5, h6, hwS, hwnb⟩ := mem_pathFourSets.mp hw
      have hce2 : classIn c i S' = iEdgesAt c i w := classIn_eq_iEdgesAt (v := w) hc h5 hwS hwnb
      have hwv : w = v := huniq w (mem_iEdgesAt_of_mem i (hce2 ▸ heS'))
        (mem_iEdgesAt_of_mem i (hce2 ▸ hfS'))
      exact Or.inr ⟨v, hv, hwv ▸ hw⟩
    · exact (hd2 v (mem_iEdgesAt_of_mem i (hce ▸ heS))
        (mem_iEdgesAt_of_mem i (hce ▸ hfS))).elim
  · have hd : Disj2 e f :=
      (meet_or_disj hc hS hef heS hfS).resolve_left (fun h => absurd h hmeet)
    have heoff : OffDiag e := by
      have hx := (mem_classIn.mp heS).1
      rw [mem_edgeFinset] at hx
      exact hx.2
    have hfoff : OffDiag f := by
      have hx := (mem_classIn.mp hfS).1
      rw [mem_edgeFinset] at hx
      exact hx.2
    refine Or.inl ?_
    exact (span_endsF_eq (he := heoff) (hf := hfoff) hd (mem_twoFourSets.mp hS).1
      (mem_classIn.mp heS).1 (mem_classIn.mp hfS).1).symm.trans
      (span_endsF_eq (he := heoff) (hf := hfoff) hd (mem_twoFourSets.mp hS').1
        (mem_classIn.mp heS').1 (mem_classIn.mp hfS').1)
/-! ### a pair of colour-`i` edges through a common vertex `v` -/

/-- A two-element finset written as two `insert`s has two elements. -/
private theorem card_insert2 {α : Type*} [DecidableEq α] {e f : α} (h : e ≠ f) :
    ((insert e (insert f ∅) : Finset α)).card = 2 := by
  rw [show (insert e (insert f ∅) : Finset α) = {e, f} from rfl, card_pair_eq_two h]

/-- **A PAIR OF COLOUR-`i` EDGES THROUGH A COMMON VERTEX `v` IS THE PAIR AT `v`.**  If two
distinct colour-`i` edges of `K_n` both contain `v`, then they are the whole edge set
`iEdgesAt c i v` (a colour class has at most two edges at a vertex), and `v` is a path centre. -/
theorem pairOf_eq_iEdgesAt {n k : ℕ} {c : Col n k} (hc : Admissible c) {i : Fin k}
    {e f : Sym2 (Verts n)} {v : Verts n} (hef : e ≠ f) (he : e ∈ classF c i)
    (hf : f ∈ classF c i) (hv_e : Sym2.Mem v e) (hv_f : Sym2.Mem v f) :
    insert e (insert f ∅) = iEdgesAt c i v ∧ v ∈ twoA c i := by
  obtain ⟨a, hxe⟩ := Sym2.mem_iff_exists.mp hv_e
  obtain ⟨b, hyf⟩ := Sym2.mem_iff_exists.mp hv_f
  have heoff : OffDiag e := by
    have hx := (mem_classIn.mp (show e ∈ classIn c i (Finset.univ : Finset (Verts n)) from he)).1
    rw [mem_edgeFinset] at hx
    exact hx.2
  have hfoff : OffDiag f := by
    have hx := (mem_classIn.mp (show f ∈ classIn c i (Finset.univ : Finset (Verts n)) from hf)).1
    rw [mem_edgeFinset] at hx
    exact hx.2
  have hvae : a ≠ v := Ne.symm (heoff v a hxe)
  have hvb : b ≠ v := Ne.symm (hfoff v b hyf)
  have hab : a ≠ b := by
    intro h
    apply hef
    rw [hxe, hyf, h]
  have hain : a ∈ nb c i v (Finset.univ : Finset (Verts n)) :=
    mem_nb.mpr ⟨hvae, Finset.mem_univ a, hxe ▸ mem_classF he⟩
  have hbin : b ∈ nb c i v (Finset.univ : Finset (Verts n)) :=
    mem_nb.mpr ⟨hvb, Finset.mem_univ b, hyf ▸ mem_classF hf⟩
  have heq : insert e (insert f ∅) = iEdgesAt c i v := by
    refine Finset.eq_of_subset_of_card_le (fun z hz => ?_) ?_
    · rcases Finset.mem_insert.mp hz with hze | hz
      · rw [hze]; exact (mem_iEdgesAt i).mpr ⟨a, hain, hxe⟩
      · have hzf : z = f := by
          rcases Finset.mem_insert.mp hz with h1 | h1
          · exact h1
          · exact absurd h1 (by simp)
        rw [hzf]; exact (mem_iEdgesAt i).mpr ⟨b, hbin, hyf⟩
    · rw [card_insert2 hef]; exact card_iEdgesAt_le_two hc i v
  refine ⟨heq, ?_⟩
  rw [mem_twoA, ← card_iEdgesAt i v, ← heq, card_insert2 hef]

/-- **A DISJOINT PAIR OF COLOUR-`i` EDGES IS NOT A PATH PAIR.**  Two colour-`i` edges which meet
at a vertex `v` are the two edges of a two-edge path, i.e. a member of `meetPairs c i`. -/
theorem disj_of_not_mem_meetPairs {n k : ℕ} {c : Col n k} (hc : Admissible c) {i : Fin k}
    {p : Finset (Sym2 (Verts n))} (hp : p ∈ disjPairs c i) :
    ∀ e f : Sym2 (Verts n), e ≠ f → p = insert e (insert f ∅) → Disj2 e f := by
  intro e f hef hpe
  intro v hv1 hv2
  obtain ⟨hp1, hp2⟩ := mem_disjPairs.mp hp
  have hsub : p ⊆ classF c i := (mem_pairOf.mp hp1).1
  have heF : e ∈ classF c i := by
    refine hsub ?_
    rw [hpe]
    simp
  have hfF : f ∈ classF c i := by
    refine hsub ?_
    rw [hpe]
    simp
  obtain ⟨heq, htwo⟩ := pairOf_eq_iEdgesAt hc hef heF hfF hv1 hv2
  exact absurd (mem_meetPairs.mpr ⟨v, htwo, hpe.trans heq⟩) hp2

/-! ### a disjoint pair spans exactly one four-set -/

/-- **THE FOUR-SETS DOUBLED IN COLOUR `i` WHICH CARRY NO TWO-EDGE PATH OF COLOUR `i`** — those
spanned by the two *disjoint* colour-`i` edges. -/
def nonMeetingFourSets {n k : ℕ} (c : Col n k) (i : Fin k) : Finset (Finset (Verts n)) :=
  twoFourSets c i \ meetingFourSets c i

theorem mem_nonMeetingFourSets {n k : ℕ} {c : Col n k} {i : Fin k} {S : Finset (Verts n)} :
    S ∈ nonMeetingFourSets c i ↔ S ∈ twoFourSets c i ∧ S ∉ meetingFourSets c i :=
  Finset.mem_sdiff

theorem nonMeetingFourSets_subset_twoFourSets {n k : ℕ} (c : Col n k) (i : Fin k) :
    nonMeetingFourSets c i ⊆ twoFourSets c i := Finset.sdiff_subset

/-- **THE TWO `i`-EDGES OF A FOUR-SET WHICH CARRIES NO PATH ARE DISJOINT.** -/
theorem Disj2_of_mem_nonMeetingFourSets {n k : ℕ} {c : Col n k} (hc : Admissible c)
    {i : Fin k} {S : Finset (Verts n)} (hS : S ∈ nonMeetingFourSets c i)
    {e f : Sym2 (Verts n)} (hef : e ≠ f) (he : e ∈ classIn c i S) (hf : f ∈ classIn c i S) :
    Disj2 e f := by
  have hmem := mem_nonMeetingFourSets.mp hS
  by_cases hex : ∃ v, Sym2.Mem v e ∧ Sym2.Mem v f
  · obtain ⟨v, hv1, hv2⟩ := hex
    have hpath : S ∈ pathFourSets c i v :=
      pathFourSets_of_mem_common hc (mem_twoFourSets.mp hmem.1).1 hef he hf hv1 hv2
    exact absurd ((mem_meetingFourSets i).mpr ⟨v, twoA_of_mem_pathFourSets hc hpath, hpath⟩) hmem.2
  · exact fun v hv1 hv2 => absurd ⟨v, hv1, hv2⟩ hex

/-- **A DISJOINT PAIR SPANS EXACTLY ONE FOUR-SET.**  For every disjoint pair `p` of colour-`i`
edges there is a four-element vertex set whose colour-`i` edges are exactly the two edges of `p`,
and that four-set carries no two-edge path. -/
theorem exists_nonMeeting_of_mem_disjPairs {n k : ℕ} {c : Col n k} (hc : Admissible c)
    {i : Fin k} {p : Finset (Sym2 (Verts n))} (hp : p ∈ disjPairs c i) :
    ∃ S, S ∈ nonMeetingFourSets c i ∧ classIn c i S = p := by
  obtain ⟨hp1, hp2⟩ := mem_disjPairs.mp hp
  obtain ⟨e, f, hpef, heP, hfP, hef⟩ := exists_pair_card_eq_two (mem_pairOf.mp hp1).2
  have hsubF : p ⊆ classF c i := (mem_pairOf.mp hp1).1
  have heF : e ∈ classF c i := hsubF (hpef ▸ heP)
  have hfF : f ∈ classF c i := hsubF (hpef ▸ hfP)
  have heoff : OffDiag e := by
    have hx := (mem_classIn.mp (show e ∈ classIn c i (Finset.univ : Finset (Verts n)) from heF)).1
    rw [mem_edgeFinset] at hx
    exact hx.2
  have hfoff : OffDiag f := by
    have hx := (mem_classIn.mp (show f ∈ classIn c i (Finset.univ : Finset (Verts n)) from hfF)).1
    rw [mem_edgeFinset] at hx
    exact hx.2
  have hdisj : Disj2 e f := disj_of_not_mem_meetPairs hc hp (e := e) (f := f) hef hpef
  have hmemE : ∀ z : Verts n, Sym2.Mem z e → z ∈ endsF e ∪ endsF f := by
    intro z hz
    exact Finset.mem_union_left _ ((mem_endsF.mpr hz))
  have hmemF : ∀ z : Verts n, Sym2.Mem z f → z ∈ endsF e ∪ endsF f := by
    intro z hz
    exact Finset.mem_union_right _ ((mem_endsF.mpr hz))
  have hT4 : (endsF e ∪ endsF f).card = 4 :=
    card_union_endsF (he := heoff) (hf := hfoff) hdisj
  have hTe : e ∈ edgeFinset (endsF e ∪ endsF f) :=
    mem_edgeFinset.mpr ⟨Finset.mem_sym2_iff.mpr hmemE, heoff⟩
  have hTf : f ∈ edgeFinset (endsF e ∪ endsF f) :=
    mem_edgeFinset.mpr ⟨Finset.mem_sym2_iff.mpr hmemF, hfoff⟩
  have hsub : p ⊆ edgeFinset (endsF e ∪ endsF f) := by
    intro z hz
    rw [hpef] at hz
    rcases Finset.mem_insert.mp hz with r1 | hz2
    · rw [r1]; exact hTe
    · rcases Finset.mem_insert.mp hz2 with r2 | r3
      · rw [r2]; exact hTf
      · exact absurd r3 (by simp)
  have hsub1 : insert e (insert f ∅) ⊆ classIn c i (endsF e ∪ endsF f) := by
    intro z hz
    rcases Finset.mem_insert.mp hz with r1 | hz2
    · rw [r1]; exact mem_classIn.mpr ⟨hTe, mem_classF heF⟩
    · rcases Finset.mem_insert.mp hz2 with r2 | r3
      · rw [r2]; exact mem_classIn.mpr ⟨hTf, mem_classF hfF⟩
      · exact absurd r3 (by simp)
  have hcard2 : (classIn c i (endsF e ∪ endsF f)).card = 2 :=
    le_antisymm (classIn_card_le_two hc i _ hT4) (by
      rw [← card_insert2 hef]
      exact Finset.card_le_card hsub1)
  have hclass' : insert e (insert f ∅) = classIn c i (endsF e ∪ endsF f) := by
    refine Finset.eq_of_subset_of_card_le hsub1 ?_
    rw [card_insert2 hef, hcard2]
  have hclass : classIn c i (endsF e ∪ endsF f) = p := hclass'.symm.trans hpef.symm
  have hnot : (endsF e ∪ endsF f) ∉ meetingFourSets c i := by
    intro hT
    obtain ⟨v, hv, hpath⟩ := (mem_meetingFourSets i).mp hT
    obtain ⟨h1, h2, hvT, hnb⟩ := mem_pathFourSets.mp hpath
    have hce : classIn c i (endsF e ∪ endsF f) = iEdgesAt c i v :=
      classIn_eq_iEdgesAt (v := v) hc h1 hvT hnb
    have heT : e ∈ classIn c i (endsF e ∪ endsF f) := by rw [hclass]; exact heP
    have hfT : f ∈ classIn c i (endsF e ∪ endsF f) := by rw [hclass]; exact hfP
    have hM1 : Sym2.Mem v e := mem_iEdgesAt_of_mem i (by rw [← hce]; exact heT)
    have hM2 : Sym2.Mem v f := mem_iEdgesAt_of_mem i (by rw [← hce]; exact hfT)
    obtain ⟨heq, htwo⟩ := pairOf_eq_iEdgesAt hc hef heF hfF hM1 hM2
    have hpEq : p = iEdgesAt c i v := hpef.trans heq
    exact absurd (mem_meetPairs.mpr ⟨v, htwo, hpEq⟩) hp2
  exact ⟨endsF e ∪ endsF f,
    mem_nonMeetingFourSets.mpr ⟨mem_twoFourSets.mpr ⟨hT4, hcard2⟩, hnot⟩, hclass⟩

/-- **THE FOUR-SET OF A DISJOINT PAIR IS DETERMINED BY THE PAIR.** -/
theorem eq_span_of_mem_nonMeetingFourSets {n k : ℕ} {c : Col n k} (hc : Admissible c)
    {i : Fin k} {S S' : Finset (Verts n)} (hS : S ∈ nonMeetingFourSets c i)
    (hS' : S' ∈ nonMeetingFourSets c i) (hp : classIn c i S = classIn c i S') : S = S' := by
  obtain ⟨hmemS, hmemS'⟩ := mem_nonMeetingFourSets.mp hS, mem_nonMeetingFourSets.mp hS'
  obtain ⟨e, f, hpef, heS, hfS, hef⟩ := exists_pair_card_eq_two (mem_twoFourSets.mp hmemS.1).2
  have heS' : e ∈ classIn c i S' := by rw [← hp]; exact heS
  have hfS' : f ∈ classIn c i S' := by rw [← hp]; exact hfS
  have heoff : OffDiag e := by
    have hx := (mem_classIn.mp heS).1
    rw [mem_edgeFinset] at hx
    exact hx.2
  have hfoff : OffDiag f := by
    have hx := (mem_classIn.mp hfS).1
    rw [mem_edgeFinset] at hx
    exact hx.2
  have hd : Disj2 e f := Disj2_of_mem_nonMeetingFourSets hc hS hef heS hfS
  exact (span_endsF_eq (he := heoff) (hf := hfoff) hd (mem_twoFourSets.mp hmemS.1).1
    (mem_classIn.mp heS).1 (mem_classIn.mp hfS).1).symm.trans
    (span_endsF_eq (he := heoff) (hf := hfoff) hd (mem_twoFourSets.mp hmemS'.1).1
      (mem_classIn.mp heS').1 (mem_classIn.mp hfS').1)

/-- **A FOUR-SET WHICH CARRIES A TWO-EDGE PATH HAS ITS COLOUR-`i` CLASS IN `meetPairs`.** -/
theorem classIn_mem_meetPairs {n k : ℕ} {c : Col n k} (hc : Admissible c) {i : Fin k}
    {S : Finset (Verts n)} (hS : S ∈ meetingFourSets c i) : classIn c i S ∈ meetPairs c i := by
  obtain ⟨v, hv, hpath⟩ := (mem_meetingFourSets i).mp hS
  obtain ⟨h1, h2, h3, h4⟩ := mem_pathFourSets.mp hpath
  refine mem_meetPairs.mpr ⟨v, hv, ?_⟩
  have hce : classIn c i S = iEdgesAt c i v := classIn_eq_iEdgesAt (v := v) hc h1 h3 h4
  exact hce

/-- **A FOUR-SET WHOSE COLOUR-`i` CLASS IS A PATH PAIR CARRIES THAT PATH.** -/
theorem mem_pathFourSets_of_classIn_mem_meetPairs {n k : ℕ} {c : Col n k} (hc : Admissible c)
    {i : Fin k} {S : Finset (Verts n)} (hS : S ∈ twoFourSets c i)
    (hmeet : classIn c i S ∈ meetPairs c i) : ∃ v, S ∈ pathFourSets c i v := by
  obtain ⟨v, hv, hclass⟩ := mem_meetPairs.mp hmeet
  obtain ⟨e, f, hpef, heS, hfS, hef⟩ := exists_pair_card_eq_two (mem_twoFourSets.mp hS).2
  have hM1 : Sym2.Mem v e := mem_iEdgesAt_of_mem (c := c) i (hclass ▸ heS)
  have hM2 : Sym2.Mem v f := mem_iEdgesAt_of_mem (c := c) i (hclass ▸ hfS)
  exact ⟨v, pathFourSets_of_mem_common hc (mem_twoFourSets.mp hS).1 hef heS hfS hM1 hM2⟩

/-- **THE COLOUR-`i` CLASS OF A FOUR-SET WHICH CARRIES NO PATH IS A DISJOINT PAIR.** -/
theorem classIn_mem_disjPairs {n k : ℕ} {c : Col n k} (hc : Admissible c) {i : Fin k}
    {S : Finset (Verts n)} (hS : S ∈ nonMeetingFourSets c i) : classIn c i S ∈ disjPairs c i := by
  have hmem := mem_nonMeetingFourSets.mp hS
  have hsub : classIn c i S ⊆ classF c i := by
    intro z hz
    have hz1 := (mem_classIn.mp hz).1
    have hz2 := (mem_classIn.mp hz).2
    have hz3 := mem_edgeFinset.mp hz1
    show z ∈ classIn c i (Finset.univ : Finset (Verts n))
    refine mem_classIn.mpr ⟨mem_edgeFinset.mpr
      ⟨Finset.mem_sym2_iff.mpr fun y hy => Finset.mem_univ y, hz3.2⟩, hz2⟩
  have hcard : (classIn c i S).card = 2 := (mem_twoFourSets.mp hmem.1).2
  refine mem_disjPairs.mpr ⟨mem_pairOf.mpr ⟨hsub, hcard⟩, ?_⟩
  intro hmeet
  obtain ⟨v, hv⟩ := mem_pathFourSets_of_classIn_mem_meetPairs hc hmem.1 hmeet
  exact absurd ((mem_meetingFourSets i).mpr ⟨v, twoA_of_mem_pathFourSets hc hv, hv⟩) hmem.2

/-- **THE BIJECTION `disjPairs c i ≃ nonMeetingFourSets c i`.**  A two-element set of
colour-`i` edges which is not a path pair spans **exactly one** four-set with a doubled colour
`i`, and that four-set determines the pair. -/
theorem card_nonMeetingFourSets {n k : ℕ} {c : Col n k} (hc : Admissible c) (i : Fin k) :
    (nonMeetingFourSets c i).card = (disjPairs c i).card := by
  refine Finset.card_bij (s := nonMeetingFourSets c i) (t := disjPairs c i)
    (fun S _ => classIn c i S)
    (fun S hS => classIn_mem_disjPairs hc hS)
    (fun S hS T hT heq => eq_span_of_mem_nonMeetingFourSets hc hS hT heq)
    (fun p hp => by
      obtain ⟨S, hS, hclass⟩ := exists_nonMeeting_of_mem_disjPairs hc hp
      refine ⟨S, hS, hclass⟩)

/-! ### §10  the path half, exactly -/

private theorem exists_insert_of_subset_card {n : ℕ} {S T : Finset (Verts n)} (hST : T ⊆ S)
    (hS : S.card = 4) (hT : T.card = 3) : ∃ x, x ∉ T ∧ insert x T = S := by
  have hcard1 : (S \ T).card = 1 := by
    have h := Finset.card_sdiff_add_card_eq_card hST
    rw [hS, hT] at h
    omega
  obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hcard1
  have hxm : x ∈ S \ T := by rw [hx]; exact Finset.mem_singleton.mpr rfl
  have hxS : x ∈ S := (Finset.mem_sdiff.mp hxm).1
  refine ⟨x, (Finset.mem_sdiff.mp hxm).2, ?_⟩
  refine Finset.Subset.antisymm (fun v hv => ?_) (fun v hvS => ?_)
  · rcases Finset.mem_insert.mp hv with h1 | h1
    · rw [h1]; exact hxS
    · exact hST h1
  · by_cases hvT : v ∈ T
    · exact Finset.mem_insert.mpr (Or.inr hvT)
    · have hvm : v ∈ S \ T := Finset.mem_sdiff.mpr ⟨hvS, hvT⟩
      rw [hx] at hvm
      rw [Finset.mem_singleton] at hvm
      rw [hvm]
      exact Finset.mem_insert_self x T

/-- **THE FOUR-SETS DOUBLED AT `v` ARE EXACTLY THE FOUR-SETS CONTAINING THE PATH.** -/
theorem pathFourSets_eq_containing {n k : ℕ} {c : Col n k} (hc : Admissible c) (i : Fin k)
    (v : Verts n) (hv : v ∈ twoA c i) : pathFourSets c i v = containing (pathVerts c i v) := by
  ext S
  constructor
  · intro hS
    obtain ⟨h1, h2, h3, h4⟩ := mem_pathFourSets.mp hS
    have hnbU : nb c i v S = nb c i v (Finset.univ : Finset (Verts n)) := by
      refine Finset.eq_of_subset_of_card_le (fun a ha =>
        mem_nb.mpr ⟨(mem_nb.mp ha).1, Finset.mem_univ _, (mem_nb.mp ha).2.2⟩) ?_
      rw [h4]; exact (nb_univ_card_le_two hc i v)
    refine mem_containing.mpr ⟨h1, fun y hy => ?_⟩
    rcases Finset.mem_insert.mp hy with hy | hy
    · exact hy ▸ h3
    · rw [← hnbU] at hy; exact (mem_nb.mp hy).2.1
  · intro hS
    obtain ⟨h1, h2⟩ := mem_containing.mp hS
    obtain ⟨x, hx, hS'⟩ := exists_insert_of_subset_card h2 h1 (card_pathVerts hv)
    rw [← hS'] at h2 ⊢
    exact mem_pathFourSets_insert hc i hv hx

/-- **EACH TWO-EDGE PATH LIES IN EXACTLY `n - 3` TIGHT FOUR-SETS** — the exact form of
`Quad.card_pathFourSets_ge`. -/
theorem card_pathFourSets_eq {n k : ℕ} {c : Col n k} (hc : Admissible c) (i : Fin k)
    (v : Verts n) (hv : v ∈ twoA c i) (hn : 4 ≤ n) : (pathFourSets c i v).card = n - 3 := by
  rw [pathFourSets_eq_containing hc i v hv, card_containing _ (card_pathVerts hv) hn]

/-- **THE PATH HALF OF THE CENSUS, EXACTLY: `|meetingFourSets c i| = |twoA c i| * (n-3)`.** -/
theorem card_meetingFourSets {n k : ℕ} {c : Col n k} (hc : Admissible c) (i : Fin k) (hn : 4 ≤ n) :
    (meetingFourSets c i).card = (twoA c i).card * (n - 3) := by
  calc (meetingFourSets c i).card = ∑ v ∈ twoA c i, (pathFourSets c i v).card :=
        Finset.card_biUnion (pairwiseDisjoint_pathFourSets hc i)
    _ = ∑ _v ∈ twoA c i, (n - 3) :=
      Finset.sum_congr rfl fun v hv => card_pathFourSets_eq hc i v hv hn
    _ = (twoA c i).card * (n - 3) := by simp [Finset.sum_const]

/-! ### §11  THE CENSUS IDENTITY -/

/-- **THE EXACT PER-COLOUR FOUR-SET CENSUS.**  For every colour `i` of an admissible colouring,

    `|twoFourSets c i| = choose |E_i| 2 + (n - 4) * (twoA c i).card`:

one four-set for every unordered pair of colour-`i` edges (`choose |E_i| 2` of them), plus
`n - 4` more for every two-edge path of colour `i`.  This is the `card_twoFourSets` step of
`Census.lean` §2*, open since round ~40. -/
theorem card_twoFourSets_census {n k : ℕ} {c : Col n k} (hc : Admissible c) (i : Fin k)
    (hn : 4 ≤ n) :
    (twoFourSets c i).card = Nat.choose (classF c i).card 2 + (n - 4) * (twoA c i).card := by
  have hsub : meetingFourSets c i ⊆ twoFourSets c i := by
    intro S hS
    obtain ⟨v, hv, hpath⟩ := (mem_meetingFourSets i).mp hS
    obtain ⟨h1, h2, h3, h4⟩ := mem_pathFourSets.mp hpath
    exact mem_twoFourSets.mpr ⟨h1, h2⟩
  have hb : (meetingFourSets c i).card ≤ (twoFourSets c i).card := Finset.card_le_card hsub
  have hsd : (twoFourSets c i).card
      = (meetingFourSets c i).card + (nonMeetingFourSets c i).card := by
    have hsub2 : ((twoFourSets c i \ meetingFourSets c i) : Finset (Finset (Verts n))).card
        = (twoFourSets c i).card - (meetingFourSets c i).card := Finset.card_sdiff_of_subset hsub
    show (twoFourSets c i).card = (meetingFourSets c i).card
      + (twoFourSets c i \ meetingFourSets c i).card
    rw [hsub2]
    exact (Nat.add_sub_of_le hb).symm
  have hmeet : (meetingFourSets c i).card = (twoA c i).card * (n - 3) :=
    card_meetingFourSets hc i hn
  have hnon : (nonMeetingFourSets c i).card = (disjPairs c i).card := card_nonMeetingFourSets hc i
  have hdisj : (meetPairs c i).card + (disjPairs c i).card = Nat.choose (classF c i).card 2 :=
    sum_card_meet_disj hc i
  have hma : (meetPairs c i).card = (twoA c i).card := card_meetPairs hc i
  have hle : (twoA c i).card ≤ Nat.choose (classF c i).card 2 := twoA_card_le_choose_two hc i
  have hid : (twoA c i).card * (n - 3) = (n - 4) * (twoA c i).card + (twoA c i).card := by
    have h7 : n - 3 = (n - 4) + 1 := by omega
    rw [h7, Nat.mul_add, Nat.mul_comm (n - 4) (twoA c i).card]
    simp
  omega

/-- **THE GLOBAL CENSUS: THE TIGHT FOUR-SETS ARE COUNTED BY THE PAIRS OF SAME-COLOURED EDGES.**

    `|fiveFourSets c| = ∑_i choose |E_i| 2 + (n - 4) * Paths c`.

The tight four-sets of an admissible colouring are exactly the four-sets carrying a pair of
same-coloured edges, and each pair is counted once for every fourth vertex (`n-3` of them if the
two edges meet, `1` if they are disjoint). -/
theorem fiveFourSets_census {n k : ℕ} {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n) :
    (fiveFourSets c).card = ∑ i : Fin k, Nat.choose (classF c i).card 2 + (n - 4) * Paths c := by
  rw [← sum_twoFourSets hc]
  calc ∑ i : Fin k, (twoFourSets c i).card
      = ∑ i : Fin k, (Nat.choose (classF c i).card 2 + (n - 4) * (twoA c i).card) :=
        Finset.sum_congr rfl fun i _ => card_twoFourSets_census hc i hn
    _ = ∑ i : Fin k, Nat.choose (classF c i).card 2
        + (n - 4) * ∑ i : Fin k, (twoA c i).card := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    _ = ∑ i : Fin k, Nat.choose (classF c i).card 2 + (n - 4) * Paths c := rfl

/-- **THE CENSUS OBSTRUCTION** of `Census.lean` §2*: the number of pairs of same-coloured edges,
plus `(n-4)` times the number of two-edge paths, is at most the number of four-vertex sets:

    `∑_i choose |E_i| 2 + (n - 4) * Paths c ≤ |fourSets|`.

This is a necessary condition on the colour-class profile of an admissible colouring which uses
the *pair* census, not just `∑_i |E_i|`, `Paths c` and `Isolated c`. -/
theorem census_obstruction {n k : ℕ} {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n) :
    ∑ i : Fin k, Nat.choose (classF c i).card 2 + (n - 4) * Paths c ≤ (fourSets n).card :=
  (fiveFourSets_census hc hn).ge.trans (fiveFourSets_le_fourSets (c := c))

/-- **THE PAIR COUNT IS BOUNDED BY THE NUMBER OF TIGHT FOUR-SETS.** -/
theorem sum_choose_two_le_fiveFourSets {n k : ℕ} {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n) :
    ∑ i : Fin k, Nat.choose (classF c i).card 2 ≤ (fiveFourSets c).card := by
  have h := fiveFourSets_census hc hn
  omega

/-- `2 * ∑_i choose |E_i| 2 = ∑_i |E_i| * (|E_i| - 1)`, from `choose_two_mul`. -/
private theorem two_mul_finset_sum_choose {k : ℕ} (F : Fin k → ℕ) :
    2 * ∑ i, Nat.choose (F i) 2 = ∑ i, F i * (F i - 1) := by
  have h : ∀ i : Fin k, 2 * Nat.choose (F i) 2 = F i * (F i - 1) := fun i => choose_two_mul (F i)
  calc 2 * ∑ i, Nat.choose (F i) 2 = ∑ i, 2 * Nat.choose (F i) 2 := by rw [Finset.mul_sum]
    _ = ∑ i, F i * (F i - 1) := Finset.sum_congr rfl fun i _ => h i

/-- **THE COLOUR-CLASS SIZES SUM TO THE NUMBER OF EDGES.** -/
theorem sum_card_classF {n k : ℕ} (c : Col n k) :
    ∑ i : Fin k, (classF c i).card = (edgeFinset (Finset.univ : Finset (Verts n))).card := by
  rw [Finset.card_eq_sum_card_fiberwise (s := edgeFinset (Finset.univ : Finset (Verts n)))
      (t := (Finset.univ : Finset (Fin k))) (f := c)]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [classF]
    rfl
  · intro e he
    exact Finset.mem_univ _

/-- **THE SECOND MOMENT OF THE COLOUR-CLASS PROFILE IS BOUNDED BY THE FOUR-SETS.**

    `∑_i |E_i|² ≤ 2 * C(n,4) + |E(K_n)|`,

because `m² = 2 * choose m 2 + m` and `∑_i choose |E_i| 2 ≤ |tight four-sets| ≤ C(n,4)`. -/
theorem sum_sq_le {n k : ℕ} {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n) :
    ∑ i : Fin k, (classF c i).card * (classF c i).card
      ≤ 2 * (fourSets n).card + (edgeFinset (Finset.univ : Finset (Verts n))).card := by
  have h1 : ∀ i : Fin k, (classF c i).card * (classF c i).card
      = 2 * Nat.choose (classF c i).card 2 + (classF c i).card := by
    intro i
    rw [← mul_sub_add, ← choose_two_mul]
  have h2 : ∑ i : Fin k, (classF c i).card * (classF c i).card
      = 2 * (∑ i : Fin k, Nat.choose (classF c i).card 2) + ∑ i : Fin k, (classF c i).card := by
    calc (∑ i : Fin k, (classF c i).card * (classF c i).card)
        = ∑ i : Fin k, (2 * Nat.choose (classF c i).card 2 + (classF c i).card) :=
          Finset.sum_congr rfl fun i _ => h1 i
      _ = 2 * (∑ i : Fin k, Nat.choose (classF c i).card 2)
          + ∑ i : Fin k, (classF c i).card := by rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  have h3 := sum_choose_two_le_fiveFourSets hc hn
  have h4 := fiveFourSets_le_fourSets (c := c)
  have h5 := sum_card_classF c
  have h6 : (∑ i : Fin k, (classF c i).card * ((classF c i).card - 1))
      = 2 * ∑ i : Fin k, Nat.choose (classF c i).card 2 :=
    (two_mul_finset_sum_choose (fun i => (classF c i).card)).symm
  rw [h2]
  omega

/-! ### §12  the census is machine-checked on the four constructions of `Tables.lean` -/

/-- **THE PER-COLOUR CENSUS ON THE `K₆` WITNESS.** -/
theorem card_twoFourSets_census_sixCol : ∀ i : Fin 5,
    (twoFourSets sixCol i).card = Nat.choose (classF sixCol i).card 2 + (6 - 4) * (twoA sixCol i).card := by
  native_decide

/-- The per-colour census on the `K₉` witness. -/
theorem card_twoFourSets_census_nineCol : ∀ i : Fin 8,
    (twoFourSets nineCol i).card = Nat.choose (classF nineCol i).card 2 + (9 - 4) * (twoA nineCol i).card := by
  native_decide

/-- The per-colour census on the `K₁₀` witness. -/
theorem card_twoFourSets_census_tenCol : ∀ i : Fin 9,
    (twoFourSets tenCol i).card = Nat.choose (classF tenCol i).card 2 + (10 - 4) * (twoA tenCol i).card := by
  native_decide

/-- The per-colour census on the `K₁₁` witness. -/
theorem card_twoFourSets_census_elevenCol : ∀ i : Fin 10,
    (twoFourSets elevenCol i).card = Nat.choose (classF elevenCol i).card 2 + (11 - 4) * (twoA elevenCol i).card := by
  native_decide

/-- **THE GLOBAL CENSUS ON THE `K₆` WITNESS**: all `15` tight four-sets, no two-edge path at all,
so the pair count alone accounts for them: `∑_i choose |E_i| 2 = 15`. -/
theorem fiveFourSets_census_sixCol :
    (fiveFourSets sixCol).card = ∑ i : Fin 5, Nat.choose (classF sixCol i).card 2
      + (6 - 4) * Paths sixCol := by native_decide

/-- The global census on the `K₉` witness. -/
theorem fiveFourSets_census_nineCol :
    (fiveFourSets nineCol).card = ∑ i : Fin 8, Nat.choose (classF nineCol i).card 2
      + (9 - 4) * Paths nineCol := by native_decide

/-- The global census on the `K₁₀` witness. -/
theorem fiveFourSets_census_tenCol :
    (fiveFourSets tenCol).card = ∑ i : Fin 9, Nat.choose (classF tenCol i).card 2
      + (10 - 4) * Paths tenCol := by native_decide

/-- The global census on the `K₁₁` witness. -/
theorem fiveFourSets_census_elevenCol :
    (fiveFourSets elevenCol).card = ∑ i : Fin 10, Nat.choose (classF elevenCol i).card 2
      + (11 - 4) * Paths elevenCol := by native_decide

/-- **TWO DISTINCT EDGES SHARE AT MOST ONE ENDPOINT.** -/
private theorem eq_common {n : ℕ} {e f : Sym2 (Verts n)} {he : OffDiag e} {hf : OffDiag f}
    (hef : e ≠ f) {v v' : Verts n} (hv : Sym2.Mem v e) (hv' : Sym2.Mem v f)
    (h2 : Sym2.Mem v' e) (h2' : Sym2.Mem v' f) : v = v' := by
  obtain ⟨a, hxe⟩ := Sym2.mem_iff_exists.mp hv
  obtain ⟨b, hyf⟩ := Sym2.mem_iff_exists.mp hv'
  have hne : a ≠ v := Ne.symm (he v a hxe)
  have hne' : b ≠ v := Ne.symm (hf v b hyf)
  have hab : a ≠ b := by
    intro h
    apply hef
    rw [hxe, hyf, h]
  rcases (mem_iff_eq hxe).mp h2 with h3 | h3
  · exact h3.symm
  · rcases (mem_iff_eq hyf).mp h2' with h4 | h4
    · exact h4.symm
    · exact (hab (h3.symm.trans h4)).elim

/-- **THE ORDERED PAIRS OF DISTINCT COLOUR-`i` EDGES WITH A COMMON ENDPOINT** — the *ordered*
version of `meetPairs c i`, counted twice over. -/
def adjEdgePairs {n k : ℕ} (c : Col n k) (i : Fin k) : Finset (Sym2 (Verts n) × Sym2 (Verts n)) :=
  (edgePairs (classF c i)).filter fun q => ∃ v : Verts n, v ∈ q.1 ∧ v ∈ q.2

theorem mem_adjEdgePairs {n k : ℕ} {c : Col n k} {i : Fin k} {q : Sym2 (Verts n) × Sym2 (Verts n)} :
    q ∈ adjEdgePairs c i ↔ q.1 ∈ classF c i ∧ q.2 ∈ classF c i ∧ q.1 ≠ q.2 ∧
      ∃ v, Sym2.Mem v q.1 ∧ Sym2.Mem v q.2 := by
  constructor
  · intro h
    have h' := Finset.mem_filter.mp h
    have hm := mem_edgePairs.mp h'.1
    obtain ⟨v, hv⟩ := h'.2
    exact ⟨hm.1, hm.2.1, hm.2.2, ⟨v, Sym2.mem_iff_mem.mp hv.1, Sym2.mem_iff_mem.mp hv.2⟩⟩
  · show (q.1 ∈ classF c i ∧ q.2 ∈ classF c i ∧ q.1 ≠ q.2 ∧
      ∃ v, Sym2.Mem v q.1 ∧ Sym2.Mem v q.2) → q ∈ adjEdgePairs c i
    rintro ⟨h1, h2, h3, v, hv1, hv2⟩
    exact Finset.mem_filter.mpr ⟨mem_edgePairs.mpr ⟨h1, h2, h3⟩,
      ⟨v, Sym2.mem_iff_mem.mpr hv1, Sym2.mem_iff_mem.mpr hv2⟩⟩

/-- **THE (VERTEX, ORDERED PAIR) DOUBLE COUNT**: `meetOrders c i` is the finset of triples
`(v, e, f)` of an endpoint `v` and two distinct colour-`i` edges through it. -/
def meetOrders {n k : ℕ} (c : Col n k) (i : Fin k) :
    Finset ((Verts n) × (Sym2 (Verts n) × Sym2 (Verts n))) :=
  ((Finset.univ : Finset (Verts n)).product (edgePairs (classF c i))).filter
    fun t => Sym2.Mem t.1 t.2.1 ∧ Sym2.Mem t.1 t.2.2

theorem mem_meetOrders {n k : ℕ} {c : Col n k} {i : Fin k}
    {t : (Verts n) × (Sym2 (Verts n) × Sym2 (Verts n))} :
    t ∈ meetOrders c i ↔ t.2.1 ∈ classF c i ∧ t.2.2 ∈ classF c i ∧ t.2.1 ≠ t.2.2 ∧
      Sym2.Mem t.1 t.2.1 ∧ Sym2.Mem t.1 t.2.2 := by
  rw [meetOrders, Finset.mem_filter]
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := Finset.mem_product.mp h.1
    obtain ⟨h3, h4, h5⟩ := mem_edgePairs.mp h2
    exact ⟨h3, h4, h5, h.2.1, h.2.2⟩
  · rintro ⟨h1, h2, h3, h4, h5⟩
    exact ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, mem_edgePairs.mpr ⟨h1, h2, h3⟩⟩, ⟨h4, h5⟩⟩

/-! ### §13  the ORDERED pair census: `Census.card_adjPairs` -/

/-- **A COLOUR-`i` EDGE THROUGH `v` IS AN IMAGE OF A COLOUR-`i` NEIGHBOUR OF `v`.** -/
private theorem mem_iEdgesAt_of_mem_classF {n k : ℕ} {c : Col n k} (i : Fin k) {v : Verts n}
    {e : Sym2 (Verts n)} (he : e ∈ classF c i) (hv : Sym2.Mem v e) :
    e ∈ iEdgesAt c i v := by
  obtain ⟨a, hxe⟩ := Sym2.mem_iff_exists.mp hv
  have hcl := mem_classIn.mp (show e ∈ classIn c i (Finset.univ : Finset (Verts n)) from he)
  have hne : v ≠ a := (mem_edgeFinset.mp hcl.1).2 v a hxe
  refine (mem_iEdgesAt i).mpr ⟨a, mem_nb.mpr ⟨Ne.symm hne, Finset.mem_univ a, hxe ▸ hcl.2⟩,
    hxe⟩

/-- **THE DOUBLE COUNT AT A VERTEX**: the number of ordered pairs of distinct colour-`i` edges
through `v` is `|nb| * (|nb| - 1)`, the number of ordered pairs of distinct members of `nb`. -/
theorem card_fiber_meetOrders {n k : ℕ} {c : Col n k} (hc : Admissible c) (i : Fin k)
    (w : Verts n) :
    ((meetOrders c i).filter fun t : (Verts n) × (Sym2 (Verts n) × Sym2 (Verts n)) =>
      (fun t => t.1) t = w).card
      = (nb c i w (Finset.univ : Finset (Verts n))).card
        * ((nb c i w (Finset.univ : Finset (Verts n))).card - 1) := by
  have hbij : ((meetOrders c i).filter fun t : (Verts n) × (Sym2 (Verts n) × Sym2 (Verts n)) =>
        (fun t => t.1) t = w).card = (edgePairs (iEdgesAt c i w)).card := by
    refine Finset.card_bij (fun t _ => t.2) ?_ ?_ ?_
    · intro t ht
      have ht' := Finset.mem_filter.mp ht
      have htw : t.1 = w := by simpa using ht'.2
      have h' := mem_meetOrders.mp ht'.1
      have h1 : t.2.1 ∈ classF c i := h'.1
      have h2 : t.2.2 ∈ classF c i := h'.2.1
      have h3 : t.2.1 ≠ t.2.2 := h'.2.2.1
      have h4 : Sym2.Mem t.1 t.2.1 := h'.2.2.2.1
      have h5 : Sym2.Mem t.1 t.2.2 := h'.2.2.2.2
      rw [htw] at h4 h5
      exact mem_edgePairs.mpr ⟨mem_iEdgesAt_of_mem_classF i h1 h4,
        mem_iEdgesAt_of_mem_classF i h2 h5, h3⟩
    · intro t ht t' ht' heq
      have h1 := mem_meetOrders.mp (Finset.mem_filter.mp ht).1
      have h2 := mem_meetOrders.mp (Finset.mem_filter.mp ht').1
      have htw : t.1 = w := by simpa using (Finset.mem_filter.mp ht).2
      have htw' : t'.1 = w := by simpa using (Finset.mem_filter.mp ht').2
      have h4 : Sym2.Mem t.1 t.2.1 := h1.2.2.2.1
      have h5 : Sym2.Mem t.1 t.2.2 := h1.2.2.2.2
      have h4' : Sym2.Mem t'.1 t'.2.1 := h2.2.2.2.1
      have h5' : Sym2.Mem t'.1 t'.2.2 := h2.2.2.2.2
      have heq' : t.2.1 = t'.2.1 := congrArg (fun p : Sym2 (Verts n) × Sym2 (Verts n) => p.1) heq
      have heq'' : t.2.2 = t'.2.2 := congrArg (fun p : Sym2 (Verts n) × Sym2 (Verts n) => p.2) heq
      have hne : t.2.1 ≠ t.2.2 := h1.2.2.1
      have hne' : t'.2.1 ≠ t'.2.2 := h2.2.2.1
      have heoff : OffDiag t.2.1 := by
        have hx := (mem_classIn.mp
          (show t.2.1 ∈ classIn c i (Finset.univ : Finset (Verts n)) from h1.1)).1
        rw [mem_edgeFinset] at hx
        exact hx.2
      have hfoff : OffDiag t.2.2 := by
        have hx := (mem_classIn.mp
          (show t.2.2 ∈ classIn c i (Finset.univ : Finset (Verts n)) from h1.2.1)).1
        rw [mem_edgeFinset] at hx
        exact hx.2
      exact Prod.ext (eq_common (he := heoff) (hf := hfoff) hne h4 h5 (heq'.symm ▸ h4')
        (heq''.symm ▸ h5')) heq
    · intro q hq
      have hq' := mem_edgePairs.mp hq
      have h1 : q.1 ∈ classF c i := iEdgesAt_subset_classF i w hq'.1
      have h2 : q.2 ∈ classF c i := iEdgesAt_subset_classF i w hq'.2.1
      refine ⟨(w, (q.1, q.2)),
        Finset.mem_filter.mpr ⟨mem_meetOrders.mpr ⟨h1, h2, hq'.2.2,
          mem_iEdgesAt_of_mem i hq'.1, mem_iEdgesAt_of_mem i hq'.2.1⟩, rfl⟩, rfl⟩
  rw [hbij, card_edgePairs, card_iEdgesAt i w]

/-- **THE DOUBLE COUNT: `|meetOrders c i| = ∑_v |nb c i v| * (|nb c i v| - 1)`.** -/
theorem card_meetOrders_eq_sum {n k : ℕ} {c : Col n k} (hc : Admissible c) (i : Fin k) :
    (meetOrders c i).card
      = ∑ w : Verts n, (nb c i w (Finset.univ : Finset (Verts n))).card
        * ((nb c i w (Finset.univ : Finset (Verts n))).card - 1) := by
  rw [Finset.card_eq_sum_card_fiberwise (s := meetOrders c i)
      (t := (Finset.univ : Finset (Verts n))) (f := fun t => t.1)]
  · exact Finset.sum_congr rfl fun w _ => card_fiber_meetOrders hc i w
  · intro t ht
    exact Finset.mem_univ _

/-- **THE DOUBLE COUNT AT A PATH CENTRE IS 2, AND IT IS 0 ELSEWHERE: `|meetOrders c i| =
2 * |twoA c i|`** — i.e. **THE NUMBER OF ORDERED PAIRS OF DISTINCT COLOUR-`i` EDGES WITH A COMMON
ENDPOINT IS TWICE THE NUMBER OF TWO-EDGE PATHS**, the `card_adjPairs` step of `Census.lean` §2*. -/
theorem card_meetOrders {n k : ℕ} {c : Col n k} (hc : Admissible c) (i : Fin k) :
    (meetOrders c i).card = 2 * (twoA c i).card := by
  have h1 : ∀ w : Verts n, (nb c i w (Finset.univ : Finset (Verts n))).card
      * ((nb c i w (Finset.univ : Finset (Verts n))).card - 1)
      = if w ∈ twoA c i then 2 else 0 := by
    intro w
    by_cases hw : w ∈ twoA c i
    · rw [if_pos hw]
      simp only [mem_twoA.mp hw]
    · rw [if_neg hw]
      have hle : (nb c i w (Finset.univ : Finset (Verts n))).card ≤ 2 :=
        nb_univ_card_le_two hc i w
      by_cases h2 : (nb c i w (Finset.univ : Finset (Verts n))).card = 2
      · exact (hw (mem_twoA.mpr h2)).elim
      · have hlt : (nb c i w (Finset.univ : Finset (Verts n))).card < 2 := by omega
        have hle' : (nb c i w (Finset.univ : Finset (Verts n))).card ≤ 1 :=
          Nat.le_of_lt_succ hlt
        rw [Nat.lt_succ_iff] at hlt
        have hz : (nb c i w (Finset.univ : Finset (Verts n))).card - 1 = 0 := by omega
        exact Nat.mul_eq_zero.mpr (Or.inr hz)
  rw [card_meetOrders_eq_sum hc i]
  calc ∑ w : Verts n, (nb c i w (Finset.univ : Finset (Verts n))).card
        * ((nb c i w (Finset.univ : Finset (Verts n))).card - 1)
      = ∑ w : Verts n, (if w ∈ twoA c i then 2 else 0) := by
          refine Finset.sum_congr rfl ?_
          intro w _
          exact h1 w
    _ = 2 * (twoA c i).card := by rw [← Finset.sum_filter]; simp <;> omega

/-- **THE BIJECTION `adjEdgePairs c i ≃ meetOrders c i`**: an ordered pair of distinct colour-`i`
edges with a common endpoint determines that endpoint uniquely, so forgetting the endpoint is a
bijection. -/
theorem card_adjEdgePairs {n k : ℕ} {c : Col n k} (hc : Admissible c) (i : Fin k) :
    (adjEdgePairs c i).card = (meetOrders c i).card := by
  refine Finset.card_bij (s := adjEdgePairs c i) (t := meetOrders c i)
    (fun q hq => (Classical.choose (((mem_adjEdgePairs (c := c) (i := i)).mp hq).2.2.2), q))
    (fun q hq => ?_)
    (fun q hq r hr heq => by
      exact congrArg (fun p : (Verts n) × (Sym2 (Verts n) × Sym2 (Verts n)) => p.2) heq)
    (fun t ht => ?_)
  · have h' := mem_adjEdgePairs.mp hq
    have hcommon := Classical.choose_spec ((mem_adjEdgePairs.mp hq).2.2.2)
    exact mem_meetOrders.mpr ⟨h'.1, h'.2.1, h'.2.2.1, hcommon.1, hcommon.2⟩
  · have h' := mem_meetOrders.mp ht
    have h1 : t.2.1 ∈ classF c i := h'.1
    have h2 : t.2.2 ∈ classF c i := h'.2.1
    have h3 : t.2.1 ≠ t.2.2 := h'.2.2.1
    have h4 : Sym2.Mem t.1 t.2.1 := h'.2.2.2.1
    have h5 : Sym2.Mem t.1 t.2.2 := h'.2.2.2.2
    have heoff : OffDiag t.2.1 := by
      have hx := (mem_classIn.mp
        (show t.2.1 ∈ classIn c i (Finset.univ : Finset (Verts n)) from h1)).1
      rw [mem_edgeFinset] at hx
      exact hx.2
    have hfoff : OffDiag t.2.2 := by
      have hx := (mem_classIn.mp
        (show t.2.2 ∈ classIn c i (Finset.univ : Finset (Verts n)) from h2)).1
      rw [mem_edgeFinset] at hx
      exact hx.2
    have hq' : t.2 ∈ adjEdgePairs c i := mem_adjEdgePairs.mpr ⟨h1, h2, h3, t.1, h4, h5⟩
    have hw := Classical.choose_spec ((mem_adjEdgePairs.mp hq').2.2.2)
    refine ⟨t.2, hq', ?_⟩
    have heq : Classical.choose ((mem_adjEdgePairs.mp hq').2.2.2) = t.1 :=
      eq_common (he := heoff) (hf := hfoff) h3 hw.1 hw.2 h4 h5
    rw [heq]

/-- **THE NUMBER OF ORDERED PAIRS OF DISTINCT COLOUR-`i` EDGES WITH A COMMON ENDPOINT IS TWICE THE
NUMBER OF TWO-EDGE PATHS** — the `card_adjPairs` step of `Census.lean` §2*. -/
theorem card_adjEdgePairs_eq {n k : ℕ} {c : Col n k} (hc : Admissible c) (i : Fin k) :
    (adjEdgePairs c i).card = 2 * (twoA c i).card :=
  (card_adjEdgePairs hc i).trans (card_meetOrders hc i)

/-- In the division-free form: `|adjEdgePairs c i| * 2 = 2 * (twoA c i).card * 2`. -/
theorem two_mul_card_adjEdgePairs {n k : ℕ} {c : Col n k} (hc : Admissible c) (i : Fin k) :
    2 * (adjEdgePairs c i).card = 4 * (twoA c i).card := by
  have h := card_adjEdgePairs_eq hc i
  omega

/-- **THE ORDERED-PAIR CENSUS, GLOBALLY: the ordered pairs of same-coloured edges with a common
endpoint number `2 * Paths c`** — twice the number of two-edge paths, because each path is counted
in the two orders of its edges. -/
theorem sum_card_adjEdgePairs {n k : ℕ} {c : Col n k} (hc : Admissible c) :
    ∑ i : Fin k, (adjEdgePairs c i).card = 2 * Paths c := by
  calc ∑ i : Fin k, (adjEdgePairs c i).card = ∑ i : Fin k, 2 * (twoA c i).card := by
        exact Finset.sum_congr rfl fun i _ => card_adjEdgePairs_eq hc i
    _ = 2 * ∑ i : Fin k, (twoA c i).card := by rw [Finset.mul_sum]
    _ = 2 * Paths c := rfl

/-! ### the ordered count is machine-checked on the four constructions of `Tables.lean` -/

/-- The ordered-pair count on the `K₆` witness: `sixCol` is a 1-factorisation, so it has no
two-edge path and no adjacent ordered pair. -/
theorem sum_card_adjEdgePairs_sixCol : ∑ i : Fin 5, (adjEdgePairs sixCol i).card
    = 2 * Paths sixCol := by native_decide

/-- The ordered-pair count on the `K₉` witness. -/
theorem sum_card_adjEdgePairs_nineCol : ∑ i : Fin 8, (adjEdgePairs nineCol i).card
    = 2 * Paths nineCol := by native_decide

/-- The ordered-pair count on the `K₁₀` witness. -/
theorem sum_card_adjEdgePairs_tenCol : ∑ i : Fin 9, (adjEdgePairs tenCol i).card
    = 2 * Paths tenCol := by native_decide

/-- The ordered-pair count on the `K₁₁` witness. -/
theorem sum_card_adjEdgePairs_elevenCol : ∑ i : Fin 10, (adjEdgePairs elevenCol i).card
    = 2 * Paths elevenCol := by native_decide

end
end JSP140
