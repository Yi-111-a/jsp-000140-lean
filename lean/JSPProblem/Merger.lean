import JSPProblem.Paths

/-!
# JSP-000140 — round 70: THE MERGER BUDGET

Rounds 14–69 attacked the missing half of the catalog answer `f(n,4,5) = 5n/6 + o(n)` from
below (`Cherry`, `Counting`, `Paths`, `Rigidity`: the sharp counting bound `5(n-1) ≤ 6k` and the
Steiner-triple-system structure of the extremal case), from above (`Ghost`, `BlockCol`, `Tables`,
`Window`: explicit colourings, the anchor `EG 12 = 11`) and from the middle (`Pad`, `Grow`: the
six-step growth lemma as a finite, decidable construction problem).  Every one of those rounds
counts *vertices* (`Paths`, `Isolated`, `Defect`) or *edges* (`|E_i|`), and every one of them
throws away the same piece of information: **how many four-vertex sets each colour "merges" in.**

This round counts four-vertex sets instead.

## The merge count of a four-set

A `K₄` has six edges.  Admissibility says it spans at least five colours, so **at most one colour
appears twice** in it.  The number of colours lost in `S` is

    μ(S) = #{ i : exactly two edges of S have colour i }  =  6 - |colours in S|  ≤  1.

`Merger.sum_eq_six` (`∑_i [t_i(S) ≥ 1] = 6`), `Merger.merge_eq` (`μ(S) = 6 - |colours in S|`) and
`Merger.merge_le_one` (`μ(S) ≤ 1`) make this exact, and `Merger.budget` sums it: **the total number
of `K₄`s in which some colour is doubled is at most `C(n,4)`**.

## The exact identity behind it (the merger budget)

Fix a colour `i` and let `t_i(S)` be the number of colour-`i` edges of `S`.  Counting the pairs
`(e, S)` with `e` a colour-`i` edge contained in the four-set `S` two ways — by `e` (each edge lies
in exactly `C(n-2,2)` four-sets) and by `S` (`t_i(S) = [t_i ≥ 1] + [t_i = 2]`) — gives

    **card (Doubles c i) = |E_i| · C(n-2,2) - C(n,4) + card (Misses c i)**        (`Merger.doubles_eq`)

where `Doubles c i` are the four-sets doubling colour `i` and `Misses c i` the four-sets missing it
altogether.  This is *new information about colour classes*: the old budget `3|E_i| ≤ 2n`
(`Counting.three_mul_classIn_le`) bounds `|E_i|` from above by counting vertices, the new identity
determines the four-set profile of `E_i` from `|E_i|` **exactly**.

Three consequences.

1. **`Merger.spread` — the SPREAD CONDITION.**  Summing `Merger.doubles_eq` over the colours and
   using `Merger.budget`:

        ∑_i Finset.card (Misses c i)  ≤  (k - 5) · C(n,4).

   *In an admissible `k`-colouring of `K_n` the four-vertex sets that avoid a given colour
   altogether are, summed over all colours, at most a `1 - 5/k` fraction of all four-sets: on
   average every colour class must appear in at least a `5/k` fraction of them.*  This is a
   quantitative **no hiding place** condition on a construction: a colour class concentrated on a
   few vertices, or one whose edges fall into the same four-sets, is rejected by it.

2. **`Merger.empty4_eq_empty` — for `k ≤ 5` every colour meets every four-set.**  In particular
   `Merger.doubles_eq` becomes `card (Doubles c i) = |E_i|·C(n-2,2) - C(n,4)`, i.e. **every colour
   class of an admissible `k ≤ 5` colouring has at least `C(n,4)/C(n-2,2) = n(n-1)/12` edges**
   (`Merger.classIn_card_ge`).  Concretely:

   * `Merger.six_classIn_card_ge` : `3 ≤ |E_i|` for every colour of an admissible `Col 6 5` — since
     the five classes partition the fifteen edges of `K₆` and each has at least three, each has
     **exactly** three, so `Tables.sixCol` is not an accident of the search;
   * `Merger.five_classIn_card_ge` : `2 ≤ |E_i|` for every colour of an admissible `Col 5 5`, and
     the five classes partition the ten edges of `K₅`, so each has exactly two.

   These are the first statements of the development about *all* admissible colourings at a tight
   order (`EG 6 = 5`, `EG 5 = 5` were verified numerically in rounds 30/38), rather than about one
   witness.

## Next: the missing half of the rigidity

With `|E_i| = 3` at `n = 6, k = 5` the identity forces `card (Doubles c i) = 3`, whereas a colour
class consisting of a two-edge path `a - v - b` plus one further edge `e` produces **five** doubled
four-sets: the three `K₄`s on `{a,v,b} ∪ {x}` (`x` outside the path) and the two `K₄`s on
`V(a,v) ∪ V(e)` and `V(v,b) ∪ V(e)`.  The budget `≤ 3` would be violated, so every admissible
5-colouring of `K₆` is a **1-factorisation** — no two-edge path at all.  The bookkeeping is local
(each of those five four-sets must *contain* colour `i`, and no third colour-`i` edge can sit inside
one, by `ColorClass.three_of_classIn_fourSet`); it is the declared next lemma of round 71.
-/

set_option maxRecDepth 100000

namespace JSP140

variable {n k : ℕ}

/-! ### §1  Counting subsets of a finset -/

/-- The `r`-element subsets of `s`. -/
def subsetsOf {α : Type*} (r : ℕ) (s : Finset α) : Finset (Finset α) :=
  s.powerset.filter (fun T => T.card = r)

@[simp] theorem mem_subsetsOf {α : Type*} {r : ℕ} {s : Finset α} {T : Finset α} :
    T ∈ subsetsOf r s ↔ T ⊆ s ∧ T.card = r := by
  simp [subsetsOf]

private lemma subsetsOf_zero {α : Type*} [DecidableEq α] (s : Finset α) :
    subsetsOf 0 s = ({∅} : Finset (Finset α)) := by
  classical
  ext T
  constructor
  · intro h
    have h2 := (mem_subsetsOf.mp h).2
    have hT : T = ∅ := Finset.card_eq_zero.mp h2
    simp [hT]
  · intro h
    have hT : T = ∅ := Finset.mem_singleton.mp h
    subst hT
    exact mem_subsetsOf.mpr ⟨fun a ha => absurd ha (by simp), rfl⟩

/-- The split of the `(r+1)`-element subsets of `insert a s` into those avoiding `a` and those
containing it. -/
private lemma subsetsOf_insert {α : Type*} [DecidableEq α] (r : ℕ) (a : α) (s : Finset α)
    (ha : a ∉ s) :
    subsetsOf (r + 1) (insert a s)
      = (subsetsOf (r + 1) s) ∪ ((subsetsOf r s).image (fun T => insert a T)) := by
  classical
  ext T
  constructor
  · intro hT
    obtain ⟨h1, h2⟩ := mem_subsetsOf.mp hT
    rw [Finset.mem_union, Finset.mem_image]
    by_cases haT : a ∈ T
    · refine Or.inr ⟨T.erase a, ?_, Finset.insert_erase haT⟩
      · refine mem_subsetsOf.mpr ⟨?_, ?_⟩
        · intro b hb
          have hb2 : b ≠ a := (Finset.mem_erase.mp hb).1
          have hb3 : b ∈ T := (Finset.mem_erase.mp hb).2
          rcases Finset.mem_insert.mp (h1 hb3) with hcon | hcon
          · exact absurd hcon hb2
          · exact hcon
        · have hcard := Finset.card_erase_of_mem haT
          omega
    · refine Or.inl (mem_subsetsOf.mpr ⟨?_, h2⟩)
      · intro b hb
        exact (Finset.mem_insert.mp (h1 hb)).resolve_left (fun h => haT (h ▸ hb))
  · intro hT
    rcases Finset.mem_union.mp hT with hT | hT
    · obtain ⟨h1, h2⟩ := mem_subsetsOf.mp hT
      exact mem_subsetsOf.mpr ⟨fun b hb => Finset.mem_insert_of_mem (h1 hb), h2⟩
    · obtain ⟨U, hU, hUT⟩ := Finset.mem_image.mp hT
      have hTU : T = insert a U := by rw [← hUT]
      rw [hTU]
      refine mem_subsetsOf.mpr ⟨?_, ?_⟩
      · intro b hb
        rcases Finset.mem_insert.mp hb with hcon | hb
        · rw [hcon]; exact Finset.mem_insert_self a s
        · exact Finset.mem_insert_of_mem ((mem_subsetsOf.mp hU).1 hb)
      · have haU : a ∉ U := fun hcon => ha ((mem_subsetsOf.mp hU).1 hcon)
        have hUc : U.card = r := (mem_subsetsOf.mp hU).2
        rw [Finset.card_insert_of_notMem haU]
        omega

private lemma card_subsetsOf_nil {α : Type*} [DecidableEq α] (r : ℕ) :
    (subsetsOf r (∅ : Finset α)).card = Nat.choose 0 r := by
  by_cases hr : r = 0
  · rw [hr, subsetsOf_zero, Finset.card_singleton]
    simp
  · have hpos : 0 < r := by omega
    have hne : (subsetsOf r (∅ : Finset α)).card = 0 := by
      apply Finset.card_eq_zero.mpr
      refine Finset.eq_empty_iff_forall_notMem.mpr ?_
      intro T hT
      obtain ⟨h1, h2⟩ := mem_subsetsOf.mp hT
      have hT' : T = (∅ : Finset α) :=
        Finset.eq_empty_iff_forall_notMem.mpr (fun z hz => absurd (h1 hz) (by simp))
      rw [hT', Finset.card_empty] at h2
      omega
    rw [hne, Nat.choose_eq_zero_of_lt hpos]

private lemma insert_cancel [DecidableEq α] (a : α) {s t : Finset α} (has : a ∉ s) (hat : a ∉ t)
    (h : insert a s = insert a t) : s = t := by
  ext z
  by_cases hz : z = a
  · simp [hz, has, hat]
  · calc z ∈ s ↔ z ∈ insert a s := by simp only [Finset.mem_insert, hz, false_or]
        _ ↔ z ∈ insert a t := by rw [h]
        _ ↔ z ∈ t := by simp only [Finset.mem_insert, hz, false_or]

/-- **The number of `r`-element subsets of an `m`-element finset is `C(m, r)`.** -/
theorem card_subsetsOf {α : Type*} [DecidableEq α] (r : ℕ) (s : Finset α) :
    (subsetsOf r s).card = Nat.choose s.card r := by
  classical
  induction s using Finset.induction_on generalizing r with
  | empty =>
      rw [card_subsetsOf_nil, Finset.card_empty]
  | @insert a s ha ih =>
      rcases r with _ | r
      · rw [subsetsOf_zero, Finset.card_singleton, Nat.choose_zero_right]
      · have hdec := subsetsOf_insert r a s ha
        have hdisj : Disjoint (subsetsOf (r + 1) s)
            ((subsetsOf r s).image (fun T => insert a T)) := by
          refine Finset.disjoint_left.mpr fun T h1 h2 => ?_
          rw [mem_subsetsOf] at h1
          rw [Finset.mem_image] at h2
          obtain ⟨U, -, rfl⟩ := h2
          exact ha (h1.1 (Finset.mem_insert_self a U))
        have hinj : Set.InjOn (fun T => insert a T) (↑(subsetsOf r s) : Set (Finset α)) := by
          intro T₁ hT₁ T₂ hT₂ heq
          exact insert_cancel a (fun hc => ha ((mem_subsetsOf.mp hT₁).1 hc))
            (fun hc => ha ((mem_subsetsOf.mp hT₂).1 hc)) heq
        have hcard : ((subsetsOf r s).image (fun T => insert a T)).card
            = (subsetsOf r s).card := Finset.card_image_iff.mpr hinj
        have hunion : (subsetsOf (r + 1) (insert a s)).card
            = (subsetsOf (r + 1) s).card + (subsetsOf r s).card := by
          calc (subsetsOf (r + 1) (insert a s)).card
              = ((subsetsOf (r + 1) s) ∪ ((subsetsOf r s).image (fun T => insert a T))).card := by
                rw [hdec]
            _ = (subsetsOf (r + 1) s).card
                + ((subsetsOf r s).image (fun T => insert a T)).card :=
              Finset.card_union_of_disjoint hdisj
            _ = (subsetsOf (r + 1) s).card + (subsetsOf r s).card := by rw [hcard]
        rw [hunion, ih, ih, Finset.card_insert_of_notMem ha, Nat.choose_succ_succ', Nat.add_comm]

/-! ### §2  The four-vertex sets -/

/-- The four-vertex sets of `K_n`. -/
def fsets4 (n : ℕ) : Finset (Finset (Verts n)) := subsetsOf 4 (Finset.univ : Finset (Verts n))

@[simp] theorem mem_fsets4 {n : ℕ} {S : Finset (Verts n)} :
    S ∈ fsets4 n ↔ S.card = 4 := by
  rw [fsets4, mem_subsetsOf]
  simp

/-- **There are `C(n,4)` four-vertex sets.** -/
theorem card_fsets4 (n : ℕ) : (fsets4 n).card = Nat.choose n 4 := by
  rw [fsets4, card_subsetsOf, Finset.card_univ, Fintype.card_fin]

/-- The two endpoints of a non-loop edge. -/
theorem exists_ends {n : ℕ} {e : Sym2 (Verts n)} (he : OffDiag e) :
    ∃ x y : Verts n, e = s(x, y) ∧ x ≠ y := by
  obtain ⟨x, y, hxy⟩ : ∃ x y : Verts n, e = s(x, y) := Sym2.exists.mp ⟨e, rfl⟩
  exact ⟨x, y, hxy, fun hcon => he x y hxy hcon⟩

/-- The four-vertex sets containing the edge `e`. -/
def Quads {n : ℕ} (e : Sym2 (Verts n)) : Finset (Finset (Verts n)) :=
  (fsets4 n).filter (fun S => e ∈ edgeFinset S)

@[simp] theorem mem_Quads {n : ℕ} {e : Sym2 (Verts n)} {S : Finset (Verts n)} :
    S ∈ Quads e ↔ S.card = 4 ∧ e ∈ edgeFinset S := by
  simp [Quads]

/-- **An edge of `K_n` lies in exactly `C(n-2,2)` four-vertex sets.** -/
theorem card_Quads {n : ℕ} (e : Sym2 (Verts n)) (he : OffDiag e) :
    (Quads e).card = Nat.choose (n - 2) 2 := by
  classical
  obtain ⟨x, y, hxy, hne⟩ := exists_ends he
  subst hxy
  set R := (Finset.univ : Finset (Verts n)) \ insert x (insert y ∅) with hRdef
  have hxR : x ∉ R := by
    rw [hRdef]
    simp
  have hyR : y ∉ R := by
    rw [hRdef]
    simp [hne]
  have hcardR : R.card = n - 2 := by
    have hsub : (insert x (insert y ∅) : Finset (Verts n)) ⊆ (Finset.univ : Finset (Verts n)) := by
      simp
    have htwo : (insert x (insert y ∅) : Finset (Verts n)).card = 2 := by
      rw [Finset.card_insert_of_notMem (by simp [hne]), Finset.card_insert_of_notMem (by simp)]
      simp only [Finset.card_empty]
    rw [hRdef, Finset.card_sdiff_of_subset hsub, htwo, Finset.card_univ, Fintype.card_fin]
  have hxU : x ∈ (Finset.univ : Finset (Verts n)) := Finset.mem_univ x
  have hinj : ∀ s t : Finset (Verts n), x ∉ s → x ∉ t → insert x s = insert x t → s = t := by
    intro s t hxs hxt h
    apply insert_cancel x hxs hxt h
  have hbij : (subsetsOf 2 R).card = (Quads (s(x, y))).card := by
    refine Finset.card_bij (fun T (_hT : T ∈ subsetsOf 2 R) => insert x (insert y T)) ?_ ?_ ?_
    · intro T hT
      have h1 := (mem_subsetsOf.mp hT).1
      have h2 := (mem_subsetsOf.mp hT).2
      have hyT : y ∉ T := fun hc => hyR (h1 hc)
      have hxT : x ∉ T := fun hc => hxR (h1 hc)
      have hyU : y ∈ (Finset.univ : Finset (Verts n)) := Finset.mem_univ y
      have hxT' : x ∉ insert y T := by
        intro hc
        rcases Finset.mem_insert.mp hc with hcon | hcon
        · exact hne hcon
        · exact hxT hcon
      refine mem_Quads.mpr ⟨?_, ?_⟩
      · rw [Finset.card_insert_of_notMem hxT', Finset.card_insert_of_notMem hyT]
        omega
      · exact mem_edgeFinset_mk (Finset.mem_insert_self x _)
          (Finset.mem_insert_of_mem (Finset.mem_insert_self y T)) hne
    · intro T₁ hT₁ T₂ hT₂ heq
      have nxT₁ : x ∉ insert y T₁ := by
        intro hc
        rcases Finset.mem_insert.mp hc with hcon | hcon
        · exact hne hcon
        · exact hxR ((mem_subsetsOf.mp hT₁).1 hcon)
      have nxT₂ : x ∉ insert y T₂ := by
        intro hc
        rcases Finset.mem_insert.mp hc with hcon | hcon
        · exact hne hcon
        · exact hxR ((mem_subsetsOf.mp hT₂).1 hcon)
      have hxy : insert y T₁ = insert y T₂ := insert_cancel x nxT₁ nxT₂ heq
      have hxy' : T₁.erase y = T₂.erase y := by
        have hh := congrArg (fun s : Finset (Verts n) => s.erase y) hxy
        simpa only [Finset.erase_insert_eq_erase, Finset.erase_insert_eq_erase] using hh
      have nyT₁ : y ∉ T₁ := fun hc => hyR ((mem_subsetsOf.mp hT₁).1 hc)
      have nyT₂ : y ∉ T₂ := fun hc => hyR ((mem_subsetsOf.mp hT₂).1 hc)
      calc T₁ = T₁.erase y := (Finset.erase_eq_of_notMem nyT₁).symm
        _ = T₂.erase y := hxy'
        _ = T₂ := Finset.erase_eq_of_notMem nyT₂
    · intro S hS
      rw [mem_Quads] at hS
      obtain ⟨hS4, hSe⟩ := hS
      obtain ⟨hxS, hyS⟩ := Finset.mk_mem_sym2_iff.mp (mem_edgeFinset.mp hSe).1
      have hyS' : y ∈ S.erase x := Finset.mem_erase.mpr ⟨hne.symm, hyS⟩
      have hsub : (S.erase x).erase y ⊆ R := by
        intro z hz
        refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ z, ?_⟩
        intro hz2
        have hzx : z ≠ x := (Finset.mem_erase.mp (Finset.mem_erase.mp hz).2).1
        have hzy : z ≠ y := (Finset.mem_erase.mp hz).1
        have hzS : z ∈ S := (Finset.mem_erase.mp (Finset.mem_erase.mp hz).2).2
        rcases Finset.mem_insert.mp hz2 with hcon | hcon
        · exact hzx hcon
        · rcases Finset.mem_insert.mp hcon with hcon' | hcon'
          · exact hzy hcon'
          · exact absurd hcon' (by simp)
      have hcard : ((S.erase x).erase y).card = 2 := by
        rw [Finset.card_erase_of_mem hyS', Finset.card_erase_of_mem hxS]
        omega
      refine ⟨(S.erase x).erase y, mem_subsetsOf.mpr ⟨hsub, hcard⟩, ?_⟩
      rw [Finset.insert_erase hyS', Finset.insert_erase hxS]
  rw [← hbij, card_subsetsOf, hcardR]

/-! ### §3  The merge count of a four-set -/

/-- The number of colours **lost** in the four-set `S`: one for every colour that occurs twice in
`S`.  Admissibility makes this at most `1`. -/
def Merge {n k : ℕ} (c : Col n k) (S : Finset (Verts n)) : ℕ :=
  ∑ i : Fin k, if (classIn c i S).card = 2 then 1 else 0

/-- The four-sets in which the colour `i` occurs **twice**. -/
def Doubles {n k : ℕ} (c : Col n k) (i : Fin k) : Finset (Finset (Verts n)) :=
  (fsets4 n).filter (fun S => (classIn c i S).card = 2)

@[simp] theorem mem_Doubles {n k : ℕ} {c : Col n k} {i : Fin k} {S : Finset (Verts n)} :
    S ∈ Doubles c i ↔ S.card = 4 ∧ (classIn c i S).card = 2 := by
  simp [Doubles]

/-- The four-sets **missing** the colour `i` altogether. -/
def Misses {n k : ℕ} (c : Col n k) (i : Fin k) : Finset (Finset (Verts n)) :=
  (fsets4 n).filter (fun S => (classIn c i S).card = 0)

@[simp] theorem mem_Misses {n k : ℕ} {c : Col n k} {i : Fin k} {S : Finset (Verts n)} :
    S ∈ Misses c i ↔ S.card = 4 ∧ (classIn c i S).card = 0 := by
  simp [Misses]

/-- The indicator sum of a predicate is the card of the corresponding filter. -/
private lemma sum_ite_card {α : Type*} [DecidableEq α] (s : Finset α) (p : α → Prop)
    [DecidablePred p] : (∑ x ∈ s, (if p x then 1 else 0)) = (s.filter p).card := by
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]

/-- **The six edges of a `K₄` are split among the colours.** -/
theorem sum_eq_six {n k : ℕ} {c : Col n k} {S : Finset (Verts n)} (hS : S.card = 4) :
    (∑ i : Fin k, (classIn c i S).card) = 6 :=
  sum_card_classIn c S ▸ card_edgeFinset_four hS

/-- The colours occurring in `S` are exactly those colours whose class in `S` is non-empty. -/
theorem colorsOn_eq_filter {n k : ℕ} (c : Col n k) (S : Finset (Verts n)) :
    colorsOn c S = (Finset.univ : Finset (Fin k)).filter
      (fun i => 0 < (classIn c i S).card) := by
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, colorsOn, Finset.mem_image]
  constructor
  · rintro ⟨e, he, hce⟩
    exact Finset.card_pos.mpr ⟨e, Finset.mem_filter.mpr ⟨he, hce⟩⟩
  · intro h
    obtain ⟨e, he⟩ := Finset.card_pos.mp h
    exact ⟨e, (Finset.mem_filter.mp he).1, (Finset.mem_filter.mp he).2⟩

/-- **The number of colours in `S` is the number of non-empty colour classes in `S`.** -/
theorem card_colorsOn_eq_count {n k : ℕ} (c : Col n k) (S : Finset (Verts n)) :
    (colorsOn c S).card = ∑ i : Fin k, if (classIn c i S).card = 0 then 0 else 1 := by
  have hkey : ∀ i : Fin k, (classIn c i S).card ≠ 0 ↔ 0 < (classIn c i S).card := by
    intro i
    constructor
    · exact fun h => Nat.pos_of_ne_zero h
    · exact fun h => Nat.ne_of_gt h
  rw [colorsOn_eq_filter, ← sum_ite_card]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : (classIn c i S).card = 0
  · have hn : ¬ (0 < (classIn c i S).card) := by rw [h]; exact Nat.lt_irrefl _
    rw [if_neg hn, if_pos h]
  · rw [if_pos ((hkey i).mp h), if_neg h]

/-- **THE MERGE IDENTITY.**  In an admissible colouring, a four-set loses exactly one colour for
every colour that occurs twice in it, so `|colours in S| + μ(S) = 6` with `μ(S) ≤ 1`. -/
theorem merge_eq {n k : ℕ} {c : Col n k} (hc : Admissible c) {S : Finset (Verts n)}
    (hS : S.card = 4) : (colorsOn c S).card + Merge c S = 6 := by
  have hkey : ∀ i : Fin k, (classIn c i S).card
      = (if (classIn c i S).card = 0 then (0 : ℕ) else 1)
        + (if (classIn c i S).card = 2 then 1 else 0) := by
    intro i
    have h := classIn_card_le_two hc i S hS
    by_cases h0 : (classIn c i S).card = 0
    · have h2 : (classIn c i S).card ≠ 2 := by omega
      rw [if_pos h0, if_neg h2, h0]
    · by_cases h2 : (classIn c i S).card = 2
      · rw [if_neg h0, if_pos h2, h2]
      · have hone : (classIn c i S).card = 1 := by omega
        rw [hone]
        rw [if_neg (by simp), if_neg (by simp)]
  calc (colorsOn c S).card + Merge c S
      = (∑ i : Fin k, (if (classIn c i S).card = 0 then 0 else 1))
        + (∑ i : Fin k, (if (classIn c i S).card = 2 then 1 else 0)) := by
          rw [card_colorsOn_eq_count, Merge]
      _ = ∑ i : Fin k, (classIn c i S).card := by
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun i _ => (hkey i).symm
      _ = 6 := sum_eq_six hS

/-- **A `K₄` loses at most one colour.** -/
theorem merge_le_one {n k : ℕ} {c : Col n k} (hc : Admissible c) {S : Finset (Verts n)}
    (hS : S.card = 4) : Merge c S ≤ 1 := by
  have h := hc S hS
  have hm := merge_eq hc hS
  omega

/-- The `Doubles` finset is counted by the merge indicator. -/
theorem merge_eq_sum {n k : ℕ} {c : Col n k} (i : Fin k) :
    (Doubles c i).card = ∑ S ∈ fsets4 n, (if (classIn c i S).card = 2 then 1 else 0) := by
  have hD : Doubles c i = (fsets4 n).filter (fun S => (classIn c i S).card = 2) := rfl
  rw [hD, ← sum_ite_card]

/-- **THE MERGER BUDGET.**  The number of `K₄`s in which some colour is doubled is at most
`C(n,4)`: the doubling sets of two distinct colours are disjoint. -/
theorem budget {n k : ℕ} {c : Col n k} (hc : Admissible c) :
    (∑ i : Fin k, (Doubles c i).card) ≤ Finset.card (fsets4 n) := by
  calc (∑ i : Fin k, (Doubles c i).card)
      = ∑ i : Fin k, ∑ S ∈ fsets4 n, (if (classIn c i S).card = 2 then 1 else 0) := by
        refine Finset.sum_congr rfl fun i _ => merge_eq_sum (c := c) i
      _ = ∑ S ∈ fsets4 n, Merge c S := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun S _ => ?_
        rfl
      _ ≤ ∑ S ∈ fsets4 n, 1 := by
        refine Finset.sum_le_sum fun S hS => ?_
        exact merge_le_one hc (mem_fsets4.mp hS)
      _ = Finset.card (fsets4 n) := (Finset.card_eq_sum_ones _).symm

/-! ### §4  The exact identity: counting `(edge, four-set)` pairs -/

/-- The colour-`i` edges inside `S` are the colour-`i` edges of `K_n` which lie in `S`. -/
theorem classIn_eq_filter {n k : ℕ} {c : Col n k} (i : Fin k) (S : Finset (Verts n)) :
    classIn c i S = (classIn c i (Finset.univ : Finset (Verts n))).filter
      (fun e => e ∈ edgeFinset S) := by
  ext e
  constructor
  · intro he
    rw [mem_classIn] at he
    rw [Finset.mem_filter, mem_classIn]
    exact ⟨⟨edgeFinset_mono (Finset.subset_univ S) he.1, he.2⟩, he.1⟩
  · intro he
    rw [Finset.mem_filter, mem_classIn] at he
    rw [mem_classIn]
    exact ⟨he.2, he.1.2⟩

/-- **THE INCIDENCE IDENTITY.**  Counting the pairs `(e, S)` with `e` a colour-`i` edge of the
four-set `S` by `e` gives `|E_i| · C(n-2,2)`: every edge lies in exactly `C(n-2,2)` four-sets. -/
theorem incidence {n k : ℕ} {c : Col n k} (i : Fin k) :
    (∑ S ∈ fsets4 n, (classIn c i S).card)
      = Finset.card (classIn c i (Finset.univ : Finset (Verts n))) * Nat.choose (n - 2) 2 := by
  set E := classIn c i (Finset.univ : Finset (Verts n)) with hE
  calc (∑ S ∈ fsets4 n, (classIn c i S).card)
      = ∑ S ∈ fsets4 n, ∑ e ∈ classIn c i S, (1 : ℕ) := by
        refine Finset.sum_congr rfl fun S _ => Finset.card_eq_sum_ones _
      _ = ∑ S ∈ fsets4 n, ∑ e ∈ E, (if e ∈ edgeFinset S then 1 else 0) := by
        refine Finset.sum_congr rfl fun S hS => ?_
        rw [classIn_eq_filter i S]
        exact Finset.sum_filter (fun e' => e' ∈ edgeFinset S) (fun _ => (1 : ℕ))
      _ = ∑ e ∈ E, ∑ S ∈ fsets4 n, (if e ∈ edgeFinset S then 1 else 0) := by
        exact Finset.sum_comm
      _ = ∑ e ∈ E, (Quads e).card := by
        refine Finset.sum_congr rfl fun e _ => ?_
        rw [Quads]
        exact (Finset.sum_filter (s := fsets4 n) (fun S => e ∈ edgeFinset S)
          (fun _ => (1 : ℕ))).symm.trans
          ((Finset.card_eq_sum_ones ((fsets4 n).filter (fun S => e ∈ edgeFinset S))).symm)
      _ = Finset.card (classIn c i (Finset.univ : Finset (Verts n))) * Nat.choose (n - 2) 2 := by
        have key : ∀ e ∈ classIn c i (Finset.univ : Finset (Verts n)),
            (Quads e).card = Nat.choose (n - 2) 2 := by
          intro e he
          exact card_Quads e (mem_edgeFinset.mp (mem_classIn.mp he).1).2
        have hA : (∑ e ∈ classIn c i (Finset.univ : Finset (Verts n)), (Quads e).card)
            = ∑ _e ∈ classIn c i (Finset.univ : Finset (Verts n)), Nat.choose (n - 2) 2 :=
          Finset.sum_congr rfl fun e he => key e he
        have hB : (∑ _e ∈ classIn c i (Finset.univ : Finset (Verts n)), Nat.choose (n - 2) 2)
            = Finset.card (classIn c i (Finset.univ : Finset (Verts n))) * Nat.choose (n - 2) 2 := by
          rw [Finset.sum_const, nsmul_eq_mul, Nat.cast_id, Nat.mul_comm]
        exact hA.trans hB

/-- **THE MERGE SPLIT.**  For one colour, the four-sets fall into three classes -- those in which it
occurs once, twice, and not at all -- and the number of colour-`i` edges over all four-sets is the
sum of these three counts. -/
theorem merge_split {n k : ℕ} {c : Col n k} (hc : Admissible c) (i : Fin k) :
    (∑ S ∈ fsets4 n, (classIn c i S).card)
      = (Finset.card (fsets4 n) - (Misses c i).card) + (Doubles c i).card := by
  set f0 : Finset (Verts n) → ℕ :=
    fun S => if (classIn c i S).card = 0 then 0 else 1 with hf0
  set f2 : Finset (Verts n) → ℕ :=
    fun S => if (classIn c i S).card = 2 then 1 else 0 with hf2
  set fne : Finset (Verts n) → ℕ :=
    fun S => if (classIn c i S).card ≠ 0 then 1 else 0 with hfne
  set fsum : Finset (Verts n) → ℕ := fun S => f0 S + f2 S with hfsum
  have hsplit : ∀ S : Finset (Verts n), S.card = 4 →
      (classIn c i S).card = fsum S := by
    intro S hS
    have h := classIn_card_le_two hc i S hS
    simp only [hfsum, hf0, hf2]
    by_cases h0 : (classIn c i S).card = 0
    · have h2 : (classIn c i S).card ≠ 2 := by omega
      rw [h0]
      simp
    · by_cases h2 : (classIn c i S).card = 2
      · rw [h2]
        simp
      · have hone : (classIn c i S).card = 1 := by omega
        rw [hone]
        simp
  have hleft : Finset.sum (fsets4 n) f0
      = Finset.card (fsets4 n) - (Misses c i).card := by
    have h1 : Finset.sum (fsets4 n) f0 = Finset.sum (fsets4 n) fne := by
      refine Finset.sum_congr rfl fun S _ => ?_
      by_cases h : (classIn c i S).card = 0 <;> simp [h, hf0, hfne]
    have h2 : Finset.sum (fsets4 n) fne
        = ((fsets4 n).filter (fun S => (classIn c i S).card ≠ 0)).card := by
      have hA : Finset.sum (fsets4 n) fne
          = Finset.sum ((fsets4 n).filter (fun S => (classIn c i S).card ≠ 0))
              (fun _ => (1 : ℕ)) := by
        simp only [hfne]
        exact (Finset.sum_filter (s := fsets4 n) (fun S => (classIn c i S).card ≠ 0)
          (fun _ => (1 : ℕ))).symm
      exact hA.trans ((Finset.card_eq_sum_ones _).symm)
    have h3 : (fsets4 n).filter (fun S => (classIn c i S).card ≠ 0)
        = fsets4 n \ Misses c i := by
      ext S
      rw [Finset.mem_filter, Finset.mem_sdiff]
      constructor
      · rintro ⟨h, hne⟩
        refine ⟨h, ?_⟩
        intro hM
        apply hne
        have hM' : S ∈ Misses c i := hM
        rw [mem_Misses] at hM'
        exact hM'.2
      · rintro ⟨h, hM⟩
        refine ⟨h, ?_⟩
        intro hc
        apply hM
        rw [Misses, Finset.mem_filter]
        exact ⟨h, hc⟩
    have hsub : Misses c i ⊆ fsets4 n := by
      intro S hS
      rw [mem_Misses] at hS
      exact mem_fsets4.mpr hS.1
    rw [h1, h2, h3, Finset.card_sdiff_of_subset hsub]
  have hright : Finset.sum (fsets4 n) f2 = (Doubles c i).card := by
    simp only [hf2]
    exact (merge_eq_sum (c := c) i).symm
  calc (∑ S ∈ fsets4 n, (classIn c i S).card)
      = Finset.sum (fsets4 n) fsum := by
        refine Finset.sum_congr rfl fun S hS => hsplit S (mem_fsets4.mp hS)
      _ = Finset.sum (fsets4 n) f0 + Finset.sum (fsets4 n) f2 := by
        simp only [hfsum]
        exact Finset.sum_add_distrib
      _ = (Finset.card (fsets4 n) - (Misses c i).card) + (Doubles c i).card := by
        rw [hleft, hright]

/-- **THE MERGER IDENTITY, EXACT.**  In an admissible colouring the four-set profile of the colour
class `E_i` is determined by `|E_i|`: it doubles exactly `|E_i|·C(n-2,2) - (C(n,4) - misses)`
four-sets, where `misses` is the number of four-sets missing `i`. -/
theorem doubles_eq {n k : ℕ} {c : Col n k} (hc : Admissible c) (i : Fin k) :
    (Doubles c i).card
      = Finset.card (classIn c i (Finset.univ : Finset (Verts n))) * Nat.choose (n - 2) 2
        - (Finset.card (fsets4 n) - (Misses c i).card) := by
  have h1 := incidence (n := n) (c := c) i
  have h2 := merge_split hc i
  omega

/-! ### §5  The spread condition -/

/-- Every colour class doubles at least `|E_i| · C(n-2,2) - C(n,4)` four-sets: in an admissible
colouring the doubled four-sets and the missed four-sets together pay for all of `C(n,4)`. -/
theorem doubles_nonneg {n k : ℕ} {c : Col n k} (hc : Admissible c) (i : Fin k) :
    Finset.card (classIn c i (Finset.univ : Finset (Verts n))) * Nat.choose (n - 2) 2
      + (Misses c i).card ≥ Finset.card (fsets4 n) := by
  set B := Finset.card (fsets4 n) with hB
  set C := (Misses c i).card with hC
  set D := (Doubles c i).card with hD
  set A := Finset.card (classIn c i (Finset.univ : Finset (Verts n))) * Nat.choose (n - 2) 2
    with hA
  have h1' : A - (B - C) = D := by
    have h1 := doubles_eq hc i
    rw [← hA, ← hB, ← hC, ← hD] at h1
    exact h1.symm
  have h3' : Finset.sum (fsets4 n) (fun S : Finset (Verts n) => (classIn c i S).card) = A := by
    have h3 := incidence (n := n) (c := c) i
    rwa [← hA] at h3
  have h2' : (B - C) + D = Finset.sum (fsets4 n)
      (fun S : Finset (Verts n) => (classIn c i S).card) := by
    have h2 := merge_split hc i
    rw [← hB, ← hC, ← hD] at h2
    exact h2.symm
  rw [hA, hC, hB]
  set E := B - C with hE
  have hE' : A - E = D := by rw [hE]; exact h1'
  by_cases hle : C ≤ B
  · have hsub2 : B - C + C = B := Nat.sub_add_cancel hle
    have hE2 : E + C = B := by rw [hE]; exact hsub2
    calc A + C = E + D + C := by omega
      _ = D + B := by
        calc E + D + C = E + (D + C) := Nat.add_assoc _ _ _
          _ = E + (C + D) := congrArg (fun z : ℕ => E + z) (Nat.add_comm D C)
          _ = (E + C) + D := (Nat.add_assoc _ _ _).symm
          _ = B + D := by rw [hE2]
          _ = D + B := Nat.add_comm _ _
      _ ≥ B := by omega
  · have hz : B - C = 0 := Nat.sub_eq_zero_of_le (by omega)
    have hz' : E = 0 := by rw [hE]; exact hz
    rw [hz'] at hE'
    omega

/-- **For `k ≤ 5` every colour meets every four-set.**  In an admissible colouring with at most five
colours the five-or-more colours of a `K₄` exhaust the palette, so no colour can be missing from a
four-set. -/
theorem empty4_eq_empty {n k : ℕ} {c : Col n k} (hc : Admissible c) (hk : k ≤ 5) (i : Fin k) :
    Misses c i = ∅ := by
  refine Finset.eq_empty_iff_forall_notMem.mpr fun S hS => ?_
  rw [mem_Misses] at hS
  obtain ⟨hS4, hSi⟩ := hS
  have hle : (classIn c i S).card ≤ 2 := classIn_card_le_two hc i S hS4
  have hc1 := hc S hS4
  have hc2 : (colorsOn c S).card ≤ k - 1 := by
    rw [colorsOn_eq_filter]
    have hkey : (Finset.univ : Finset (Fin k)).filter (fun t => 0 < (classIn c t S).card)
        = (Finset.univ : Finset (Fin k)).filter (fun t => (classIn c t S).card ≠ 0) :=
      Finset.filter_congr fun _ _ => Nat.pos_iff_ne_zero
    rw [hkey]
    have hsplit : (Finset.univ : Finset (Fin k)).filter
        (fun t => (classIn c t S).card ≠ 0)
        = (Finset.univ : Finset (Fin k)) \ ((Finset.univ : Finset (Fin k)).filter
            (fun t => (classIn c t S).card = 0)) := by
      ext t
      by_cases h : (classIn c t S).card = 0 <;> simp [h]
    rw [hsplit]
    have hpos : 0 < ((Finset.univ : Finset (Fin k)).filter
        (fun t => (classIn c t S).card = 0)).card :=
      Finset.card_pos.mpr
        ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hSi⟩⟩
    have hsub : ((Finset.univ : Finset (Fin k)).filter
        (fun t => (classIn c t S).card = 0)) ⊆ (Finset.univ : Finset (Fin k)) :=
      Finset.filter_subset _ _
    rw [Finset.card_sdiff_of_subset hsub, Finset.card_univ, Fintype.card_fin]
    exact Nat.sub_le_sub_left hpos k
  omega

/-- **For `k ≤ 5` the four-set profile of the colour class `E_i` is
`|E_i|·C(n-2,2) - C(n,4)`.** -/
theorem doubles_eq_of_k_le_five {n k : ℕ} {c : Col n k} (hc : Admissible c) (hk : k ≤ 5)
    (i : Fin k) : (Doubles c i).card
      = Finset.card (classIn c i (Finset.univ : Finset (Verts n))) * Nat.choose (n - 2) 2
        - Finset.card (fsets4 n) := by
  have h := doubles_eq hc i
  have hz : (Misses c i).card = 0 := by rw [empty4_eq_empty hc hk i]; rfl
  rw [hz, Nat.sub_zero] at h
  exact h

/-- **THE SIZE LOWER BOUND.**  In an admissible `k`-colouring of `K_n` with `k ≤ 5`, **every colour
class has at least `C(n,4)/C(n-2,2) = n(n-1)/12` edges**: a colour class that is too small cannot
double enough four-sets to pay for the `C(n,4)` four-sets it is responsible for.  This is a new
necessary condition, complementary to the classical upper bound `3|E_i| ≤ 2n`
(`Counting.three_mul_classIn_le`). -/
theorem classIn_card_ge {n k : ℕ} {c : Col n k} (hc : Admissible c) (hk : k ≤ 5) (i : Fin k) :
    Finset.card (classIn c i (Finset.univ : Finset (Verts n))) * Nat.choose (n - 2) 2
      ≥ Finset.card (fsets4 n) := by
  have hone : ∀ S ∈ fsets4 n, 1 ≤ Finset.card (classIn c i S) := by
    intro S hS
    have hnz : Finset.card (classIn c i S) ≠ 0 := fun hz => by
      have hmem : S ∈ Misses c i := by
        rw [mem_Misses, Finset.card_eq_zero.mp hz]
        exact ⟨mem_fsets4.mp hS, rfl⟩
      rw [empty4_eq_empty hc hk i] at hmem
      simp at hmem
    omega
  calc Finset.card (fsets4 n) = ∑ S ∈ fsets4 n, 1 := Finset.card_eq_sum_ones _
    _ ≤ ∑ S ∈ fsets4 n, Finset.card (classIn c i S) := Finset.sum_le_sum fun S hS => hone S hS
    _ = Finset.card (classIn c i (Finset.univ : Finset (Verts n))) * Nat.choose (n - 2) 2 :=
      incidence i

/-- **At `n = 6, k = 5` every colour class has at least three edges** — so, since the five colour
classes partition the fifteen edges of `K₆`, each of them has **exactly** three.  Every admissible
5-colouring of `K₆` therefore splits the edges into five triples, as a 1-factorisation does. -/
theorem six_classIn_card_ge {k : ℕ} {c : Col 6 k} (hc : Admissible c) (hk : k ≤ 5) (i : Fin k) :
    3 ≤ Finset.card (classIn c i (Finset.univ : Finset (Verts 6))) := by
  have h := classIn_card_ge hc hk i
  have hN : Finset.card (fsets4 6) = 15 := by
    rw [card_fsets4]
    decide
  have hC : Nat.choose (6 - 2) 2 = 6 := by decide
  rw [hN, hC] at h
  omega

/-- **At `n = 5, k = 5` every colour class has at least two edges** — the ten edges of `K₅` split
into five pairs, as in a 1-factorisation of `K₅`. -/
theorem five_classIn_card_ge {k : ℕ} {c : Col 5 k} (hc : Admissible c) (hk : k ≤ 5) (i : Fin k) :
    2 ≤ Finset.card (classIn c i (Finset.univ : Finset (Verts 5))) := by
  have h := classIn_card_ge hc hk i
  have hN : Finset.card (fsets4 5) = 5 := by
    rw [card_fsets4]
    decide
  have hC : Nat.choose (5 - 2) 2 = 3 := by decide
  rw [hN, hC] at h
  omega

/-- **THE SPREAD CONDITION.**  In an admissible `k`-colouring of `K_n`, the four-sets missing a
given colour altogether are, summed over all colours, at most `(k-5)` times the number of all
four-sets: *no colour class can hide.*  Equivalently, averaged over the colours, every colour class
occurs in at least a `5/k` fraction of all four-vertex sets. -/
theorem spread {n k : ℕ} {c : Col n k} (hc : Admissible c) :
    (∑ i : Fin k, (Misses c i).card) ≤ (k - 5) * Finset.card (fsets4 n) := by
  have key2 : ∀ i : Fin k, (∑ S ∈ fsets4 n, (classIn c i S).card)
      = Finset.card (fsets4 n) - (Misses c i).card + (Doubles c i).card :=
    fun i => merge_split hc i
  have hq' : 6 * Finset.card (fsets4 n)
      = ∑ (i : Fin k), (Finset.card (fsets4 n) - (Misses c i).card + (Doubles c i).card) := by
    have h1 : 6 * Finset.card (fsets4 n) = ∑ S ∈ fsets4 n, ((6 : ℕ)) := by
      simp [Nat.mul_comm]
    have h2 : (∑ S ∈ fsets4 n, ((6 : ℕ)))
        = ∑ S ∈ fsets4 n, ∑ i : Fin k, (classIn c i S).card := by
      refine Finset.sum_congr rfl fun S hS => ?_
      rw [sum_eq_six (mem_fsets4.mp hS)]
    have h3 : (∑ S ∈ fsets4 n, ∑ i : Fin k, (classIn c i S).card)
        = ∑ i : Fin k, ∑ S ∈ fsets4 n, (classIn c i S).card := Finset.sum_comm
    have h4 : (∑ i : Fin k, ∑ S ∈ fsets4 n, (classIn c i S).card)
        = ∑ (i : Fin k), (Finset.card (fsets4 n) - (Misses c i).card + (Doubles c i).card) := by
      refine Finset.sum_congr rfl fun i _ => key2 i
    exact h1.trans (h2.trans (h3.trans h4))
  have hB : (∑ i : Fin k, (Finset.card (fsets4 n) : ℕ)) = k * Finset.card (fsets4 n) := by
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin, Nat.cast_id]
  have hsub' : (∑ i : Fin k, (Finset.card (fsets4 n) - (Misses c i).card))
      = ∑ i : Fin k, (Finset.card (fsets4 n) : ℕ) - ∑ i : Fin k, (Misses c i).card := by
    have key : ∀ i : Fin k, Finset.card (fsets4 n) - (Misses c i).card + (Misses c i).card
        = Finset.card (fsets4 n) :=
      fun i => Nat.sub_add_cancel (Finset.card_le_card (Finset.filter_subset _ _))
    have h1 : (∑ i : Fin k, (Finset.card (fsets4 n) - (Misses c i).card))
        + ∑ i : Fin k, (Misses c i).card
        = ∑ i : Fin k, (Finset.card (fsets4 n) : ℕ) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => key i
    have hle : (∑ i : Fin k, (Misses c i).card) ≤ ∑ i : Fin k, (Finset.card (fsets4 n) : ℕ) := by
      refine Finset.sum_le_sum fun i _ => ?_
      exact Finset.card_le_card (Finset.filter_subset _ _)
    refine (Nat.add_sub_cancel_right
        ((∑ i : Fin k, (Finset.card (fsets4 n) - (Misses c i).card)) : ℕ)
        ((∑ i : Fin k, (Misses c i).card) : ℕ)).symm.trans ?_
    rw [h1]
  have hbal : 6 * Finset.card (fsets4 n)
      = (∑ i : Fin k, (Finset.card (fsets4 n) : ℕ)) - ∑ i : Fin k, (Misses c i).card
        + ∑ i : Fin k, (Doubles c i).card := by
    calc 6 * Finset.card (fsets4 n)
        = ∑ i : Fin k, (Finset.card (fsets4 n) - (Misses c i).card + (Doubles c i).card) := hq'
      _ = (∑ i : Fin k, (Finset.card (fsets4 n) - (Misses c i).card))
          + ∑ i : Fin k, (Doubles c i).card := Finset.sum_add_distrib
      _ = (∑ i : Fin k, (Finset.card (fsets4 n) : ℕ)) - ∑ i : Fin k, (Misses c i).card
          + ∑ i : Fin k, (Doubles c i).card := by rw [hsub']
  have hbud := budget hc
  have hfle : (∑ i : Fin k, (Misses c i).card) ≤ ∑ i : Fin k, (Finset.card (fsets4 n) : ℕ) := by
    refine Finset.sum_le_sum fun i _ => ?_
    exact Finset.card_le_card (Finset.filter_subset _ _)
  by_cases hk5 : 5 ≤ k
  · rw [Nat.sub_mul]
    have hsub_eq : (∑ i : Fin k, (Finset.card (fsets4 n) : ℕ))
        - ∑ i : Fin k, (Misses c i).card
        = 6 * Finset.card (fsets4 n) - ∑ i : Fin k, (Doubles c i).card := by omega
    have he : (∑ i : Fin k, (Doubles c i).card) ≤ Finset.card (fsets4 n) := hbud
    have hsub_ge : 5 * Finset.card (fsets4 n)
        ≤ 6 * Finset.card (fsets4 n) - ∑ i : Fin k, (Doubles c i).card := by
      have h2 : (6 * Finset.card (fsets4 n) - ∑ i : Fin k, (Doubles c i).card)
          + ∑ i : Fin k, (Doubles c i).card = 6 * Finset.card (fsets4 n) :=
        Nat.sub_add_cancel (by omega)
      have h3 : 5 * Finset.card (fsets4 n) + ∑ i : Fin k, (Doubles c i).card
          ≤ 6 * Finset.card (fsets4 n) := by omega
      have h3' : 5 * Finset.card (fsets4 n)
          ≤ (6 * Finset.card (fsets4 n) - ∑ i : Fin k, (Doubles c i).card) + 0 := by
        omega
      omega
    have h5 : 5 * Finset.card (fsets4 n)
        ≤ (∑ i : Fin k, (Finset.card (fsets4 n) : ℕ)) - ∑ i : Fin k, (Misses c i).card :=
      hsub_eq ▸ hsub_ge
    have h6 : (∑ i : Fin k, (Misses c i).card) + 5 * Finset.card (fsets4 n)
        ≤ ∑ i : Fin k, (Finset.card (fsets4 n) : ℕ) := by omega
    have h7 : (∑ i : Fin k, (Misses c i).card)
        ≤ ∑ i : Fin k, (Finset.card (fsets4 n) : ℕ) - 5 * Finset.card (fsets4 n) := by
      have h5b : 5 * Finset.card (fsets4 n)
          ≤ ∑ i : Fin k, (Finset.card (fsets4 n) : ℕ) := by omega
      omega
    rw [← hB]
    exact h7
  · have hz : ∀ i : Fin k, (Misses c i).card = 0 := fun i => by
      rw [empty4_eq_empty hc (by omega) i]
      rfl
    simp [hz]

end JSP140
