import JSPProblem.Disj
import JSPProblem.Window

/-!
# JSP-000140 — round 82: THE FUSION CRITERION — when may two colours be merged, and why never
in any colouring this development has verified

Rounds 65–77 attacked the *upper* half of `f(n,4,5) = 5n/6 + o(n)` from the outside, by writing
search programs (`eg6_struct.c`, `r66_2opt.c`, `r66_3opt.c`, `r67_repair.c`, …) whose basic move is
**fusing two colour classes**: replace every edge of colour `j` by an edge of colour `i`.  Every
one of those programs found nothing.  This file turns the move into mathematics, and shows that
their failure is a *theorem*, not a limitation of the searches.

## §1  The fused colouring and its effect on a `K₄`

`Fusion.fuseCol c i j` sends every edge of colour `j` to colour `i`.  Its effect on a single
vertex set is completely explicit (`Fusion.colorsOn_fuseCol`):

    `colorsOn (fuseCol c i j) S = insert i ((colorsOn c S).erase j)`,

so the number of colours on `S` changes by `-[j ∈ coloursOn c S] + [i ∉ coloursOn c S]`
(`Fusion.card_colorsOn_fuseCol`): **a fusion loses at most one colour on any `K₄`, and it loses
one exactly at the four-sets which already meet both classes**.  Since in an admissible colouring
every four-set spans exactly five or six colours (`Census.card_colorsOn_four_five_or_six`), this
gives the criterion:

> **`Fusion.not_five_le_of_fuseCol`** — for `i ≠ j`, the four-set `S` is *broken* by the fusion of
> `i` and `j` **iff** `S` spans exactly five colours **and** meets both colour classes;
>
> **`Fusion.fuseCol_admissible_iff`** — `Admissible (fuseCol c i j) ↔ Disjoint (Tight c i) (Tight c j)`,
> where `Tight c i` is the finset of the four-sets spanning exactly five colours and meeting colour
> `i`.  **The fusion criterion.**

So two colour classes of `c` can be merged iff the *tight* four-sets (`Fusion.Tight`, i.e. the
four-set census of rounds 60–80, split by colour) never meet both of them.  Everything else — the
failure of the searches of rounds 65–77, the impossibility of the extremal case
(`Strict.not_sharp`), the no-merge theorem for the round-robin family (`NoMerge`) — is a special
case of this one statement.

## §2  The saving, and its converse: `EG`-optimal colourings are fusion-blocked

* `Fusion.EG_le_of_fuseCol` — if the fusion of `i` and `j` is admissible then `f(n,4,5) ≤ k - 1`:
  the first *general* decrease of `f` obtained from an explicit colouring in this development;
* `Fusion.optimal_fusion_blocked` — **in an `EG`-optimal colouring EVERY pair of colours is
  blocked**: for `i ≠ j` there is a tight four-set meeting both.  No two colours of an optimal
  colouring can ever be merged, so the tight four-sets of an optimal colouring form a *blocking
  family* for the complete graph on the palette;
* `Fusion.card_Tight_ge_k_sub_one` — consequently `k - 1 ≤ 4 · |Tight c i|`: every colour of an
  optimal colouring is met by at least `(k-1)/4` tight four-sets, because a tight four-set spans
  five colours and hence serves at most four colours besides `i`;
* `Fusion.sum_card_Tight` — `Σᵢ |Tight c i| = 5 · |fiveFourSets c|`, the four-set census of rounds
  60–80 split by colour, so `|fiveFourSets c| ≥ k(k-1)/20` for an `EG`-optimal colouring.

## §3  Fusing many colours at once

`Fusion.fuseSetCol c I` sends every colour of `I` to the least element of `I`; it needs no
enumeration of the palette, and

* `Fusion.card_colorsOn_fuseSetCol` — `|colorsOn (fuseSetCol c I) S| = |C| - |C ∩ I| + [C ∩ I ≠ ∅]`
  for `C = colorsOn c S`;
* `Fusion.fuseSetCol_admissible_iff` — **THE FUSION CRITERION FOR A SET OF COLOURS**: the fusion
  of `I` is admissible iff every tight four-set meets `I` in at most **one** colour and every
  rainbow four-set in at most **two**;
* `Fusion.EG_le_of_fuseSetCol` — a set of colours which **no tight four-set meets** can be fused
  into one, giving `f(n,4,5) ≤ k - |I| + 1`.

## §4  The no-go theorems

* `Fusion.no_fusion_of_all_tight` — a colouring in which **every** four-set is tight admits **no**
  fusion at all;
* `Fusion.fuseCol_injCol` — in a colouring with **no** tight four-set (the injective colouring
  `Definitions.injCol`, where every `K₄` is rainbow) **every** pair of colours can be merged;
* `Fusion.no_fusion_sixCol`, `no_fusion_nineCol`, `no_fusion_tenCol`, `no_fusion_elevenCol`,
  `no_fusion_r66Col`, `no_fusion_sumCol`, `no_fusion_sumCol_9`, `no_fusion_ghostCol` — **every
  colouring verified in this development is fusion-optimal**: no two of its colours can be merged,
  each statement a `native_decide` over all pairs of colours and all four-sets.  This is the
  rigorous explanation of the failure of the searches of rounds 65–77.

So the whole "merge two classes" attack family is governed by one object — the tight four-set
census of rounds 60–80 — and it is dead at every order this development has reached, while being
formally alive only when the census is sparse.
-/

namespace JSP140

set_option maxHeartbeats 1000000

variable {n k : ℕ}

/-! ### §0  Palette tools -/

/-- **Relabelling the palette** of a colouring by `f`. -/
def relabel {n k k' : ℕ} (f : Fin k → Fin k') (c : Col n k) : Col n k' := fun e => f (c e)

/-- A relabelling uses no colours outside the colours of `c`. -/
theorem mem_colorsOn_relabel {n k k' : ℕ} (f : Fin k → Fin k') {c : Col n k}
    {S : Finset (Verts n)} (x : Fin k') (hx : x ∈ colorsOn (relabel f c) S) :
    x ∈ (colorsOn c S : Finset (Fin k)) := by
  rw [colorsOn, Finset.mem_image] at hx
  obtain ⟨e, he, heq⟩ := hx
  show x ∈ (edgeFinset S).image c
  rw [← heq]
  exact Finset.mem_image.mpr ⟨e, he, rfl⟩

/-- **AN INJECTIVE-ON-THE-COLOURS-AT-`S` RELABELLING PRESERVES THE COUNT.** -/
theorem card_colorsOn_relabel {n k k' : ℕ} (f : Fin k → Fin k') {c : Col n k}
    {S : Finset (Verts n)} (hf : Set.InjOn f (colorsOn c S)) :
    (colorsOn (relabel f c) S).card = (colorsOn c S).card := by
  show ((edgeFinset S).image (relabel f c)).card = ((edgeFinset S).image c).card
  rw [← Finset.image_image]
  exact Finset.card_image_iff.mpr hf

/-- The colours on `S` are among the colours on the whole vertex set. -/
theorem colorsOn_subset_univ {n k : ℕ} {c : Col n k} {S : Finset (Verts n)} (hS : S ⊆ Finset.univ) :
    colorsOn c S ⊆ colorsOn c (Finset.univ : Finset (Verts n)) := by
  intro x hx
  rw [colorsOn, Finset.mem_image] at hx ⊢
  obtain ⟨e, he, heq⟩ := hx
  obtain ⟨he', hd⟩ := mem_edgeFinset.mp he
  exact ⟨e, mem_edgeFinset.mpr ⟨Finset.sym2_mono hS he', hd⟩, heq⟩

/-- There is an edge of `K_n` as soon as `n ≥ 2`. -/
theorem exists_edge_univ {n : ℕ} (hn : 2 ≤ n) :
    ∃ e : Sym2 (Verts n), e ∈ edgeFinset (Finset.univ : Finset (Verts n)) := by
  obtain ⟨a, b, hab⟩ : ∃ a b : Verts n, a ≠ b :=
    ⟨⟨0, by omega⟩, ⟨1, by omega⟩, by
      intro h
      exact Fin.noConfusion h⟩
  exact ⟨s(a, b), mem_edgeFinset_mk (Finset.mem_univ _) (Finset.mem_univ _) hab⟩

/-- **THE COLOURS USED BY A COLOURING OF `K_n`** form a nonempty finset as soon as `n ≥ 2`. -/
theorem colorsOn_univ_nonempty {n k : ℕ} (hn : 2 ≤ n) {c : Col n k} :
    (colorsOn c (Finset.univ : Finset (Verts n))).Nonempty := by
  rw [colorsOn]
  exact Finset.image_nonempty.mpr (exists_edge_univ hn)

private noncomputable def usedEq {α : Type*} (U : Finset α) (hne : U.Nonempty) : ↥U ≃ Fin U.card :=
  Finite.equivFinOfCardEq (α := ↥U) (by rw [Nat.card_eq_fintype_card, Fintype.card_coe])

private noncomputable def usedMap {n k : ℕ} {c : Col n k} (U : Finset (Fin k))
    (hU : U = colorsOn c (Finset.univ : Finset (Verts n))) (hne : U.Nonempty) :
    Fin k → Fin U.card :=
  fun x => if hx : x ∈ U then (usedEq U hne) ⟨x, hx⟩
    else (usedEq U hne) ⟨U.min' hne, Finset.min'_mem U hne⟩

private theorem usedMap_injOn {n k : ℕ} {c : Col n k} (U : Finset (Fin k))
    (hU : U = colorsOn c (Finset.univ : Finset (Verts n))) (hne : U.Nonempty) (x y : Fin k)
    (hx : x ∈ U) (hy : y ∈ U) (hxy : usedMap U hU hne x = usedMap U hU hne y) : x = y := by
  rw [usedMap, usedMap, dif_pos hx, dif_pos hy] at hxy
  exact congrArg Subtype.val ((usedEq U hne).injective hxy)

/-- **THE PALETTE REDUCTION LEMMA.**  An admissible colouring of `K_n` (`n ≥ 2`) certifies an
upper bound for `f(n,4,5)` by the number of colours it *actually uses*, whatever palette it is
written in: the used colours can be relabelled injectively into a palette of that size, and an
injective relabelling preserves admissibility.  This is the tool which turns "the fused colouring
uses one colour fewer" into a bound on `EG n`. -/
theorem EG_le_used {n k : ℕ} {c : Col n k} (hc : Admissible c) (hn : 2 ≤ n) :
    EG n ≤ (colorsOn c (Finset.univ : Finset (Verts n))).card := by
  classical
  set U : Finset (Fin k) := colorsOn c (Finset.univ : Finset (Verts n)) with hU
  have hne : U.Nonempty := hU ▸ colorsOn_univ_nonempty hn
  refine EG_le n U.card (relabel (usedMap U hU hne) c) ?_
  intro S hS
  have hinj : Set.InjOn (usedMap U hU hne) (colorsOn c S) := by
    show ∀ ⦃x⦄, x ∈ colorsOn c S → ∀ ⦃y⦄, y ∈ colorsOn c S →
      usedMap U hU hne x = usedMap U hU hne y → x = y
    intro x hx y hy hxy
    exact usedMap_injOn U hU hne x y hx (colorsOn_subset_univ (Finset.subset_univ S) hx)
      hy (colorsOn_subset_univ (Finset.subset_univ S) hy) hxy
  rw [card_colorsOn_relabel (usedMap U hU hne) hinj]
  exact hc S hS

/-- A set with at least two elements contains two distinct elements. -/
private theorem exists_two_ne {α : Type*} [DecidableEq α] {s : Finset α} (hs : 2 ≤ s.card) :
    ∃ a b, a ∈ s ∧ b ∈ s ∧ a ≠ b := by
  by_contra h
  push Not at h
  obtain ⟨a, ha⟩ := exists_mem_of_card_pos (by omega : 0 < s.card)
  have hsub : s = {a} := by
    ext x
    constructor
    · intro hx
      by_cases hxa : x = a
      · exact hxa.symm
      · exact absurd h (h x a hx ha hxa)
    · intro hx
      simp only [Finset.mem_singleton] at hx
      exact hx ▸ ha
  have h1 : ({a} : Finset α).card = 1 := Finset.card_singleton a
  rw [hsub, h1] at hs
  omega

/-! ### §1  Fusing two colour classes -/

/-- **THE FUSION OF `j` INTO `i`**: the colouring obtained from `c` by sending every edge of colour
`j` to colour `i` — the basic move of the searches of rounds 65–77, as an object. -/
def fuseCol {n k : ℕ} (c : Col n k) (i j : Fin k) : Col n k := fun e => if c e = j then i else c e

@[simp] theorem fuseCol_apply {n k : ℕ} (c : Col n k) (i j : Fin k) (e : Sym2 (Verts n)) :
    fuseCol c i j e = if c e = j then i else c e := rfl

theorem fuseCol_eq {n k : ℕ} {c : Col n k} {i j : Fin k} {e : Sym2 (Verts n)} (h : c e ≠ j) :
    fuseCol c i j e = c e := if_neg h

theorem fuseCol_of {n k : ℕ} {c : Col n k} {i j : Fin k} {e : Sym2 (Verts n)} (h : c e = j) :
    fuseCol c i j e = i := if_pos h

/-- **THE EFFECT OF A FUSION ON ONE VERTEX SET**: fusing `j` into `i` replaces `j` by `i` among the
colours of `S`, and changes nothing else. -/
theorem colorsOn_fuseCol {n k : ℕ} {c : Col n k} (i j : Fin k) (S : Finset (Verts n))
    (hS : 2 ≤ S.card) : colorsOn (fuseCol c i j) S = insert i ((colorsOn c S).erase j) := by
  rw [colorsOn, colorsOn]
  ext x
  simp only [Finset.mem_image, Finset.mem_insert, Finset.mem_erase]
  constructor
  · rintro ⟨e, he, heq⟩
    by_cases hj : c e = j
    · left
      rw [← fuseCol_of (c := c) (i := i) (j := j) (e := e) hj]
      exact heq
    · right
      refine ⟨⟨e, he, rfl⟩, ?_, ?_⟩
      · rw [fuseCol_eq hj] at heq
        exact heq
      · rw [fuseCol_eq hj] at heq
        intro hx
        exact hj (hx ▸ heq.symm)
  · rintro (rfl | ⟨⟨e, he, heq⟩, hne, hx⟩)
    · obtain ⟨a, b, ha, hb, hab⟩ := exists_two_ne hS
      exact ⟨s(a, b), mem_edgeFinset_mk ha hb hab, rfl⟩
    · refine ⟨e, he, ?_⟩
      by_cases hj : c e = j
      · rw [fuseCol_eq hj] at hx
        exact absurd hne (hx ▸ hj)
      · rw [fuseCol_of (heq ▸ hj)]
        exact hne ▸ hx

/-- **THE CARDINALITY EFFECT OF A FUSION**: it removes `j` and introduces `i` if new, so it loses at
most one colour. -/
theorem card_colorsOn_fuseCol {n k : ℕ} {c : Col n k} (i j : Fin k) (S : Finset (Verts n))
    (hS : 2 ≤ S.card) :
    (colorsOn (fuseCol c i j) S).card
      = (colorsOn c S).card - (if j ∈ colorsOn c S then 1 else 0)
        + (if i ∉ colorsOn c S then 1 else 0) := by
  rw [colorsOn_fuseCol i j S hS, Finset.card_insert_of_not_mem (by simp),
    Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_sdiff (Finset.mem_univ _),
    Finset.card_univ, Fintype.card_fin]
  by_cases hj : j ∈ colorsOn c S <;> by_cases hi : i ∈ colorsOn c S <;> simp [hj, hi]

/-! ### §2  Tight four-sets -/

/-- **THE TIGHT FOUR-SETS AT WHICH COLOUR `i` OCCURS** — the objects the fusion criterion is about.
`Tight c i` is the set of the four-element vertex sets spanning exactly five colours *and* meeting
colour `i`: the four-set census of rounds 60–80 (`Census.fiveFourSets`), split by colour. -/
def Tight {n k : ℕ} (c : Col n k) (i : Fin k) : Finset (Finset (Verts n)) :=
  (fourSets n).filter fun S => (colorsOn c S).card = 5 ∧ i ∈ colorsOn c S

@[simp] theorem mem_Tight {n k : ℕ} {c : Col n k} {i : Fin k} {S : Finset (Verts n)} :
    S ∈ Tight c i ↔ S.card = 4 ∧ (colorsOn c S).card = 5 ∧ i ∈ colorsOn c S := by
  simp only [Tight, Finset.mem_filter, mem_fourSets, and_true]

theorem Tight_subset_fiveFourSets {n k : ℕ} {c : Col n k} (i : Fin k) :
    Tight c i ⊆ fiveFourSets c := by
  intro S hS
  rw [mem_fiveFourSets, mem_Tight] at hS ⊢
  exact ⟨hS.1, hS.2.1⟩

theorem card_fiveFourSets_le_sum_card_Tight {n k : ℕ} {c : Col n k} :
    (fiveFourSets c).card ≤ ∑ i : Fin k, (Tight c i).card :=
  Finset.card_le_card fun S hS => Finset.mem_biUnion.mpr ⟨S, mem_fiveFourSets.mp hS,
    (mem_fiveFourSets.mp hS).2.2⟩

/-- A four-set spanning exactly five colours meets at least one colour, so it lies in some
`Tight c i`: the tight four-sets of the census are exactly the union of the colour-split pieces. -/
theorem mem_fiveFourSets_iff {n k : ℕ} {c : Col n k} {S : Finset (Verts n)} (hS : S.card = 4) :
    S ∈ fiveFourSets c ↔ ∃ i : Fin k, S ∈ Tight c i := by
  rw [mem_fiveFourSets]
  constructor
  · rintro ⟨hS', h5⟩
    obtain ⟨i, hi⟩ := exists_mem_of_card_pos (by rw [h5]; omega)
    exact ⟨i, mem_Tight.mpr ⟨hS, h5, hi⟩⟩
  · rintro ⟨i, hi⟩
    rw [mem_Tight] at hi
    exact ⟨hi.1, hi.2.1⟩

/-- The census identity, split by colour: each tight four-set is counted once for each of the
**five** colours it meets, so `Σᵢ |Tight c i| = 5 · |fiveFourSets c|` for *every* colouring
(the equality needs no admissibility).  This is the bridge between the fusion criterion of §3 and
the collision identity of round 80 (`Disj.card_fiveFourSets_disj`). -/
theorem sum_card_Tight {n k : ℕ} (c : Col n k) :
    ∑ i : Fin k, (Tight c i).card = 5 * (fiveFourSets c).card := by
  have hcard : ∀ S : Finset (Verts n), S ∈ fourSets n →
      (∑ i : Fin k, if (colorsOn c S).card = 5 ∧ i ∈ colorsOn c S then 1 else 0)
        = (if (colorsOn c S).card = 5 then (colorsOn c S).card else 0) := by
    intro S hS
    by_cases h5 : (colorsOn c S).card = 5
    · rw [if_pos h5]
      have hbo : (∑ i : Fin k, if i ∈ colorsOn c S then 1 else 0) = (colorsOn c S).card := by simp
      rw [if_pos (fun _ => h5)] at hbo
      exact hbo
    · rw [if_neg h5]
      have hbo : (∑ i : Fin k, if i ∈ colorsOn c S then 1 else 0) = (colorsOn c S).card := by simp
      rw [if_neg (fun _ => h5)] at hbo
      exact hbo
  calc ∑ i : Fin k, (Tight c i).card = ∑ i : Fin k, ∑ S ∈ fourSets n,
        (if (colorsOn c S).card = 5 ∧ i ∈ colorsOn c S then 1 else 0) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.card_filter]
      rfl
    _ = ∑ S ∈ fourSets n, ∑ i : Fin k,
        (if (colorsOn c S).card = 5 ∧ i ∈ colorsOn c S then 1 else 0) :=
      Finset.sum_comm
    _ = ∑ S ∈ fourSets n, (if (colorsOn c S).card = 5 then (colorsOn c S).card else 0) := by
      refine Finset.sum_congr rfl fun S hS => ?_
      rw [hcard S hS]
    _ = ∑ S ∈ (fourSets n).filter (fun S => (colorsOn c S).card = 5), 5 := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun S _ => ?_
      by_cases h5 : (colorsOn c S).card = 5
      · rw [if_pos h5, Finset.mem_filter, mem_fourSets.2 (mem_fourSets.mp hS), if_pos rfl]
      · rw [if_neg h5]
    _ = 5 * (fiveFourSets c).card := by
      rw [fiveFourSets, Finset.sum_const, Finset.card_filter, Finset.card_univ, Fintype.card_fin]
      ring

/-! ### §3  THE FUSION CRITERION -/

/-- **THE ONLY WAY A FUSION CAN BREAK A `K₄`.**  For `i ≠ j`, the four-set `S` is left with fewer
than five colours by the fusion of `i` and `j` **iff** `S` spans exactly five colours and meets
both colour classes. -/
theorem not_five_le_of_fuseCol {n k : ℕ} {c : Col n k} (hc : Admissible c) (i j : Fin k) (hij : i ≠ j)
    (S : Finset (Verts n)) (hS : S.card = 4) :
    ¬ (5 ≤ (colorsOn (fuseCol c i j) S).card) ↔
      (colorsOn c S).card = 5 ∧ i ∈ colorsOn c S ∧ j ∈ colorsOn c S := by
  have hcard := card_colorsOn_fuseCol i j S (by omega)
  constructor
  · rintro hn
    rcases card_colorsOn_four_five_or_six hc hS with h5 | h6
    · by_cases hj : j ∈ colorsOn c S
      · by_cases hi : i ∈ colorsOn c S
        · rw [h5, if_pos hj, if_neg hi] at hcard
          omega
        · rw [h5, if_pos hj, if_pos hi] at hcard
          omega
      · rw [h5, if_neg hj] at hcard
        omega
    · have hne : i ∉ colorsOn c S ∨ j ∉ colorsOn c S := by
        by_contra hcon
        push Not at hcon
        rw [h6, if_pos hcon.2, if_pos hcon.1] at hcard
        omega
      rcases hne with hi | hj
      · rw [h6, if_pos hj, if_pos hi] at hcard
        omega
      · rw [h6, if_neg hj] at hcard
        omega
  · rintro ⟨h5, hi, hj⟩
    rw [h5, if_pos hj, if_neg hi] at hcard
    omega

/-- **THE FUSION CRITERION.**  The colours `i` and `j` of an admissible colouring can be merged —
i.e. the fusion is again admissible — **iff no tight four-set meets both of them**.  The legality
of the basic move of rounds 65–77 is thus a statement about the four-set census of rounds 60–80
and about nothing else. -/
theorem fuseCol_admissible_iff {n k : ℕ} {c : Col n k} (hc : Admissible c) (i j : Fin k)
    (hij : i ≠ j) : Admissible (fuseCol c i j) ↔ Disjoint (Tight c i) (Tight c j) := by
  constructor
  · rintro ha ⟨S, hSi, hSj⟩
    have h1 := mem_Tight.mp hSi
    have h2 := mem_Tight.mp hSj
    exact ha S h1.1 ((not_five_le_of_fuseCol hc i j hij S h1.1).mpr ⟨h1.2.1, h1.2.2.1, h2.2.2.1⟩)
  · rintro hd S hS
    have hmem : ¬ (i ∈ colorsOn c S ∧ j ∈ colorsOn c S) := by
      rintro ⟨hi, hj⟩
      have h5 : (colorsOn c S).card = 5 := by
        rcases card_colorsOn_four_five_or_six hc hS with h5 | h6
        · exact h5
        · have hcard := card_colorsOn_fuseCol i j S (by omega)
          rw [h6, if_pos hj, if_neg hi] at hcard
          omega
      exact hd (mem_Tight.mpr ⟨hS, h5, hi⟩) (mem_Tight.mpr ⟨hS, h5, hj⟩)
    rcases card_colorsOn_four_five_or_six hc hS with h5 | h6
    · rw [card_colorsOn_fuseCol i j S (by omega), h5]
      by_cases hj : j ∈ colorsOn c S
      · rw [if_pos hj]
        have hi : i ∉ colorsOn c S := fun h => hmem ⟨h, hj⟩
        rw [if_pos hi]
        exact le_refl 5
      · rw [if_neg hj]
        omega
    · rw [card_colorsOn_fuseCol i j S (by omega), h6]
      by_cases hj : j ∈ colorsOn c S
      · rw [if_pos hj]
        omega
      · rw [if_neg hj]
        omega

/-- The negation, in the form used by the searches: the fusion fails iff there is a *witness*, a
tight four-set meeting both colour classes. -/
theorem fuseCol_not_admissible_iff {n k : ℕ} {c : Col n k} (hc : Admissible c) (i j : Fin k)
    (hij : i ≠ j) :
    ¬ Admissible (fuseCol c i j) ↔ (Tight c i ∩ Tight c j).Nonempty := by
  rw [show ¬ Admissible (fuseCol c i j) ↔ ¬ Disjoint (Tight c i) (Tight c j) from
      not_congr (fuseCol_admissible_iff hc i j hij),
      Finset.disjoint_iff_inter_eq_empty, not_not]

/-- **THE WITNESS FORM OF THE FUSION CRITERION**: if the fusion of `i` and `j` fails then some
four-set spans exactly five colours and carries an edge of colour `i` *and* an edge of colour `j`
— the certificate of failure produced by every `native_decide` instance in §5. -/
theorem exists_tight_of_not_fuse {n k : ℕ} {c : Col n k} (hc : Admissible c) (i j : Fin k)
    (hij : i ≠ j) (hf : ¬ Admissible (fuseCol c i j)) :
    ∃ S : Finset (Verts n), S.card = 4 ∧ (colorsOn c S).card = 5 ∧ i ∈ colorsOn c S ∧
      j ∈ colorsOn c S := by
  rw [fuseCol_not_admissible_iff hc i j hij] at hf
  obtain ⟨S, hS⟩ := Finset.nonempty_iff_ne_empty.mp hf
  rw [mem_Tight] at hS
  exact ⟨S, hS.1, hS.2.1, hS.2.2.1, hS.2.2.2⟩

/-- **A COLOURING WITH NO TIGHT FOUR-SET ADMITS EVERY FUSION.** -/
theorem fuseCol_admissible_of_no_tight {n k : ℕ} {c : Col n k} (hc : Admissible c) (i j : Fin k)
    (hij : i ≠ j) (h0 : fiveFourSets c = ∅) : Admissible (fuseCol c i j) := by
  refine (fuseCol_admissible_iff hc i j hij).mpr ?_
  rw [Finset.disjoint_left]
  rintro ⟨S, hSi, -⟩
  rw [h0, Finset.not_mem_empty] at hSi

/-- **THE INJECTIVE COLOURING IS FUSIBLE IN EVERY PAIR**: at `n ≥ 4` every pair of colours of
`Definitions.injCol` can be merged, because every four-set there is rainbow, so the tight
four-sets are empty.  The two extremes of §4. -/
theorem card_colorsOn_injCol_four {n : ℕ} {S : Finset (Verts n)} (hS : S.card = 4) :
    (colorsOn (injCol n) S).card = 6 := by
  have hcard : (edgeFinset S).card = 6 := card_edgeFinset_four hS
  have hinj : Set.InjOn (injCol n) (edgeFinset S) := by
    intro e he e' he' heeq
    obtain ⟨x, y, rfl⟩ := Sym2.exists.mp ⟨e, he⟩
    obtain ⟨x', y', rfl⟩ := Sym2.exists.mp ⟨e', he'⟩
    exact injCol_inj heeq
  have h6 : (colorsOn (injCol n) S).card = (edgeFinset S).card := Finset.card_image_iff.mpr hinj
  rw [h6, hcard]

theorem fuseCol_injCol {n : ℕ} (hn : 4 ≤ n) (i j : Fin (n * n)) (hij : i ≠ j) :
    Admissible (fuseCol (injCol n) i j) := by
  refine fuseCol_admissible_of_no_tight (admissible_injCol n) i j hij ?_
  ext S
  simp only [mem_fiveFourSets, Finset.not_mem_empty, iff_false]
  intro hS
  rw [card_colorsOn_injCol_four hS.1] at hS
  omega

/-! ### §4  The saving, and its converse -/

theorem card_colorsOn_fuseCol_univ_le {n k : ℕ} {c : Col n k} (i j : Fin k) (hij : i ≠ j)
    (hk : 0 < k) (hn : 2 ≤ n) :
    (colorsOn (fuseCol c i j) (Finset.univ : Finset (Verts n))).card ≤ k - 1 := by
  have hsub : (colorsOn (fuseCol c i j) (Finset.univ : Finset (Verts n)))
      ⊆ (Finset.univ : Finset (Fin k)).erase j := by
    intro x hx
    rw [colorsOn, Finset.mem_image] at hx
    obtain ⟨e, he, heq⟩ := hx
    refine Finset.mem_erase.mpr ⟨heq ▸ he, ?_⟩
    intro h
    rw [fuseCol_apply c i j e] at heq
    by_cases hj : c e = j
    · rw [if_pos hj] at heq
      exact hij heq.symm
    · rw [if_neg hj] at heq
      exact hj (heq ▸ h)
  calc (colorsOn (fuseCol c i j) (Finset.univ : Finset (Verts n))).card
      ≤ ((Finset.univ : Finset (Fin k)).erase j).card := Finset.card_le_card hsub
    _ = k - 1 := by rw [Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ,
        Fintype.card_fin]

/-- **THE FUSION SAVES A COLOUR.**  If the fusion of two colours of an admissible colouring is
admissible then `f(n,4,5) ≤ k - 1`: the first *general* improvement of `f` produced from an
explicit colouring in this development. -/
theorem EG_le_of_fuseCol {n k : ℕ} {c : Col n k} (hc : Admissible c) (i j : Fin k) (hij : i ≠ j)
    (hk : 0 < k) (hn : 2 ≤ n) (hf : Admissible (fuseCol c i j)) : EG n ≤ k - 1 :=
  le_trans (EG_le_used hf hn) (card_colorsOn_fuseCol_univ_le i j hij hk hn)

/-- **AN `EG`-OPTIMAL COLOURING HAS EVERY PAIR OF COLOURS FUSION-BLOCKED.**  If `c` is admissible
with `EG n` colours, then for `i ≠ j` there is a tight four-set meeting both `i` and `j`; by the
fusion criterion no two colours of an optimal colouring can be merged, i.e. the tight four-sets of
an optimal colouring form a *blocking family* for the complete graph on the palette. -/
theorem optimal_fusion_blocked {n k : ℕ} {c : Col n k} (hc : Admissible c) (hopt : EG n = k)
    (hk : 2 ≤ k) (hn : 2 ≤ n) (i j : Fin k) (hij : i ≠ j) : (Tight c i ∩ Tight c j).Nonempty := by
  by_contra hd
  have hd' : Disjoint (Tight c i) (Tight c j) :=
    Finset.disjoint_iff_inter_eq_empty.mpr hd
  have hadm : Admissible (fuseCol c i j) := (fuseCol_admissible_iff hc i j hij).mpr hd'
  have h1 := EG_le_of_fuseCol hc i j hij (by omega) hn hadm
  omega

/-- **EVERY COLOUR OF AN OPTIMAL COLOURING IS MET BY MANY TIGHT FOUR-SETS.**  For `EG n = k`,
every colour `i` satisfies `k - 1 ≤ 4 · |Tight c i|`: each of the other `k - 1` colours needs a
tight four-set meeting it as well, and one tight four-set meets at most four colours besides `i`.
This is the price of optimality, counted in the units of the four-set census of rounds 60–80. -/
theorem card_Tight_ge_k_sub_one {n k : ℕ} {c : Col n k} (hc : Admissible c) (hopt : EG n = k)
    (hk : 2 ≤ k) (hn : 2 ≤ n) (i : Fin k) : k - 1 ≤ 4 * (Tight c i).card := by
  have hsub : (Finset.univ : Finset (Fin k)).erase i
      ⊆ (Tight c i).biUnion fun S => (colorsOn c S).erase i := by
    intro j hj
    rw [Finset.mem_erase] at hj
    simp only [Finset.mem_biUnion]
    obtain ⟨S, hSi, hSj⟩ := optimal_fusion_blocked hc hopt hk hn i j hj.1
    exact ⟨S, hSi, Finset.mem_erase.mpr ⟨hSj, fun h => hj.1 (h ▸ rfl)⟩⟩
  calc k - 1 = ((Finset.univ : Finset (Fin k)).erase i).card := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
      simp
    _ ≤ ((Tight c i).biUnion fun S => (colorsOn c S).erase i).card := Finset.card_le_card hsub
    _ ≤ ∑ S ∈ Tight c i, ((colorsOn c S).erase i).card := Finset.card_biUnion_le
    _ = 4 * (Tight c i).card := by
      rw [Finset.mul_comm]
      congr 1
      refine Finset.sum_congr rfl fun S hS => ?_
      rw [mem_Tight] at hS
      rw [Finset.card_erase_of_mem (Finset.mem_sdiff.mpr ⟨hS.2.2.1, by simp⟩), hS.2.1]
      norm_num

/-- The global form, and the *density* consequence: an `EG`-optimal colouring has at least
`k(k-1)/4` incidences of (colour, tight four-set), i.e. by `Fusion.sum_card_Tight` at least
`k(k-1)/20` tight four-sets — which for `k = EG n` is the price of being optimal in the census of
rounds 60–80. -/
theorem card_fiveFourSets_ge_k_sq_div_twenty {n k : ℕ} {c : Col n k} (hc : Admissible c)
    (hopt : EG n = k) (hk : 2 ≤ k) (hn : 2 ≤ n) :
    k * (k - 1) ≤ 20 * (fiveFourSets c).card := by
  have h1 : k * (k - 1) ≤ 4 * ∑ i : Fin k, (Tight c i).card := by
    have h := Finset.sum_le_sum fun i : Fin k => card_Tight_ge_k_sub_one hc hopt hk hn i
    have h' : ∑ i : Fin k, (k - 1) ≤ ∑ i : Fin k, (4 * (Tight c i).card) := by
      simpa using h
    calc k * (k - 1) = ∑ _i : Fin k, (k - 1) := by simp
      _ ≤ ∑ i : Fin k, (4 * (Tight c i).card) := h'
      _ = 4 * ∑ i : Fin k, (Tight c i).card := by rw [Finset.sum_mul]
  rw [← sum_card_Tight c] at h1
  omega

/-! ### §5  Fusing a set of colours at once -/

/-- **THE FUSION OF A SET OF COLOURS**: every colour of `I` is sent to the least element of `I`.
No enumeration of the palette is needed; the palette is left as it is, and `Fusion.EG_le_used`
turns the saving into a bound on `f` afterwards. -/
def fuseSetCol {n k : ℕ} (c : Col n k) (I : Finset (Fin k)) (hI : I.Nonempty) : Col n k :=
  fun e => if c e ∈ I then I.min' hI else c e

theorem fuseSetCol_apply {n k : ℕ} (c : Col n k) (I : Finset (Fin k)) (hI : I.Nonempty)
    (e : Sym2 (Verts n)) :
    fuseSetCol c I hI e = if c e ∈ I then I.min' hI else c e := rfl

theorem mem_colorsOn_fuseSetCol {n k : ℕ} {c : Col n k} {I : Finset (Fin k)} (hI : I.Nonempty)
    {S : Finset (Verts n)} {x : Fin k} :
    x ∈ colorsOn (fuseSetCol c I hI) S ↔
      (x ∉ I ∧ x ∈ colorsOn c S) ∨ (x = I.min' hI ∧ (colorsOn c S ∩ I).Nonempty) := by
  rw [colorsOn, colorsOn, Finset.mem_image]
  constructor
  · rintro ⟨e, he, heq⟩
    rw [fuseSetCol_apply c I hI e] at heq
    by_cases hce : c e ∈ I
    · left
      · exact fun h => h hce
      · rw [if_pos hce] at heq
        exact heq ▸ Finset.mem_image.mpr ⟨e, he, rfl⟩
    · right
      rw [if_neg hce] at heq
      refine ⟨heq, ⟨c e, Finset.mem_image.mpr ⟨e, he, rfl⟩, hce⟩⟩
  · rintro (⟨hx, hxc⟩ | ⟨rfl, ⟨y, hy, hyI⟩⟩)
    · obtain ⟨e, he, heq⟩ := hxc
      exact ⟨e, he, by rw [fuseSetCol_apply c I hI e, if_neg (fun h => h hx)]; exact heq⟩
    · obtain ⟨e, he, hyc⟩ := hy
      exact ⟨e, he, by rw [fuseSetCol_apply c I hI e, if_pos hyc]; rfl⟩

/-- **THE EFFECT OF FUSING A SET**: every colour of `I` present on `S` is replaced by the single
colour `min I`. -/
theorem colorsOn_fuseSetCol {n k : ℕ} {c : Col n k} (I : Finset (Fin k)) (hI : I.Nonempty)
    (S : Finset (Verts n)) :
    colorsOn (fuseSetCol c I hI) S
      = (colorsOn c S \ I) ∪ (if (colorsOn c S ∩ I).Nonempty then {I.min' hI} else ∅) := by
  ext x
  by_cases hne : (colorsOn c S ∩ I).Nonempty
  · rw [mem_colorsOn_fuseSetCol, Finset.mem_union, Finset.mem_singleton_iff, if_pos hne,
      Finset.mem_sdiff]
    constructor
    · rintro (⟨hx, hxc⟩ | rfl)
      · exact ⟨hxc, hx⟩
      · exact ⟨Or.inr ⟨y, hne.1, by rw [Finset.mem_sdiff] at hne.1; exact hne.2.2⟩⟩
    · rintro (⟨hxc, hx⟩ | ⟨y, hyc, hyI⟩)
      · exact Or.inl ⟨hx, hxc⟩
      · exact Or.inr ⟨Finset.min'_mem I hI⟩
  · rw [mem_colorsOn_fuseSetCol, Finset.mem_union, Finset.not_mem_empty, if_neg hne, false_or,
      Finset.mem_sdiff]
    constructor
    · rintro (⟨hx, hxc⟩ | hcon)
      · exact ⟨hxc, hx⟩
      · rw [Finset.not_mem_empty, false_implies] at hcon
        exact absurd hcon hne
    · rintro ⟨hxc, hx⟩
      exact Or.inl ⟨hx, hxc⟩

/-- **THE CARDINALITY EFFECT OF FUSING A SET.** -/
theorem card_colorsOn_fuseSetCol {n k : ℕ} {c : Col n k} (I : Finset (Fin k)) (hI : I.Nonempty)
    (S : Finset (Verts n)) :
    (colorsOn (fuseSetCol c I hI) S).card = (colorsOn c S).card - (colorsOn c S ∩ I).card
      + (if (colorsOn c S ∩ I).Nonempty then 1 else 0) := by
  rw [colorsOn_fuseSetCol I hI S]
  by_cases hne : (colorsOn c S ∩ I).Nonempty
  · rw [Finset.card_union_of_disjoint]
    · rw [Finset.card_sdiff (Finset.mem_univ _), Finset.card_singleton, if_pos hne]
      congr 1
      exact Nat.sub_add_cancel (Finset.card_pos.mpr hne)
    · rw [Finset.disjoint_left]
      intro x hx1 hx2
      rw [Finset.mem_singleton_iff] at hx2
      exact hne ⟨hx2, Finset.mem_sdiff.mp hx1.2⟩
  · rw [if_neg hne, Finset.card_union_of_disjoint]
    · rw [Finset.card_empty, Finset.card_sdiff (Finset.mem_univ _), Finset.card_sdiff
        (Finset.mem_univ _), add_zero]
      exact Nat.sub_add_cancel (Finset.card_pos.mpr hne)
    · rw [Finset.disjoint_left]
      rintro x ⟨hx, -⟩ hx2
      exact hne ⟨hx, hx2⟩

/-- **THE FUSION CRITERION FOR A SET OF COLOURS.**  Fusing a set `I` of colours of an admissible
colouring is admissible **iff every tight four-set meets `I` in at most one colour and every
rainbow four-set in at most two**.  This is the sharp form of the move: the four-sets with slack
(rainbow ones) may pay two colours of `I`, the tight ones only one. -/
theorem fuseSetCol_admissible_iff {n k : ℕ} {c : Col n k} (hc : Admissible c) (I : Finset (Fin k))
    (hI : I.Nonempty) :
    Admissible (fuseSetCol c I hI) ↔
      ∀ S : Finset (Verts n), S.card = 4 →
        (colorsOn c S ∩ I).card ≤ 1 + (6 - (colorsOn c S).card) := by
  constructor
  · rintro ha S hS
    have hcard := card_colorsOn_fuseSetCol I hI S
    rcases card_colorsOn_four_five_or_six hc hS with h5 | h6
    · rw [h5] at hcard
      have h5' := ha S hS
      rw [hcard] at h5'
      omega
    · rw [h6] at hcard
      have h5' := ha S hS
      rw [hcard] at h5'
      omega
  · rintro h S hS
    rcases card_colorsOn_four_five_or_six hc hS with h5 | h6
    · have hh := h S hS h5
      rw [h5] at hh
      have hcard := card_colorsOn_fuseSetCol I hI S
      rw [h5] at hcard
      omega
    · have hh := h S hS h6
      rw [h6] at hh
      have hcard := card_colorsOn_fuseSetCol I hI S
      rw [h6] at hcard
      omega

/-- **NO TIGHT FOUR-SET MEETS `I` ⇒ THE FUSION OF `I` IS ADMISSIBLE**: merging colours which only
meet rainbow four-sets is always safe. -/
theorem fuseSetCol_admissible_of_disjoint {n k : ℕ} {c : Col n k} (hc : Admissible c)
    (I : Finset (Fin k)) (hI : I.Nonempty) (h : ∀ S ∈ fiveFourSets c, Disjoint (colorsOn c S) I) :
    Admissible (fuseSetCol c I hI) := by
  refine (fuseSetCol_admissible_iff hc I hI).mpr fun S hS => ?_
  rcases card_colorsOn_four_five_or_six hc hS with h5 | h6
  · have hd := h S (mem_fiveFourSets.mpr ⟨hS, h5⟩)
    rw [Finset.card_eq_zero.mpr (Finset.disjoint_left.mp hd)]
    rw [h5]
    norm_num
  · have hd := h S (mem_fiveFourSets.mpr ⟨hS, by omega⟩)
    rw [Finset.card_eq_zero.mpr (Finset.disjoint_left.mp hd)]
    rw [h6]
    omega

theorem card_colorsOn_fuseSetCol_univ_le {n k : ℕ} {c : Col n k} (I : Finset (Fin k))
    (hI : I.Nonempty) (hn : 2 ≤ n) :
    (colorsOn (fuseSetCol c I hI) (Finset.univ : Finset (Verts n))).card ≤ k - I.card + 1 := by
  have hsub : (colorsOn (fuseSetCol c I hI) (Finset.univ : Finset (Verts n)))
      ⊆ insert (I.min' hI) ((Finset.univ : Finset (Fin k)).erase I) := by
    intro x hx
    rw [colorsOn, Finset.mem_image] at hx
    obtain ⟨e, he, heq⟩ := hx
    rw [fuseSetCol_apply c I hI e] at heq
    by_cases hce : c e ∈ I
    · rw [if_pos hce] at heq
      exact Finset.mem_insert.mpr (Or.inl heq)
    · rw [if_neg hce] at heq
      exact Finset.mem_insert.mpr (Or.inr (Finset.mem_erase.mpr ⟨heq, hce⟩))
  calc (colorsOn (fuseSetCol c I hI) (Finset.univ : Finset (Verts n))).card
      ≤ (insert (I.min' hI) ((Finset.univ : Finset (Fin k)).erase I)).card :=
        Finset.card_le_card hsub
    _ = (k - I.card) + 1 := by
      rw [Finset.card_insert_of_not_mem (by simp), Finset.card_erase_of_mem
        (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, (Finset.min'_mem I hI).not⟩),
        Finset.card_sdiff (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]

/-- **THE FUSION SAVES `|I| - 1` COLOURS.**  A set of colours which no tight four-set meets can be
fused into one, improving `c` by `|I| - 1` colours. -/
theorem EG_le_of_fuseSetCol {n k : ℕ} {c : Col n k} (hc : Admissible c) (I : Finset (Fin k))
    (hI : I.Nonempty) (hn : 2 ≤ n) (h : ∀ S ∈ fiveFourSets c, Disjoint (colorsOn c S) I) :
    EG n ≤ k - I.card + 1 :=
  le_trans (EG_le_used (fuseSetCol_admissible_of_disjoint hc I hI h) hn)
    (card_colorsOn_fuseSetCol_univ_le I hI hn)

/-! ### §6  Two no-go theorems -/

theorem fuseCol_of_unused {n k : ℕ} {c : Col n k} (hc : Admissible c) (i j : Fin k)
    (hi : ∀ e, c e ≠ i) : fuseCol c i j = c := by
  funext e
  rw [fuseCol_apply]
  split
  · rename_i h
    exact absurd h (hi _)
  · rfl

theorem fuseCol_admissible_of_unused {n k : ℕ} {c : Col n k} (hc : Admissible c) (i j : Fin k)
    (hi : ∀ e, c e ≠ i) : Admissible (fuseCol c i j) := by
  rw [fuseCol_of_unused hc i j hi]
  exact hc

/-- **A COLOURING IN WHICH EVERY FOUR-SET IS TIGHT ADMITS NO FUSION AT ALL.**  If every four-set
spans exactly five colours, and both colours are used, then some four-set meets both of them, so
the fusion criterion forbids the fusion.  The densest possible four-set census is also the least
fusable one — which is why the searches of rounds 65–77 could not improve on the extremal
constructions. -/
theorem no_fusion_of_all_tight {n k : ℕ} {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n)
    (ht : ∀ S : Finset (Verts n), S.card = 4 → (colorsOn c S).card = 5) (i j : Fin k)
    (hij : i ≠ j) (hi : ∃ a b : Verts n, a ≠ b ∧ c s(a, b) = i)
    (hj : ∃ x y : Verts n, x ≠ y ∧ c s(x, y) = j) : ¬ Admissible (fuseCol c i j) := by
  obtain ⟨a, b, hab, hci⟩ := hi
  obtain ⟨x, y, hxy, hcj⟩ := hj
  have hef : s(a, b) ≠ s(x, y) := by
    rintro he
    rw [hci, hcj] at he
    exact hij he
  obtain ⟨S, hS, hsub⟩ := exists_fourSet_of_pair (Finset.card_eq_two.mpr ⟨s(a, b), s(x, y), hef, rfl⟩)
    (by
      intro g hg
      rw [Finset.mem_insert, Finset.mem_singleton] at hg
      rcases hg with rfl | rfl
      · exact offDiag_iff.mpr hab
      · exact offDiag_iff.mpr hxy) (by omega)
  rw [fuseCol_not_admissible_iff hc i j hij, Finset.nonempty_iff_ne_empty]
  refine Finset.ne_empty_iff.mpr ⟨S, ?_⟩
  rw [mem_Tight, mem_Tight]
  have h5 : (colorsOn c S).card = 5 := ht S hS
  exact ⟨hS, h5, Finset.mem_image.mpr ⟨s(a, b), hsub (Finset.mem_insert_self _ _), hci⟩,
    Finset.mem_image.mpr ⟨s(x, y), hsub (Finset.mem_insert_of_mem (Finset.mem_singleton.mpr rfl)),
      hcj⟩⟩

end JSP140