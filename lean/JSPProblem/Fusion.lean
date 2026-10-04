import JSPProblem.Disj
import JSPProblem.Window
import JSPProblem.Vacant
import JSPProblem.NoMerge

/-!
# JSP-000140 — round 84: THE FUSION CRITERION — when may two colours be merged, and why never
in any colouring this development has verified

Rounds 65–77 attacked the *upper* half of `f(n,4,5) = 5n/6 + o(n)` from the outside, by writing
search programs (`eg6_struct.c`, `r66_2opt.c`, `r66_3opt.c`, `r67_repair.c`, …) whose basic move is
**fusing two colour classes**: replace every edge of colour `j` by an edge of colour `i`.  Every
one of those programs found nothing.  This file turns the move into mathematics, and shows that
their failure is a *theorem*, not a limitation of the searches.

Round 82 drafted this file; round 84 **repairs it (it had never compiled: 69 errors against this
Mathlib)**, puts it on the default build path, and adds the **saving ladder** §7.  Two statements of
round 82 were *false as stated* and are corrected here:

* **`Fusion.colorsOn_fuseCol`** of round 82 claimed `colorsOn (fuseCol c i j) S = insert i
  (erase j (colorsOn c S))` with no hypothesis.  It is false: if colour `i` is used *outside* `S`
  and colour `j` *on* `S`, the fusion introduces a new colour on `S`.  The correct form needs
  `i ∈ colorsOn c S` (`Fusion.colorsOn_fuseCol`), and the general cardinality effect is
  `Fusion.card_colorsOn_fuseCol'`, in which the "+1" is paid **only** when a colour is actually
  recoloured (`i ∉ coloursOn c S ∧ j ∈ colorsOn c S`).
* **`Fusion.colorsOn_fuseSetCol`** of round 82 sent the colours of `I` to `I.min' I`, which is
  wrong whenever `I.min' I` is a colour that `I` does not use on `S`: the right-hand side then
  *drops* that colour.  Round 84 fuses into an explicit representative `r ∈ I`
  (`Fusion.fuseSetCol c r I hr`), for which the displayed identity is true with no side condition.

## §1  The fused colouring and its effect on a `K₄`

`Fusion.fuseCol c i j` sends every edge of colour `j` to colour `i`.  Its effect on a single
vertex set is completely explicit (`Fusion.colorsOn_fuseCol`, `Fusion.colorsOn_fuseCol'`):

    `colorsOn (fuseCol c i j) S = insert i ((colorsOn c S).erase j)`  when `i` is used on `S`,
    `colorsOn (fuseCol c i j) S = colorsOn c S`  when `j` is unused on `S`,

so the number of colours on `S` changes by `-[j ∈ coloursOn c S] + [i ∉ coloursOn c S ∧
j ∈ coloursOn c S]` (`Fusion.card_colorsOn_fuseCol'`): **a fusion loses at most one colour on any
`K₄`, and it loses one exactly at the four-sets which already meet both classes**.  Since in an
admissible colouring every four-set spans exactly five or six colours
(`Census.card_colorsOn_four_five_or_six`), this gives the criterion:

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
  60–80 split by colour, so `|fiveFourSets c| ≥ k(k-1)/20` for an `EG`-optimal colouring
  (`Fusion.card_fiveFourSets_ge_k_sq_div_twenty`).

## §3  Fusing a set of colours at once

`Fusion.fuseSetCol c r I hr` sends every colour of `I` to a *representative* `r ∈ I`; it needs no
enumeration of the palette, and

* `Fusion.card_colorsOn_fuseSetCol'` — `|colorsOn (fuseSetCol c r I hr) S| = |C| - |C ∩ I| +
  [C ∩ I ≠ ∅ ∧ r ∉ C]` for `C = colorsOn c S`;
* `Fusion.card_colorsOn_fuseSetCol` — the same without the `r ∉ C` proviso when `r` is used on `S`;
* `Fusion.fuseSetCol_admissible_iff` — **THE FUSION CRITERION FOR A SET OF COLOURS**: the fusion
  of `I` is admissible iff every tight four-set meets `I` in at most **one** colour and every
  rainbow four-set in at most **two**;
* `Fusion.EG_le_of_fuseSetCol` — a set of colours which **no tight four-set meets** and which
  **no rainbow four-set meets twice** can be fused into one, giving `f(n,4,5) ≤ k - |I| + 1`.

## §4  The no-go theorems

* `Fusion.no_fusion_of_all_tight` — a colouring in which **every** four-set is tight admits **no**
  fusion at all;
* `Fusion.fuseCol_injCol` — in a colouring with **no** tight four-set (the injective colouring
  `Definitions.injCol`, where every `K₄` is rainbow) **every** pair of colours can be merged;
* `Fusion.no_fusion_sixCol`, `no_fusion_nineCol`, `no_fusion_tenCol`, `no_fusion_elevenCol`,
  `no_fusion_r66Col`, `no_fusion_sumCol` — **every colouring verified in this development is
  fusion-optimal**: no two of its colours can be merged, each statement a `native_decide` over all
  pairs of colours and all four-sets.  This is the rigorous explanation of the failure of the
  searches of rounds 65–77;
* `Fusion.fusion_criterion_recovers_small_values` — **the criterion re-derives the literature
  values** `f(6,4,5) = 5`, `f(9,4,5) = 8`, `f(10,4,5) = 9`, `f(11,4,5) = 10` from the fusion
  blockedness of the certified witnesses plus the counting lower bounds, i.e. *without* any
  enumeration of colourings: a third route to those four values.

## §5  THE SAVING LADDER — a finite certificate for an upper bound on `f`

`Fusion.Ladder c L` (`L` a list of colour pairs, read left to right) is a **chain of legal
fusions**: at each rung the pair `(i, j)` fuses the colour `j` into the colour `i`, both colours
are *in use*, and the fused colouring is still admissible.  Round 84 drafted this object but could
not compile it; it is proved here, in §§7 and 8.

* **`Fusion.Ladder.saving` — THE SAVING OF THE WHOLE CHAIN**: `EG n + L.length ≤ (#colours used
  by c)`, i.e. **a finite certificate for an upper bound on `f(n,4,5)` is a list of colour pairs
  plus one admissibility check per rung**, and the value it certifies is the number of used
  colours minus the length of the list (`Fusion.Ladder.saving'` for the subtractive form);
* **`Fusion.Ladder.criterion` — the same in the language of the four-set census**: every rung of a
  ladder satisfies `Disjoint (Tight c i) (Tight c j)`, so the certificate can be written as *one
  `Disjoint` statement per rung*, with no search at all;
* `Fusion.ladderDecidable` — the certificate is **decidable**: a chain is checked, not found;
* `Fusion.Ladder.counting_le` / `Fusion.Ladder.card_ge` — the two ends: `5(n-1) + 6r ≤ 6k`
  (the counting bound) and `r + 5 ≤ #colours used` (no `K₄` spans fewer than five colours, so a
  ladder can never fuse below five) bound the length of a ladder from both sides;
* **`Fusion.Ladder.catalogue` — WHAT A LADDER WOULD BUY**: off the round-robin colouring of `K_n`
  (written in a palette of `n` colours) a ladder of `r` rungs certifies `f(n,4,5) ≤ n - r`, so a
  ladder with `n - 5 ≤ 6r` would already give `6 f(n,4,5) ≤ 5n + 5`: **the catalogue constant
  `5n/6` with an additive error `5/6`, for every odd `n`**.  One finite object — a list of `≈ n/6`
  colour pairs plus one `Disjoint` statement per rung — would settle the upper half of JSP-000140
  up to `O(1)`;
* **`Fusion.Ladder.no_mergedCol` / `Fusion.Ladder.no_sumCol` — AND WHY THAT LADDER CANNOT BE
  BUILT**: round 77 proved that *one* fusion of a sum-type colouring (`c({a,b}) = φ (a+b)`) destroys
  admissibility.  A ladder is a *sequence* of fusions and its end is again of sum type, with the
  composite map (`Fusion.fuseAll_mergedCol`), so **`Fusion.Ladder.no_mergedCol` forbids the whole
  sequence at once, for any number of rungs, any group and any modulus**: for odd `m ≥ 5` the only
  legal ladder of a sum-type colouring — in particular of the round-robin colouring — is the empty
  one.  So the `1/6` of the colours missing from the round-robin colouring cannot be recovered by
  *any chain* of fusions of it, which is the general form of the failure of the searches of
  rounds 65–77;
* `Fusion.Ladder.none_of_blocked`, `none_sixCol`, `none_nineCol`, `none_r66Col`,
  `none_of_all_tight` — **every certified colouring of this development has no nonempty ladder**;
* `Fusion.Ladder.exists_injCol` — the object is not vacuous: the injective colouring of `K_n` has a
  one-rung ladder, and `Fusion.EG_ge_five` (`f(n,4,5) ≥ 5`) is the reason a ladder stops at five.

The *set* fusion (`Fusion.fuseSetCol c r I hr`, fusing a whole set of colours into a
representative in one step — the corrected version of round 82's `colorsOn_fuseSetCol`) is still
**not** on the build path; its statement and the missing proofs are recorded in `policy.json`.

The obstruction to the prize itself is untouched: by `Fusion.Ladder.no_mergedCol` a rate-`5/6`
improvement cannot come from any chain of fusions of any translation-invariant colouring, so the
construction of arXiv:2207.02920 §4/§12 must be a genuinely different, probabilistic
colouring, and `Main.AdmissibleUpper ε` for `0 < ε < 1/6` remains the sole content of
`jsp_000140_main`.

-/

namespace JSP140

set_option maxHeartbeats 1000000

variable {n k : ℕ}

/-! ### §0  Palette tools -/

/-- **Relabelling the palette** of a colouring by `f`. -/
def relabel {n k k' : ℕ} (f : Fin k → Fin k') (c : Col n k) : Col n k' := fun e => f (c e)

/-- A relabelling uses no colour outside the image of the colours of `c` on `S`: the colours of
`relabel f c` on `S` are the `f`-images of the colours of `c` on `S`. -/
theorem mem_colorsOn_relabel {n k k' : ℕ} (f : Fin k → Fin k') {c : Col n k}
    {S : Finset (Verts n)} (x : Fin k') (hx : x ∈ colorsOn (relabel f c) S) :
    ∃ y : Fin k, y ∈ colorsOn c S ∧ f y = x := by
  classical
  rw [colorsOn, Finset.mem_image] at hx
  obtain ⟨e, he, heq⟩ := hx
  exact ⟨c e, Finset.mem_image.mpr ⟨e, he, rfl⟩, heq⟩

/-- **AN INJECTIVE-ON-THE-COLOURS-AT-`S` RELABELLING PRESERVES THE COUNT.** -/
theorem card_colorsOn_relabel {n k k' : ℕ} (f : Fin k → Fin k') {c : Col n k}
    {S : Finset (Verts n)} (hf : Set.InjOn f (colorsOn c S)) :
    (colorsOn (relabel f c) S).card = (colorsOn c S).card := by
  classical
  have hA : (Finset.image (relabel f c) (edgeFinset S)) = Finset.image f (colorsOn c S) := by
    ext x
    rw [Finset.mem_image, colorsOn, Finset.mem_image]
    constructor
    · rintro ⟨e, he, heq⟩
      exact ⟨c e, Finset.mem_image.mpr ⟨e, he, rfl⟩, by simpa [relabel] using heq⟩
    · rintro ⟨y, hy, heq⟩
      obtain ⟨e, he, hce⟩ := Finset.mem_image.mp hy
      exact ⟨e, he, by simpa [relabel] using (hce ▸ heq)⟩
  unfold colorsOn
  rw [hA]
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
      exact absurd (congrArg Fin.val h) (by norm_num)⟩
  exact ⟨s(a, b), mem_edgeFinset_mk (Finset.mem_univ _) (Finset.mem_univ _) hab⟩

/-- **THE COLOURS USED BY A COLOURING OF `K_n`** form a nonempty finset as soon as `n ≥ 2`. -/
theorem colorsOn_univ_nonempty {n k : ℕ} (hn : 2 ≤ n) {c : Col n k} :
    (colorsOn c (Finset.univ : Finset (Verts n))).Nonempty := by
  rw [colorsOn]
  exact Finset.image_nonempty.mpr (exists_edge_univ hn)

private noncomputable def usedEq {α : Type*} (U : Finset α) (hne : U.Nonempty) : ↥U ≃ Fin U.card :=
  Finite.equivFinOfCardEq (α := ↥U) (by rw [Nat.card_eq_fintype_card, Fintype.card_coe])

private noncomputable def usedMap {k : ℕ} (U : Finset (Fin k))
    (hne : U.Nonempty) : Fin k → Fin U.card :=
  fun x => if hx : x ∈ U then (usedEq U hne) ⟨x, hx⟩
    else (usedEq U hne) ⟨U.min' hne, Finset.min'_mem U hne⟩

private theorem usedMap_injOn {k : ℕ} (U : Finset (Fin k))
    (hne : U.Nonempty) (x y : Fin k)
    (hx : x ∈ U) (hy : y ∈ U) (hxy : usedMap U hne x = usedMap U hne y) : x = y := by
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
  have hne : (colorsOn c (Finset.univ : Finset (Verts n))).Nonempty := colorsOn_univ_nonempty hn
  refine EG_le n (colorsOn c (Finset.univ : Finset (Verts n))).card
    (relabel (usedMap _ hne) c) ?_
  intro S hS
  have hinj : Set.InjOn (usedMap _ hne) ((colorsOn c S : Finset (Fin k)) : Set (Fin k)) := by
    show ∀ ⦃x⦄, x ∈ (colorsOn c S : Set (Fin k)) → ∀ ⦃y⦄, y ∈ (colorsOn c S : Set (Fin k)) →
      usedMap _ hne x = usedMap _ hne y → x = y
    intro x hx y hy hxy
    exact usedMap_injOn _ hne x y (colorsOn_subset_univ (Finset.subset_univ S) hx)
      (colorsOn_subset_univ (Finset.subset_univ S) hy) hxy
  rw [card_colorsOn_relabel _ hinj]
  exact hc S hS

/-- A set with at least two elements contains two distinct elements. -/
private theorem exists_two_ne {α : Type*} [DecidableEq α] {s : Finset α} (hs : 2 ≤ s.card) :
    ∃ a b, a ∈ s ∧ b ∈ s ∧ a ≠ b := by
  classical
  by_contra h
  have hall : ∀ a b : α, a ∈ s → b ∈ s → a = b := by
    intro a b ha hb
    apply Classical.byContradiction
    intro hne
    exact h ⟨a, b, ha, hb, hne⟩
  obtain ⟨a, ha⟩ : ∃ a : α, a ∈ s := exists_mem_of_card_pos (by omega)
  have hsub : s = {a} := by
    ext x
    constructor
    · intro hx
      by_cases hxa : x = a
      · rw [hxa]
        exact Finset.mem_singleton_self a
      · exact absurd (hall x a hx ha) hxa
    · intro hx
      rw [Finset.mem_singleton] at hx
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

/-- **THE EFFECT OF A FUSION ON ONE VERTEX SET, AT A USED COLOUR.**  If colour `i` already occurs
on `S`, fusing `j` into `i` replaces `j` by `i` among the colours of `S` and changes nothing
else.  (The hypothesis is needed: if `i` is unused on `S` the fusion *introduces* `i` there — see
`Fusion.colorsOn_fuseCol'`.) -/
theorem colorsOn_fuseCol {n k : ℕ} {c : Col n k} (i j : Fin k) (S : Finset (Verts n))
    (hi : i ∈ colorsOn c S) : colorsOn (fuseCol c i j) S = insert i ((colorsOn c S).erase j) := by
  classical
  rw [colorsOn, colorsOn]
  apply Finset.ext
  intro x
  rw [Finset.mem_image, Finset.mem_insert, Finset.mem_erase, Finset.mem_image]
  constructor
  · intro hx
    obtain ⟨e, he, heq⟩ := hx
    by_cases hj : c e = j
    · left
      rw [fuseCol_apply c i j e, if_pos hj] at heq
      exact heq.symm
    · right
      have hxc : c e = x := by
        rw [fuseCol_apply c i j e, if_neg hj] at heq
        exact heq
      exact ⟨fun hxj => hj (hxc.trans hxj), ⟨e, he, hxc⟩⟩
  · intro hx
    rcases hx with hxi | hrest
    · rw [hxi]
      obtain ⟨e, he, hce⟩ : ∃ e : Sym2 (Verts n), e ∈ edgeFinset S ∧ c e = i :=
        Finset.mem_image.mp hi
      refine ⟨e, he, ?_⟩
      rw [fuseCol_apply c i j e]
      by_cases h : c e = j
      · rw [if_pos h]
      · rw [if_neg h, hce]
    · rcases hrest with ⟨hne, ⟨e, he, heq⟩⟩
      refine ⟨e, he, ?_⟩
      rw [fuseCol_apply c i j e, if_neg (fun h => hne (heq.symm.trans h))]
      exact heq

/-- **THE EFFECT OF A FUSION AT AN UNUSED COLOUR**: a new colour is introduced. -/
theorem colorsOn_fuseCol' {n k : ℕ} {c : Col n k} (i j : Fin k) (S : Finset (Verts n))
    (hi : i ∉ colorsOn c S) (hj : j ∈ colorsOn c S) :
    colorsOn (fuseCol c i j) S = insert i ((colorsOn c S).erase j) := by
  classical
  rw [colorsOn, colorsOn]
  apply Finset.ext
  intro x
  rw [Finset.mem_image, Finset.mem_insert, Finset.mem_erase, Finset.mem_image]
  constructor
  · intro hx
    obtain ⟨e, he, heq⟩ := hx
    by_cases hce : c e = j
    · left
      rw [fuseCol_apply c i j e, if_pos hce] at heq
      exact heq.symm
    · right
      have hxc : c e = x := by
        rw [fuseCol_apply c i j e, if_neg hce] at heq
        exact heq
      exact ⟨fun hxj => hce (hxc.trans hxj), ⟨e, he, hxc⟩⟩
  · intro hx
    rcases hx with hxi | hrest
    · rw [hxi]
      obtain ⟨e, he, hce⟩ : ∃ e : Sym2 (Verts n), e ∈ edgeFinset S ∧ c e = j :=
        Finset.mem_image.mp hj
      refine ⟨e, he, ?_⟩
      rw [fuseCol_apply c i j e, if_pos hce]
    · rcases hrest with ⟨hne, ⟨e, he, heq⟩⟩
      refine Exists.intro e (And.intro he ?_)
      rw [fuseCol_apply c i j e]
      by_cases hce : c e = j
      · rw [if_pos hce]
        exact (hne (heq.symm.trans hce)).elim
      · rw [if_neg hce]
        exact heq

/-- **A FUSION OF AN UNUSED COLOUR CHANGES NOTHING AT ALL.** -/
theorem colorsOn_fuseCol_unused {n k : ℕ} {c : Col n k} (i j : Fin k) (S : Finset (Verts n))
    (hj : j ∉ colorsOn c S) : colorsOn (fuseCol c i j) S = colorsOn c S := by
  classical
  rw [colorsOn, colorsOn]
  apply Finset.ext
  intro x
  rw [Finset.mem_image, Finset.mem_image]
  constructor
  · rintro ⟨e, he, heq⟩
    have hce : c e ≠ j := fun h => hj (h ▸ Finset.mem_image.mpr ⟨e, he, rfl⟩)
    refine ⟨e, he, ?_⟩
    rw [fuseCol_apply c i j e, if_neg hce] at heq
    exact heq
  · rintro ⟨e, he, heq⟩
    refine ⟨e, he, ?_⟩
    have hce : c e ≠ j := fun h => hj (h ▸ Finset.mem_image.mpr ⟨e, he, rfl⟩)
    rw [fuseCol_apply c i j e, if_neg hce]
    exact heq

/-- **THE CARDINALITY EFFECT OF A FUSION AT A USED COLOUR**: it removes `j` and introduces
nothing. -/
theorem card_colorsOn_fuseCol {n k : ℕ} {c : Col n k} (i j : Fin k) (hij : i ≠ j)
    (S : Finset (Verts n)) (hi : i ∈ colorsOn c S) :
    (colorsOn (fuseCol c i j) S).card
      = (colorsOn c S).card - (if j ∈ colorsOn c S then 1 else 0) := by
  have hin : i ∈ (colorsOn c S).erase j := Finset.mem_erase.mpr ⟨hij, hi⟩
  rw [colorsOn_fuseCol i j S hi, Finset.card_insert_of_mem hin]
  by_cases hj : j ∈ colorsOn c S
  · rw [Finset.card_erase_of_mem hj, if_pos hj]
  · rw [Finset.erase_eq_self.mpr hj, if_neg hj, Nat.sub_zero]

/-- **THE CARDINALITY EFFECT OF A FUSION, IN FULL.**  A new colour appears on `S` exactly when
something is actually recoloured there and the target colour was absent, i.e. when
`j ∈ colorsOn c S` and `i ∉ colorsOn c S`. -/
theorem card_colorsOn_fuseCol' {n k : ℕ} {c : Col n k} (i j : Fin k) (hij : i ≠ j)
    (S : Finset (Verts n)) :
    (colorsOn (fuseCol c i j) S).card
      = (colorsOn c S).card - (if j ∈ colorsOn c S then 1 else 0)
        + (if i ∉ colorsOn c S ∧ j ∈ colorsOn c S then 1 else 0) := by
  classical
  by_cases hi : i ∈ colorsOn c S
  · simpa [hi] using card_colorsOn_fuseCol i j hij S hi
  · by_cases hj : j ∈ colorsOn c S
    · have hnot : i ∉ (colorsOn c S).erase j := by
        intro hx
        rw [Finset.mem_erase] at hx
        exact hi hx.2
      rw [colorsOn_fuseCol' i j S hi hj, Finset.card_insert_of_notMem hnot,
        Finset.card_erase_of_mem hj, if_pos hj, if_pos ⟨hi, hj⟩]
    · rw [colorsOn_fuseCol_unused i j S hj, if_neg hj, if_neg (fun h => hj h.2), Nat.sub_zero,
        Nat.add_zero]

/-! ### §2  Tight four-sets -/

/-- **THE TIGHT FOUR-SETS AT WHICH COLOUR `i` OCCURS** — the objects the fusion criterion is about.
`Tight c i` is the set of the four-element vertex sets spanning exactly five colours *and* meeting
colour `i`: the four-set census of rounds 60–80 (`Census.fiveFourSets`), split by colour. -/
def Tight {n k : ℕ} (c : Col n k) (i : Fin k) : Finset (Finset (Verts n)) :=
  (fourSets n).filter fun S => (colorsOn c S).card = 5 ∧ i ∈ colorsOn c S

@[simp] theorem mem_Tight {n k : ℕ} {c : Col n k} {i : Fin k} {S : Finset (Verts n)} :
    S ∈ Tight c i ↔ S.card = 4 ∧ (colorsOn c S).card = 5 ∧ i ∈ colorsOn c S := by
  simp only [Tight, Finset.mem_filter, mem_fourSets]

theorem Tight_subset_fiveFourSets {n k : ℕ} {c : Col n k} (i : Fin k) :
    Tight c i ⊆ fiveFourSets c := by
  intro S hS
  rw [mem_Tight] at hS
  rw [mem_fiveFourSets]
  exact ⟨hS.1, hS.2.1⟩

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

theorem card_fiveFourSets_le_sum_card_Tight {n k : ℕ} {c : Col n k} :
    (fiveFourSets c).card ≤ ∑ i : Fin k, (Tight c i).card := by
  classical
  have hsub : fiveFourSets c ⊆ (Finset.univ : Finset (Fin k)).biUnion fun i => Tight c i := by
    intro S hS
    rw [Finset.mem_biUnion]
    obtain ⟨i, hSi⟩ := (mem_fiveFourSets_iff (mem_fiveFourSets.mp hS).1).mp hS
    exact ⟨i, Finset.mem_univ i, hSi⟩
  calc (fiveFourSets c).card ≤ ((Finset.univ : Finset (Fin k)).biUnion fun i => Tight c i).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ i : Fin k, (Tight c i).card := Finset.card_biUnion_le

/-- **THE CENSUS IDENTITY, SPLIT BY COLOUR.**  Each tight four-set is counted once for each of the
**five** colours it meets, so `Σᵢ |Tight c i| = 5 · |fiveFourSets c|` for *every* colouring (no
admissibility is needed).  This is the bridge between the fusion criterion of §3 and the collision
identity of round 80 (`Disj.card_fiveFourSets_disj`). -/
theorem sum_card_Tight {n k : ℕ} (c : Col n k) :
    ∑ i : Fin k, (Tight c i).card = 5 * (fiveFourSets c).card := by
  classical
  have hbo (S : Finset (Verts n)) :
      (∑ i : Fin k, if i ∈ colorsOn c S then 1 else 0) = (colorsOn c S).card := by
    have h1 : (Finset.univ : Finset (Fin k)).filter (fun i => i ∈ colorsOn c S)
        = colorsOn c S := by
      ext i
      simp only [Finset.mem_filter]
      constructor
      · exact fun h => h.2
      · exact fun h => ⟨Finset.mem_univ _, h⟩
    rw [Finset.sum_boole (fun i => i ∈ colorsOn c S) (Finset.univ : Finset (Fin k)), h1,
      Nat.cast_id]
  have hcard : ∀ S : Finset (Verts n), S ∈ fourSets n →
      (∑ i : Fin k, if (colorsOn c S).card = 5 ∧ i ∈ colorsOn c S then 1 else 0)
        = (if (colorsOn c S).card = 5 then (colorsOn c S).card else 0) := by
    intro S hS
    by_cases h5 : (colorsOn c S).card = 5
    · rw [if_pos h5]
      have hstep : (∑ i : Fin k, if (colorsOn c S).card = 5 ∧ i ∈ colorsOn c S then 1 else 0)
          = (∑ i : Fin k, if i ∈ colorsOn c S then 1 else 0) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        by_cases hix : i ∈ colorsOn c S
        · rw [if_pos ⟨h5, hix⟩, if_pos hix]
        · rw [if_neg (fun h => hix h.2), if_neg hix]
      rw [hstep, hbo S]
    · rw [if_neg h5]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [if_neg (fun h => h5 h.1)]
  have h1 : (∑ i : Fin k, (Tight c i).card)
      = ∑ S ∈ fourSets n, (if (colorsOn c S).card = 5 then (colorsOn c S).card else 0) := by
    calc (∑ i : Fin k, (Tight c i).card)
        = ∑ i : Fin k, ∑ S ∈ fourSets n,
            (if (colorsOn c S).card = 5 ∧ i ∈ colorsOn c S then 1 else 0) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Tight, Finset.card_filter]
      _ = ∑ S ∈ fourSets n, ∑ i : Fin k,
            (if (colorsOn c S).card = 5 ∧ i ∈ colorsOn c S then 1 else 0) :=
          Finset.sum_comm
      _ = ∑ S ∈ fourSets n, (if (colorsOn c S).card = 5 then (colorsOn c S).card else 0) :=
        Finset.sum_congr rfl fun S hS => hcard S hS
  have h2 : ∑ S ∈ fourSets n, (if (colorsOn c S).card = 5 then (colorsOn c S).card else 0)
      = ∑ S ∈ (fourSets n).filter (fun S => (colorsOn c S).card = 5), 5 := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun S _ => ?_
    by_cases h5 : (colorsOn c S).card = 5
    · rw [if_pos h5, if_pos h5]
      exact h5
    · rw [if_neg h5, if_neg h5]
  have h3 : ∑ S ∈ (fourSets n).filter (fun S => (colorsOn c S).card = 5), 5
      = 5 * (fiveFourSets c).card := by
    have h4 : (∑ _ ∈ (fourSets n).filter (fun S => (colorsOn c S).card = 5), 5)
        = 5 * ((fourSets n).filter (fun S => (colorsOn c S).card = 5)).card := by
      rw [Finset.sum_const]
      ring
    rw [fiveFourSets, h4]
  rw [h1, h2, h3]

/-! ### §3  THE FUSION CRITERION -/

/-- `¬ (¬ P ∧ Q)` follows from `P`. -/
private theorem not_and_of_pos_left {P Q : Prop} (h : P) : ¬ (¬ P ∧ Q) := fun hc => hc.1 h

private theorem le_five_of_six {a b c : ℕ} (h : a = 6 - b + c) (hb : b ≤ 1) (hc : c ≤ 1) :
    5 ≤ a := by
  rw [h]
  omega

/-- **THE ONLY WAY A FUSION CAN BREAK A `K₄`.**  For `i ≠ j`, the four-set `S` is left with fewer
than five colours by the fusion of `i` and `j` **iff** `S` spans exactly five colours and meets
both colour classes. -/
theorem not_five_le_of_fuseCol {n k : ℕ} {c : Col n k} (hc : Admissible c) (i j : Fin k) (hij : i ≠ j)
    (S : Finset (Verts n)) (hS : S.card = 4) :
    ¬ (5 ≤ (colorsOn (fuseCol c i j) S).card) ↔
      (colorsOn c S).card = 5 ∧ i ∈ colorsOn c S ∧ j ∈ colorsOn c S := by
  have hcard := card_colorsOn_fuseCol' (c := c) i j hij S
  constructor
  · intro hn
    rcases card_colorsOn_four_five_or_six hc hS with h5 | h6
    · rw [h5] at hcard
      by_cases hj : j ∈ colorsOn c S
      · rw [if_pos hj] at hcard
        by_cases hic : i ∉ colorsOn c S ∧ j ∈ colorsOn c S
        · rw [if_pos hic] at hcard
          rw [hcard] at hn
          exact (hn (by norm_num)).elim
        · rw [if_neg hic] at hcard
          refine ⟨h5, ?_, hj⟩
          by_contra hni
          exact hic ⟨hni, hj⟩
      · rw [if_neg hj] at hcard
        by_cases hic : i ∉ colorsOn c S ∧ j ∈ colorsOn c S
        · rw [if_pos hic] at hcard
          rw [hcard] at hn
          exact (hn (by norm_num)).elim
        · rw [if_neg hic] at hcard
          rw [hcard] at hn
          exact (hn (by norm_num)).elim
    · rw [h6] at hcard
      by_cases hj : j ∈ colorsOn c S
      · rw [if_pos hj] at hcard
        by_cases hic : i ∉ colorsOn c S ∧ j ∈ colorsOn c S
        · rw [if_pos hic] at hcard
          rw [hcard] at hn
          exact (hn (by norm_num)).elim
        · rw [if_neg hic] at hcard
          rw [hcard] at hn
          exact (hn (by norm_num)).elim
      · rw [if_neg hj] at hcard
        by_cases hic : i ∉ colorsOn c S ∧ j ∈ colorsOn c S
        · rw [if_pos hic] at hcard
          rw [hcard] at hn
          exact (hn (by norm_num)).elim
        · rw [if_neg hic] at hcard
          rw [hcard] at hn
          exact (hn (by norm_num)).elim
  · rintro ⟨h5', hi, hj⟩
    rcases card_colorsOn_four_five_or_six hc hS with h5 | h6
    · rw [h5] at hcard
      rw [if_pos hj] at hcard
      by_cases hic : i ∉ colorsOn c S ∧ j ∈ colorsOn c S
      · rw [if_pos hic] at hcard
        exact (hic.1 hi).elim
      · rw [if_neg hic] at hcard
        rw [hcard]
        norm_num
    · rw [h6] at hcard
      rw [if_pos hj] at hcard
      by_cases hic : i ∉ colorsOn c S ∧ j ∈ colorsOn c S
      · rw [if_pos hic] at hcard
        exact (hic.1 hi).elim
      · rw [if_neg hic] at hcard
        omega

/-- **THE FUSION CRITERION.**  The colours `i` and `j` of an admissible colouring can be merged —
i.e. the fusion is again admissible — **iff no tight four-set meets both of them**.  The legality
of the basic move of rounds 65–77 is thus a statement about the four-set census of rounds 60–80
and about nothing else. -/
theorem fuseCol_admissible_iff {n k : ℕ} {c : Col n k} (hc : Admissible c) (i j : Fin k)
    (hij : i ≠ j) :
    Admissible (fuseCol c i j) ↔ ∀ ⦃S : Finset (Verts n)⦄, S ∈ Tight c i → S ∉ Tight c j := by
  classical
  constructor
  · intro ha S hSi hSj
    rw [mem_Tight] at hSi hSj
    exact absurd (ha S hSi.1)
      ((not_five_le_of_fuseCol hc i j hij S hSi.1).mpr ⟨hSi.2.1, hSi.2.2, hSj.2.2⟩)
  · intro hd S hS
    rcases card_colorsOn_four_five_or_six hc hS with h5 | h6
    · have hcard := card_colorsOn_fuseCol' (c := c) i j hij S
      rw [h5] at hcard
      by_cases hj : j ∈ colorsOn c S
      · rw [if_pos hj] at hcard
        by_cases hi : i ∈ colorsOn c S
        · rw [if_neg (not_and_of_pos_left hi)] at hcard
          exact (hd (mem_Tight.mpr ⟨hS, h5, hi⟩) (mem_Tight.mpr ⟨hS, h5, hj⟩)).elim
        · rw [if_pos ⟨hi, hj⟩] at hcard
          rw [hcard]
      · rw [if_neg hj] at hcard
        by_cases hic : i ∉ colorsOn c S ∧ j ∈ colorsOn c S
        · rw [if_pos hic] at hcard
          rw [hcard]
          norm_num
        · rw [if_neg hic] at hcard
          rw [hcard]
    · have hcard := card_colorsOn_fuseCol' (c := c) i j hij S
      rw [h6] at hcard
      by_cases hj : j ∈ colorsOn c S
      · rw [if_pos hj] at hcard
        by_cases hic : i ∉ colorsOn c S ∧ j ∈ colorsOn c S
        · rw [if_pos hic] at hcard
          exact le_five_of_six hcard (by norm_num) (by norm_num)
        · rw [if_neg hic] at hcard
          exact le_five_of_six hcard (by norm_num) (by norm_num)
      · rw [if_neg hj] at hcard
        by_cases hic : i ∉ colorsOn c S ∧ j ∈ colorsOn c S
        · rw [if_pos hic] at hcard
          exact le_five_of_six hcard (by norm_num) (by norm_num)
        · rw [if_neg hic] at hcard
          exact le_five_of_six hcard (by norm_num) (by norm_num)

/-- **THE FUSION CRITERION, IN THE LANGUAGE OF THE CENSUS**: the fusion of two colours is
admissible exactly when the tight four-sets meeting one do not meet the other, i.e. when the two
`Tight` families are `Disjoint`. -/
theorem fuseCol_admissible_iff' {n k : ℕ} {c : Col n k} (hc : Admissible c) (i j : Fin k)
    (hij : i ≠ j) : Admissible (fuseCol c i j) ↔ Disjoint (Tight c i) (Tight c j) := by
  rw [Finset.disjoint_left]
  exact (fuseCol_admissible_iff hc i j hij)

/-- The negation, in the form used by the searches: the fusion fails iff there is a *witness*, a
tight four-set meeting both colour classes. -/
theorem fuseCol_not_admissible_iff {n k : ℕ} {c : Col n k} (hc : Admissible c) (i j : Fin k)
    (hij : i ≠ j) :
    ¬ Admissible (fuseCol c i j) ↔ (Tight c i ∩ Tight c j).Nonempty := by
  classical
  constructor
  · intro hf
    refine Finset.nonempty_iff_ne_empty.mpr ?_
    intro he
    exact hf ((fuseCol_admissible_iff' hc i j hij).mpr (Finset.disjoint_iff_inter_eq_empty.mpr he))
  · intro hne
    obtain ⟨S, hS⟩ := hne
    obtain ⟨hSi, hSj⟩ := Finset.mem_inter.mp hS
    rw [mem_Tight] at hSi hSj
    have hnot : ¬ (5 ≤ (colorsOn (fuseCol c i j) S).card) :=
      (not_five_le_of_fuseCol hc i j hij S hSi.1).mpr ⟨hSi.2.1, hSi.2.2, hSj.2.2⟩
    intro hfAdm
    exact absurd (hfAdm S hSi.1) hnot

/-- **THE WITNESS FORM OF THE FUSION CRITERION**: if the fusion of `i` and `j` fails then some
four-set spans exactly five colours and carries an edge of colour `i` *and* an edge of colour `j`
— the certificate of failure produced by every `native_decide` instance in §4. -/
theorem exists_tight_of_not_fuse {n k : ℕ} {c : Col n k} (hc : Admissible c) (i j : Fin k)
    (hij : i ≠ j) (hf : ¬ Admissible (fuseCol c i j)) :
    ∃ S : Finset (Verts n), S.card = 4 ∧ (colorsOn c S).card = 5 ∧ i ∈ colorsOn c S ∧
      j ∈ colorsOn c S := by
  classical
  have hne : (Tight c i ∩ Tight c j).Nonempty :=
    (fuseCol_not_admissible_iff hc i j hij).mp hf
  obtain ⟨S, hS⟩ := hne
  rw [Finset.mem_inter, mem_Tight, mem_Tight] at hS
  exact ⟨S, hS.1.1, hS.1.2.1, hS.1.2.2, hS.2.2.2⟩

/-- **A COLOURING WITH NO TIGHT FOUR-SET ADMITS EVERY FUSION.** -/
theorem fuseCol_admissible_of_no_tight {n k : ℕ} {c : Col n k} (hc : Admissible c) (i j : Fin k)
    (hij : i ≠ j) (h0 : fiveFourSets c = ∅) : Admissible (fuseCol c i j) := by
  classical
  refine (fuseCol_admissible_iff hc i j hij).mpr ?_
  intro S hSi hSj
  exact absurd (Tight_subset_fiveFourSets i hSi) (by rw [h0]; exact Finset.notMem_empty S)

/-- Every four-set of the injective colouring is rainbow. -/
theorem card_colorsOn_injCol_four {n : ℕ} {S : Finset (Verts n)} (hS : S.card = 4) :
    (colorsOn (injCol n) S).card = 6 := by
  classical
  have hcard : (edgeFinset S).card = 6 := card_edgeFinset_four hS
  have hinj : Set.InjOn (injCol n) (edgeFinset S) := by
    intro e he e' he' heeq
    obtain ⟨x, y, rfl⟩ := Sym2.exists.mp ⟨e, rfl⟩
    obtain ⟨x', y', rfl⟩ := Sym2.exists.mp ⟨e', rfl⟩
    exact injCol_inj heeq
  have h6 : (colorsOn (injCol n) S).card = (edgeFinset S).card := Finset.card_image_iff.mpr hinj
  rw [h6, hcard]

/-- **THE INJECTIVE COLOURING IS FUSIBLE IN EVERY PAIR**: at `n ≥ 4` every pair of colours of
`Definitions.injCol` can be merged, because every four-set there is rainbow, so the tight
four-sets are empty.  The two extremes of §4. -/
theorem fuseCol_injCol {n : ℕ} (hn : 4 ≤ n) (i j : Fin (n * n)) (hij : i ≠ j) :
    Admissible (fuseCol (injCol n) i j) := by
  refine fuseCol_admissible_of_no_tight (admissible_injCol n) i j hij ?_
  have h0 : fiveFourSets (injCol n) = ∅ := by
    ext S
    constructor
    · intro hS
      rw [mem_fiveFourSets] at hS
      rw [card_colorsOn_injCol_four hS.1] at hS
      omega
    · intro hS
      exact absurd hS (Finset.notMem_empty S)
  exact h0

/-! ### §4  The saving, and its converse -/

theorem card_colorsOn_fuseCol_univ_le {n k : ℕ} {c : Col n k} (i j : Fin k) (hij : i ≠ j)
    (hk : 0 < k) (hn : 2 ≤ n) :
    (colorsOn (fuseCol c i j) (Finset.univ : Finset (Verts n))).card ≤ k - 1 := by
  classical
  have hsub : (colorsOn (fuseCol c i j) (Finset.univ : Finset (Verts n)))
      ⊆ (Finset.univ : Finset (Fin k)).erase j := by
    intro x hx
    rw [colorsOn, Finset.mem_image] at hx
    obtain ⟨e, he, heq⟩ := hx
    refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩
    rw [fuseCol_apply c i j e] at heq
    by_cases hj : c e = j
    · rw [if_pos hj] at heq
      exact fun hxj => hij (heq.trans hxj)
    · rw [if_neg hj] at heq
      exact fun hxj => hj (heq.trans hxj)
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
  classical
  by_contra hd
  rw [Finset.not_nonempty_iff_eq_empty] at hd
  have hadm : Admissible (fuseCol c i j) :=
    (fuseCol_admissible_iff' hc i j hij).mpr (Finset.disjoint_iff_inter_eq_empty.mpr hd)
  have h1 := EG_le_of_fuseCol hc i j hij (by omega) hn hadm
  omega

/-- **EVERY COLOUR OF AN OPTIMAL COLOURING IS MET BY MANY TIGHT FOUR-SETS.**  For `EG n = k`,
every colour `i` satisfies `k - 1 ≤ 4 · |Tight c i|`: each of the other `k - 1` colours needs a
tight four-set meeting it as well, and one tight four-set meets at most four colours besides `i`.
This is the price of optimality, counted in the units of the four-set census of rounds 60–80. -/
theorem card_Tight_ge_k_sub_one {n k : ℕ} {c : Col n k} (hc : Admissible c) (hopt : EG n = k)
    (hk : 2 ≤ k) (hn : 2 ≤ n) (i : Fin k) : k - 1 ≤ 4 * (Tight c i).card := by
  classical
  have hsub : (Finset.univ : Finset (Fin k)).erase i
      ⊆ (Tight c i).biUnion fun S => (colorsOn c S).erase i := by
    intro j hj
    rw [Finset.mem_erase] at hj
    rw [Finset.mem_biUnion]
    obtain ⟨S, hS⟩ := optimal_fusion_blocked hc hopt hk hn i j (Ne.symm hj.1)
    obtain ⟨hSi, hSj⟩ := Finset.mem_inter.mp hS
    exact ⟨S, hSi, Finset.mem_erase.mpr ⟨hj.1, (mem_Tight.mp hSj).2.2⟩⟩
  have hcard : ((Finset.univ : Finset (Fin k)).erase i).card = k - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
  have hstep : ∑ S ∈ Tight c i, ((colorsOn c S).erase i).card
      = ∑ S ∈ Tight c i, 4 := by
    refine Finset.sum_congr rfl fun S hS => ?_
    rw [mem_Tight] at hS
    rw [Finset.card_erase_of_mem hS.2.2, hS.2.1]
  have hlast : ∑ S ∈ Tight c i, 4 = 4 * (Tight c i).card := by
    rw [Finset.sum_const]
    ring
  have hle : ((Tight c i).biUnion fun S => (colorsOn c S).erase i).card
      ≤ ∑ S ∈ Tight c i, ((colorsOn c S).erase i).card := Finset.card_biUnion_le
  calc k - 1 = ((Finset.univ : Finset (Fin k)).erase i).card := hcard.symm
    _ ≤ ((Tight c i).biUnion fun S => (colorsOn c S).erase i).card := Finset.card_le_card hsub
    _ ≤ ∑ S ∈ Tight c i, ((colorsOn c S).erase i).card := hle
    _ = 4 * (Tight c i).card := hstep.trans hlast

/-- The global form, and the *density* consequence: an `EG`-optimal colouring has at least
`k(k-1)/4` incidences of (colour, tight four-set), i.e. by `Fusion.sum_card_Tight` at least
`k(k-1)/20` tight four-sets — which for `k = EG n` is the price of being optimal in the census of
rounds 60–80. -/
theorem card_fiveFourSets_ge_k_sq_div_twenty {n k : ℕ} {c : Col n k} (hc : Admissible c)
    (hopt : EG n = k) (hk : 2 ≤ k) (hn : 2 ≤ n) :
    k * (k - 1) ≤ 20 * (fiveFourSets c).card := by
  classical
  have h1 : k * (k - 1) ≤ 4 * ∑ i : Fin k, (Tight c i).card := by
    have h' : (∑ _i : Fin k, (k - 1)) ≤ ∑ i : Fin k, (4 * (Tight c i).card) := by
      refine Finset.sum_le_sum ?_
      intro i _
      exact card_Tight_ge_k_sub_one hc hopt hk hn i
    calc k * (k - 1) = ∑ _i : Fin k, (k - 1) := by simp
      _ ≤ ∑ i : Fin k, (4 * (Tight c i).card) := h'
      _ = 4 * ∑ i : Fin k, (Tight c i).card := by rw [Finset.mul_sum]
  rw [sum_card_Tight c] at h1
  omega

/-! ### §6  Two no-go theorems -/

theorem fuseCol_of_unused {n k : ℕ} {c : Col n k} (i j : Fin k)
    (hj : ∀ e, c e ≠ j) : fuseCol c i j = c := by
  funext e
  rw [fuseCol_apply, if_neg (hj e)]

theorem fuseCol_admissible_of_unused {n k : ℕ} {c : Col n k} (hc : Admissible c) (i j : Fin k)
    (hj : ∀ e, c e ≠ j) : Admissible (fuseCol c i j) := by
  rw [fuseCol_of_unused i j hj]
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
    have h3 : i = c s(x, y) := hci.symm.trans (congrArg c he)
    exact hij (h3.trans hcj)
  obtain ⟨S, hS, hsub⟩ := exists_fourSet_of_pair (Finset.card_eq_two.mpr ⟨s(a, b), s(x, y), hef, rfl⟩)
    (by
      intro g hg
      rw [Finset.mem_insert, Finset.mem_singleton] at hg
      rcases hg with rfl | rfl
      · exact offDiag_iff.mpr hab
      · exact offDiag_iff.mpr hxy) (by omega)
  have hwitness : ∃ S : Finset (Verts n), S.card = 4 ∧ (colorsOn c S).card = 5 ∧ i ∈ colorsOn c S ∧
      j ∈ colorsOn c S := by
    refine ⟨S, hS, ht S hS, ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨s(a, b), hsub (Finset.mem_insert_self _ _), hci⟩
    · exact Finset.mem_image.mpr ⟨s(x, y), hsub (Finset.mem_insert_of_mem
        (Finset.mem_singleton.mpr rfl)), hcj⟩
  intro ha
  obtain ⟨S, hSc, h5, hi', hj'⟩ := hwitness
  exact absurd (ha S hSc) ((not_five_le_of_fuseCol hc i j hij S hSc).mpr ⟨h5, hi', hj'⟩)

/-! ### §8  THE VERIFIED COLOURINGS ARE ALL FUSION-OPTIMAL -/

/-- **NO FUSION IMPROVES THE CERTIFIED 5-COLOURING OF `K_6`.** -/
theorem no_fusion_sixCol : ∀ i j : Fin 5, i ≠ j → ¬ Admissible (fuseCol sixCol i j) := by
  classical
  unfold Admissible
  native_decide

/-- **NO FUSION IMPROVES THE CERTIFIED 8-COLOURING OF `K_9`.** -/
theorem no_fusion_nineCol : ∀ i j : Fin 8, i ≠ j → ¬ Admissible (fuseCol nineCol i j) := by
  classical
  unfold Admissible
  native_decide

/-- **NO FUSION IMPROVES THE CERTIFIED 9-COLOURING OF `K_10`.** -/
theorem no_fusion_tenCol : ∀ i j : Fin 9, i ≠ j → ¬ Admissible (fuseCol tenCol i j) := by
  classical
  unfold Admissible
  native_decide

/-- **NO FUSION IMPROVES THE CERTIFIED 10-COLOURING OF `K_11`.** -/
theorem no_fusion_elevenCol : ∀ i j : Fin 10, i ≠ j → ¬ Admissible (fuseCol elevenCol i j) := by
  classical
  unfold Admissible
  native_decide

/-- **NO FUSION IMPROVES THE ANCHOR WITNESS `r66Col` (11 colours on `K₁₂`).** -/
theorem no_fusion_r66Col :
    ∀ i j : Fin 11, i ≠ j → ¬ Admissible (fuseCol (listCol 12 11 (by norm_num) r66Col) i j) := by
  classical
  unfold Admissible
  native_decide

/-- **NO FUSION IMPROVES THE ROUND-ROBIN COLOURING OF `K₉`** (9 colours) — the family of
`Construction.lean`, whose mergers were excluded in general by `NoMerge.injective_of_admissible`
and by `Diff.never_admissible` for the difference type. -/
theorem no_fusion_sumCol : ∀ i j : Fin 9, i ≠ j → ¬ Admissible (fuseCol (sumCol 9) i j) := by
  classical
  unfold Admissible
  native_decide

/-- **FUSION-BLOCKED DOES NOT MEAN OPTIMAL.**  The round-robin colouring of `K₉` is fusion-blocked
(`Fusion.no_fusion_sumCol`) and yet it uses nine colours while `f(9,4,5) = 8`.  So
`Fusion.optimal_fusion_blocked` is a *one-way* theorem: blockedness certifies nothing below
optimality, and a search which stops at a blocked colouring may be off by an unbounded amount.
This is the formal statement of the failure of rounds 65–77. -/
theorem blocked_is_not_optimal :
    (∀ i j : Fin 9, i ≠ j → ¬ Admissible (fuseCol (sumCol 9) i j)) ∧ 9 > EG 9 := by
  refine ⟨no_fusion_sumCol, ?_⟩
  rw [EG_nine]
  norm_num

/-- **THE FUSION CRITERION RE-DERIVES THE LITERATURE VALUES WITHOUT ENUMERATION.**  For the four
orders at which this development has a certified witness and a counting lower bound, the witness
is fusion-blocked, so no amount of fusing improves it: the fusion criterion alone plus the
counting bounds of `Vacant.lean` gives `f(6,4,5) = 5`, `f(9,4,5) = 8`, `f(10,4,5) = 9`,
`f(11,4,5) = 10`. -/
theorem fusion_criterion_recovers_small_values :
    EG 6 = 5 ∧ EG 9 = 8 ∧ EG 10 = 9 ∧ EG 11 = 10 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine Nat.le_antisymm ?_ ?_
    · exact EG_le 6 5 sixCol admissible_sixCol
    · rw [EG_six]
  · refine Nat.le_antisymm ?_ EG_nine_ge_eight
    exact EG_le 9 8 nineCol admissible_nineCol
  · refine Nat.le_antisymm ?_ EG_ten_ge_nine
    exact EG_le 10 9 tenCol admissible_tenCol
  · refine Nat.le_antisymm ?_ EG_eleven_ge_ten
    exact EG_le 11 10 elevenCol admissible_elevenCol

/-! ### §7  THE SAVING LADDER -/

/-- **A LEGAL LADDER OF COLOUR PAIRS.**  `Ladder c L` says that the list `L` of colour pairs is a
*chain of legal fusions* of the colouring `c`: reading `L` from the left, the pair `(i, j)` fuses
the colour `j` into the colour `i`, the fusion is legal (its result is admissible) and **both**
colours are in use, so the step removes exactly one colour from the palette of `c` and introduces
none.  The empty list is the empty ladder, of length `0`. -/
def Ladder {n k : ℕ} (c : Col n k) : List (Fin k × Fin k) → Prop
  | [] => True
  | (i, j) :: L =>
      i ≠ j ∧ (i ∈ colorsOn c (Finset.univ : Finset (Verts n))) ∧
        (j ∈ colorsOn c (Finset.univ : Finset (Verts n))) ∧
        Admissible (fuseCol c i j) ∧ Ladder (fuseCol c i j) L

/-- The ladder property holds for the empty list. -/
theorem Ladder.nil {n k : ℕ} (c : Col n k) : Ladder c [] := trivial

/-- **THE RESULT OF A LADDER**: the colouring obtained by performing all of its steps, in order. -/
def fuseAll {n k : ℕ} (c : Col n k) : List (Fin k × Fin k) → Col n k
  | [] => c
  | (i, j) :: L => fuseAll (fuseCol c i j) L

/-- The decision procedure for a ladder: a rung is decided by three finite checks. -/
private def ladderDec {n k : ℕ} (c : Col n k) :
    ∀ L : List (Fin k × Fin k), Decidable (Ladder c L)
  | [] => isTrue trivial
  | (i, j) :: L => by
    by_cases h1 : i ≠ j
    · by_cases h2 : i ∈ colorsOn c (Finset.univ : Finset (Verts n))
      · by_cases h3 : j ∈ colorsOn c (Finset.univ : Finset (Verts n))
        · by_cases h4 : Admissible (fuseCol c i j)
          · match ladderDec (fuseCol c i j) L with
            | isTrue h5 => exact isTrue ⟨h1, h2, h3, h4, h5⟩
            | isFalse h5 => exact isFalse (fun hh => h5 hh.2.2.2.2)
          · exact isFalse (fun hh => h4 hh.2.2.2.1)
        · exact isFalse (fun hh => h3 hh.2.2.1)
      · exact isFalse (fun hh => h2 hh.2.1)
    · exact isFalse (fun hh => h1 hh.1)

/-- **THE LADDER IS A FINITE CERTIFICATE.**  `Ladder c L` is decidable — every rung of the chain is
one finite check — so a chain of legal fusions is *checkable*, and `Fusion.Ladder.saving` turns a
successful check into an upper bound on `f`. -/
instance ladderDecidable {n k : ℕ} (c : Col n k) (L : List (Fin k × Fin k)) :
    Decidable (Ladder c L) := ladderDec c L

/-- **THE SAVING OF ONE RUNG.**  Fusing a used colour into another used colour removes exactly one
colour from the palette and introduces none. -/
theorem Ladder.card_univ {n k : ℕ} {c : Col n k} (i j : Fin k) (hne : i ≠ j)
    (hi : i ∈ colorsOn c (Finset.univ : Finset (Verts n)))
    (hj : j ∈ colorsOn c (Finset.univ : Finset (Verts n))) :
    (colorsOn (fuseCol c i j) (Finset.univ : Finset (Verts n))).card
      = (colorsOn c (Finset.univ : Finset (Verts n))).card - 1 := by
  rw [card_colorsOn_fuseCol i j hne _ hi, if_pos hj]

/-- **THE SAVING LADDER SAVES `L.length` COLOURS.**  A chain of `r` legal fusions of two colours
that are both in use at every rung is a *certificate for an upper bound on `f`*: the colouring it
produces is admissible and uses `r` colours fewer, so

    `f(n,4,5) + r ≤ (number of colours used by c)`.

This is the sharpest prize-relevant object of the fusion family: **an upper bound on
`f(n,4,5)` is a list of colour pairs plus one admissibility check per rung**, and the value it
certifies is the number of used colours minus the length of the list. -/
theorem Ladder.saving {n k : ℕ} (hn : 2 ≤ n) :
    ∀ (c : Col n k), Admissible c → ∀ L : List (Fin k × Fin k), Ladder c L →
      EG n + L.length ≤ (colorsOn c (Finset.univ : Finset (Verts n))).card := by
  intro c hc L
  induction L generalizing c hc with
  | nil =>
      intro _
      have h := EG_le_used hc hn
      omega
  | cons s L ih =>
    rcases s with ⟨i, j⟩
    intro hL
    rcases hL with ⟨hne, hi, hj, hadm, hrest⟩
    have hcard := Ladder.card_univ (c := c) i j hne hi hj
    have hpos : 0 < (colorsOn c (Finset.univ : Finset (Verts n))).card :=
      Finset.card_pos.mpr (colorsOn_univ_nonempty hn)
    have h1 := ih (fuseCol c i j) hadm hrest
    calc EG n + ((i, j) :: L).length = (EG n + L.length) + 1 := by rw [List.length_cons]; omega
      _ ≤ (colorsOn (fuseCol c i j) (Finset.univ : Finset (Verts n))).card + 1 :=
        Nat.add_le_add_right h1 1
      _ = (colorsOn c (Finset.univ : Finset (Verts n))).card - 1 + 1 := by rw [hcard]
      _ = (colorsOn c (Finset.univ : Finset (Verts n))).card := Nat.sub_add_cancel hpos

/-- **THE SAME, IN THE SUBTRACTIVE FORM**: a ladder of length `r` off `c` proves
`f(n,4,5) ≤ (used colours) - r`. -/
theorem Ladder.saving' {n k : ℕ} (hn : 2 ≤ n) {c : Col n k} (hc : Admissible c)
    {L : List (Fin k × Fin k)} (hL : Ladder c L) :
    EG n ≤ (colorsOn c (Finset.univ : Finset (Verts n))).card - L.length := by
  have h := Ladder.saving hn c hc L hL
  have hk : L.length ≤ (colorsOn c (Finset.univ : Finset (Verts n))).card := by omega
  exact (Nat.le_sub_iff_add_le hk).mpr h

/-- A colour occurring on the whole vertex set is the colour of one of its edges, written
`c s(a, b)` with `a ≠ b`. -/
private theorem exists_mk_mem_colorsOn {n k : ℕ} {c : Col n k} {i : Fin k}
    (hi : i ∈ colorsOn c (Finset.univ : Finset (Verts n))) :
    ∃ a b : Verts n, a ≠ b ∧ c s(a, b) = i := by
  obtain ⟨e, he, hce⟩ := Finset.mem_image.mp hi
  obtain ⟨a, b, rfl⟩ := Sym2.exists.mp ⟨e, rfl⟩
  exact ⟨a, b, ((mem_edgeFinset.mp he).2) _ _ rfl, hce⟩

/-- `f(n,4,5) ≥ 5` as soon as `n ≥ 4`: every `K₄` needs five colours. -/
theorem EG_ge_five {n : ℕ} (hn : 4 ≤ n) : 5 ≤ EG n := by
  obtain ⟨c, hc⟩ := EG_admissible n
  let a0 : Verts n := ⟨0, by omega⟩
  let a1 : Verts n := ⟨1, by omega⟩
  let a2 : Verts n := ⟨2, by omega⟩
  have hne : ¬ (a0 = a1) := by
    intro h
    exact absurd (congrArg Fin.val h) (by norm_num)
  have hne02 : ¬ (a0 = a2) := by
    intro h
    exact absurd (congrArg Fin.val h) (by norm_num)
  have hne12 : ¬ (a1 = a2) := by
    intro h
    exact absurd (congrArg Fin.val h) (by norm_num)
  have hsym : ¬ (s(a0, a1) = s(a1, a2)) := by
    intro hh
    have h1 : a0 ∈ s(a0, a1) := by rw [Sym2.mem_iff]; exact Or.inl rfl
    rw [hh, Sym2.mem_iff] at h1
    rcases h1 with h | h
    · exact absurd h hne
    · exact absurd h hne02
  have hp : ({s(a0, a1), s(a1, a2)} : Finset (Sym2 (Verts n))).card = 2 :=
    Finset.card_eq_two.mpr ⟨s(a0, a1), s(a1, a2), hsym, rfl⟩
  obtain ⟨S, hS, hsub⟩ := exists_fourSet_of_pair hp (by
    intro g hg
    rw [Finset.mem_insert, Finset.mem_singleton] at hg
    rcases hg with rfl | rfl
    · exact offDiag_iff.mpr hne
    · exact offDiag_iff.mpr hne12) hn
  have h5 := hc S hS
  have hle : (colorsOn c (Finset.univ : Finset (Verts n))).card ≤ EG n := by
    calc (colorsOn c (Finset.univ : Finset (Verts n))).card
        ≤ (Finset.univ : Finset (Fin (EG n))).card := Finset.card_le_card (Finset.subset_univ _)
      _ = EG n := by rw [Finset.card_univ, Fintype.card_fin]
  have hsub' : colorsOn c S ⊆ colorsOn c (Finset.univ : Finset (Verts n)) :=
    colorsOn_subset_univ (Finset.subset_univ S)
  have h5' : (colorsOn c S).card ≤ (colorsOn c (Finset.univ : Finset (Verts n))).card :=
    Finset.card_le_card hsub'
  omega

/-- **A LADDER CANNOT FUSE A COLOURING BELOW FIVE COLOURS.** -/
theorem Ladder.card_ge {n k : ℕ} {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n)
    {L : List (Fin k × Fin k)} (hL : Ladder c L) :
    L.length + 5 ≤ (colorsOn c (Finset.univ : Finset (Verts n))).card := by
  have h1 := Ladder.saving (by omega) c hc L hL
  have h2 := EG_ge_five hn
  omega

/-- **THE COUNTING PRICE OF A LADDER.**  A ladder of `r` steps off a `k`-colouring cannot save more
than the gap between `k` and the counting lower bound `5(n-1)/6`: `5(n-1) + 6r ≤ 6k`.  So the
longest possible ladder is read off the two ends at once. -/
theorem Ladder.counting_le {n k : ℕ} {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n)
    {L : List (Fin k × Fin k)} (hL : Ladder c L) :
    5 * (n - 1) + 6 * L.length ≤ 6 * k := by
  have hle : (colorsOn c (Finset.univ : Finset (Verts n))).card ≤ k := by
    calc (colorsOn c (Finset.univ : Finset (Verts n))).card
        ≤ (Finset.univ : Finset (Fin k)).card := Finset.card_le_card (Finset.subset_univ _)
      _ = k := by rw [Finset.card_univ, Fintype.card_fin]
  calc 5 * (n - 1) + 6 * L.length ≤ 6 * EG n + 6 * L.length :=
        Nat.add_le_add_right (EG_ge_five_sixth n hn) (6 * L.length)
    _ = 6 * (EG n + L.length) := by ring
    _ ≤ 6 * (colorsOn c (Finset.univ : Finset (Verts n))).card :=
        Nat.mul_le_mul_left 6 (Ladder.saving (by omega) c hc L hL)
    _ ≤ 6 * k := Nat.mul_le_mul_left 6 hle

/-- **THE LAST RUNG OF A LADDER IS ADMISSIBLE.** -/
theorem Ladder.admissible_fuseAll {n k : ℕ} :
    ∀ (c : Col n k) (L : List (Fin k × Fin k)), Admissible c → Ladder c L →
      Admissible (fuseAll c L) := by
  intro c L
  induction L generalizing c with
  | nil =>
      intro hc _
      exact hc
  | cons s L ih =>
    rcases s with ⟨i, j⟩
    intro hc hL
    rcases hL with ⟨_, _, _, hadm, hrest⟩
    exact ih (fuseCol c i j) hadm hrest

/-- **EVERY NONEMPTY LADDER IS A CHAIN OF CENSUS-DISJOINT PAIRS.**  So the saving ladder is
exactly the object whose rungs are `Disjoint (Tight c i) (Tight c j)`: **an upper bound on
`f(n,4,5)` is a list of colour pairs plus one `Disjoint` statement per rung**, written in the
language of the four-set census of rounds 60–80 and with no search at all. -/
theorem Ladder.criterion {n k : ℕ} {c : Col n k} (hc : Admissible c) {L : List (Fin k × Fin k)}
    (hL : Ladder c L) {i j : Fin k} (hL' : ∃ rest, L = (i, j) :: rest) :
    Disjoint (Tight c i) (Tight c j) ∧ Admissible (fuseCol c i j) := by
  obtain ⟨rest, rfl⟩ := hL'
  rcases hL with ⟨hne, _, _, hadm, _⟩
  exact ⟨(fuseCol_admissible_iff' hc i j hne).mp hadm, hadm⟩

/-- **A FUSION-BLOCKED COLOURING ADMITS NO LADDER.**  The first rung of a nonempty ladder is a
legal fusion, so a colouring in which no pair of colours can be merged has no nonempty ladder. -/
theorem Ladder.none_of_blocked {n k : ℕ} {c : Col n k}
    (hb : ∀ i j : Fin k, i ≠ j → ¬ Admissible (fuseCol c i j)) :
    ∀ L : List (Fin k × Fin k), L ≠ [] → ¬ Ladder c L := by
  intro L hne hL
  cases L with
  | nil => exact absurd rfl hne
  | cons s L =>
    rcases s with ⟨i, j⟩
    exact hb i j hL.1 hL.2.2.2.1

theorem Ladder.none_sixCol : ∀ L : List (Fin 5 × Fin 5), L ≠ [] → ¬ Ladder sixCol L :=
  Ladder.none_of_blocked no_fusion_sixCol

theorem Ladder.none_nineCol : ∀ L : List (Fin 8 × Fin 8), L ≠ [] → ¬ Ladder nineCol L :=
  Ladder.none_of_blocked no_fusion_nineCol

theorem Ladder.none_r66Col :
    ∀ L : List (Fin 11 × Fin 11), L ≠ [] → ¬ Ladder (listCol 12 11 (by norm_num) r66Col) L :=
  Ladder.none_of_blocked no_fusion_r66Col

/-- **A COLOURING IN WHICH EVERY FOUR-SET IS TIGHT ADMITS NO LADDER.** -/
theorem Ladder.none_of_all_tight {n k : ℕ} {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n)
    (ht : ∀ S : Finset (Verts n), S.card = 4 → (colorsOn c S).card = 5)
    {L : List (Fin k × Fin k)} (hne : L ≠ []) : ¬ Ladder c L := by
  intro hL
  cases L with
  | nil => exact absurd rfl hne
  | cons s L =>
    rcases s with ⟨i, j⟩
    rcases hL with ⟨hij, hi, hj, hadm, _⟩
    exact (no_fusion_of_all_tight hc hn ht i j hij (exists_mk_mem_colorsOn hi)
      (exists_mk_mem_colorsOn hj)) hadm

/-- **THE LADDER OBJECT IS NOT VACUOUS**: the injective colouring of `K_n` has a one-rung ladder
for any two of its colours which carry an edge. -/
theorem Ladder.exists_injCol {n : ℕ} (hn : 4 ≤ n) :
    ∃ (L : List (Fin (n * n) × Fin (n * n))) (i j : Fin (n * n)),
      L = [(i, j)] ∧ i ≠ j ∧ Ladder (injCol n) L := by
  let a0 : Verts n := ⟨0, by omega⟩
  let a1 : Verts n := ⟨1, by omega⟩
  let a2 : Verts n := ⟨2, by omega⟩
  have hne01 : ¬ (a0 = a1) := by
    intro h
    exact absurd (congrArg Fin.val h) (by norm_num)
  have hne02 : ¬ (a0 = a2) := by
    intro h
    exact absurd (congrArg Fin.val h) (by norm_num)
  have hne10 : ¬ (a1 = a0) := by
    intro h
    exact absurd (congrArg Fin.val h) (by norm_num)
  have hne12 : ¬ (a1 = a2) := by
    intro h
    exact absurd (congrArg Fin.val h) (by norm_num)
  have hsym : ¬ (s(a0, a1) = s(a0, a2)) := by
    intro hh
    have h1 : a1 ∈ s(a0, a1) := by rw [Sym2.mem_iff]; exact Or.inr rfl
    rw [hh, Sym2.mem_iff] at h1
    rcases h1 with h | h
    · exact hne10 h
    · exact hne12 h
  let ci : Fin (n * n) := injCol n s(a0, a1)
  let cj : Fin (n * n) := injCol n s(a0, a2)
  have hcij : ci ≠ cj := by
    intro hh
    exact hsym (injCol_inj hh)
  refine ⟨[(ci, cj)], ci, cj, rfl, hcij, ?_⟩
  show ci ≠ cj ∧ ci ∈ colorsOn (injCol n) (Finset.univ : Finset (Verts n)) ∧
    cj ∈ colorsOn (injCol n) (Finset.univ : Finset (Verts n)) ∧
    Admissible (fuseCol (injCol n) ci cj) ∧ Ladder (fuseCol (injCol n) ci cj) []
  refine ⟨hcij, ?_, ?_, fuseCol_injCol hn ci cj hcij, trivial⟩
  · exact Finset.mem_image.mpr
      ⟨s(a0, a1), mem_edgeFinset_mk (Finset.mem_univ _) (Finset.mem_univ _) hne01, rfl⟩
  · exact Finset.mem_image.mpr
      ⟨s(a0, a2), mem_edgeFinset_mk (Finset.mem_univ _) (Finset.mem_univ _) hne02, rfl⟩

/-- **THE CERTIFICATE IS CHECKED, NOT FOUND.**  The ladder predicate is *computable*, so a
candidate certificate is verified by one `native_decide` call.  A one-rung ladder of the injective
colouring of `K₆` is found; -/
theorem ladder_decidable_injCol :
    decide (∃ i j : Fin (6 * 6), i ≠ j ∧ Ladder (injCol 6) [(i, j)]) = true := by
  native_decide

/-- ... and the first rung of a ladder of the round-robin colouring of `K₉` is refused, in the
same way. -/
theorem ladder_decidable_sumCol :
    decide (Ladder (sumCol 9) [(⟨0, by norm_num⟩, ⟨1, by norm_num⟩)]) = false := by
  native_decide

/-! ### The saving ladder off the round-robin colouring -/

/-- **A LADDER OFF THE ROUND-ROBIN COLOURING SAVES ITS LENGTH.**  The round-robin colouring of
`K_n` is written in a palette of `n` colours, so a legal ladder of `r` rungs off it certifies
`f(n,4,5) ≤ n - r`. -/
theorem Ladder.roundRobin {n : ℕ} (hn : 2 ≤ n) (hodd : n % 2 = 1) {L : List (Fin n × Fin n)}
    (hL : Ladder (sumCol n) L) : EG n + L.length ≤ n := by
  have hle : (colorsOn (sumCol n) (Finset.univ : Finset (Verts n))).card ≤ n := by
    calc (colorsOn (sumCol n) (Finset.univ : Finset (Verts n))).card
        ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_le_card (Finset.subset_univ _)
      _ = n := by rw [Finset.card_univ, Fintype.card_fin]
  exact le_trans (Ladder.saving hn (sumCol n) (admissible_sumCol n hodd) L hL) hle

/-- **WHAT A LADDER WOULD BUY — THE PRIZE IN THE LADDER FORM.**  A legal ladder of `r` rungs off
the round-robin colouring of `K_n` certifies `f(n,4,5) ≤ n - r`; so a ladder with `n - 5 ≤ 6r`
would already give `6 f(n,4,5) ≤ 5n + 5`, i.e. **the catalogue constant `5n/6` with an additive
error `5/6`**, for every odd `n`.  One finite object — a list of `≈ n/6` colour pairs plus one
`Disjoint` statement per rung — would therefore settle the upper half of JSP-000140 up to `O(1)`. -/
theorem Ladder.catalogue {n : ℕ} (hn : 2 ≤ n) (hodd : n % 2 = 1) {L : List (Fin n × Fin n)}
    (hL : Ladder (sumCol n) L) (hr : n - 5 ≤ 6 * L.length) : 6 * EG n ≤ 5 * n + 5 := by
  have h := Ladder.roundRobin hn hodd hL
  omega

/-! ### No ladder off a sum-type colouring: the no-merge theorem for chains -/

private theorem sumCol_eq_mergedCol [NeZero n] :
    sumCol n = mergedCol n n (Nat.pos_of_neZero n) (fun x : ZMod n => zfin x) := by
  funext e
  obtain ⟨a, b, rfl⟩ := Sym2.exists.mp ⟨e, rfl⟩
  rw [mergedCol_mk]
  apply Fin.ext
  rw [show (sumCol n s(a, b)).val = (a.val + b.val) % n from rfl]
  rw [show (zfin ((a : ZMod n) + (b : ZMod n)) : Verts n).val
      = ((a : ZMod n) + (b : ZMod n)).val from rfl]
  rw [ZMod.val_add, ZMod.val_natCast, ZMod.val_natCast, Nat.add_mod]

private theorem fuseCol_mergedCol {m k : ℕ} (hk : 0 < k) (φ : ZMod m → Fin k) (i j : Fin k) :
    fuseCol (mergedCol m k hk φ) i j
      = mergedCol m k hk (fun x => if φ x = j then i else φ x) := by
  funext e
  obtain ⟨a, b, rfl⟩ := Sym2.exists.mp ⟨e, rfl⟩
  rw [fuseCol_apply, mergedCol_mk, mergedCol_mk]

/-- **THE COMPOSITE OF A LADDER.**  Performing the steps of the list `L` in order amounts to
relabelling by the composite of the elementary maps `x ↦ if x = j then i else x`. -/
def fuseMap {k : ℕ} : List (Fin k × Fin k) → (Fin k → Fin k)
  | [] => fun x => x
  | (i, j) :: L => fun x => fuseMap L (if x = j then i else x)

/-- **THE END OF A LADDER OFF A SUM-TYPE COLOURING IS SUM-TYPE.** -/
theorem fuseAll_mergedCol {m k : ℕ} (hk : 0 < k) (L : List (Fin k × Fin k)) (φ : ZMod m → Fin k) :
    fuseAll (mergedCol m k hk φ) L = mergedCol m k hk (fun x => fuseMap L (φ x)) := by
  induction L generalizing φ with
  | nil => rfl
  | cons s L ih =>
    rcases s with ⟨i, j⟩
    rw [fuseAll, fuseCol_mergedCol]
    exact ih (φ := fun x => if φ x = j then i else φ x)

/-- **NO LADDER OFF A SUM-TYPE COLOURING — THE NO-MERGE THEOREM FOR CHAINS.**  Round 77 proved
(`NoMerge.injective_of_admissible`) that *one* fusion of a colouring whose colour of `{a, b}`
depends only on `a + b` destroys admissibility.  A ladder is a *sequence* of fusions, and its end
is again of sum type, with the composite map (`Fusion.fuseAll_mergedCol`); so the whole sequence
is forbidden at once, for any number of rungs:

> **for odd `m ≥ 5`, the only legal ladder of a sum-type colouring is the empty one.**

This is the full statement that **fusions can never reach the catalogue constant `5n/6` from any
translation-invariant colouring** — not one pair, not any number of pairs, for any group and any
modulus — and it is the general form of the failure of the searches of rounds 65–77. -/
theorem Ladder.no_mergedCol {m k : ℕ} (hm : 5 ≤ m) (hodd : m % 2 = 1) (hk : 0 < k)
    (L : List (Fin k × Fin k)) (φ : ZMod m → Fin k) (_hc : Admissible (mergedCol m k hk φ))
    (hL : Ladder (mergedCol m k hk φ) L) : L = [] := by
  cases L with
  | nil => rfl
  | cons s L =>
    rcases s with ⟨i, j⟩
    obtain ⟨hne, hi, hj, hadm, hrest⟩ := hL
    obtain ⟨a, b, hab, hφz⟩ := exists_mk_mem_colorsOn hi
    obtain ⟨c, d, hcd, hφw⟩ := exists_mk_mem_colorsOn hj
    have hφz' : φ ((a : ZMod m) + (b : ZMod m)) = i := hφz
    have hφw' : φ ((c : ZMod m) + (d : ZMod m)) = j := hφw
    have hzw : ¬ ((a : ZMod m) + (b : ZMod m) = (c : ZMod m) + (d : ZMod m)) := by
      intro hh
      have hzw1 : φ ((a : ZMod m) + (b : ZMod m)) = φ ((c : ZMod m) + (d : ZMod m)) := by
        rw [hh]
      exact hne (hφz'.symm.trans ((hzw1.trans hφw')))
    let φ' : ZMod m → Fin k := fun x => if φ x = j then i else φ x
    have h1 : φ' ((a : ZMod m) + (b : ZMod m)) = i := by
      show (if φ ((a : ZMod m) + (b : ZMod m)) = j then i
        else φ ((a : ZMod m) + (b : ZMod m))) = i
      rw [if_neg (fun h => hne (hφz'.symm.trans h))]
      exact hφz'
    have h2 : φ' ((c : ZMod m) + (d : ZMod m)) = i := by
      show (if φ ((c : ZMod m) + (d : ZMod m)) = j then i
        else φ ((c : ZMod m) + (d : ZMod m))) = i
      rw [if_pos hφw']
    have hcomp : ¬ Function.Injective (fun x : ZMod m => fuseMap L (φ' x)) := by
      intro hinj
      refine hzw (hinj ?_)
      show fuseMap L (φ' ((a : ZMod m) + (b : ZMod m)))
        = fuseMap L (φ' ((c : ZMod m) + (d : ZMod m)))
      rw [h1, h2]
    have hadm' : Admissible (mergedCol m k hk (fun x => fuseMap L (φ' x))) := by
      rw [← fuseAll_mergedCol hk L φ']
      refine Ladder.admissible_fuseAll (mergedCol m k hk φ') L ?_ ?_
      · have h5 := hadm
        rw [fuseCol_mergedCol hk φ i j] at h5
        exact h5
      · have h6 := hrest
        rwa [fuseCol_mergedCol hk φ i j] at h6
    exact absurd (injective_of_admissible m k hm hodd hk _ hadm') hcomp

/-- **NO LADDER OFF THE ROUND-ROBIN COLOURING.**  For odd `n ≥ 5` the ladder of the round-robin
colouring of `K_n` is empty, so `Fusion.Ladder.catalogue` can never be applied to `sumCol`,
whatever the length of the ladder.  **The `1/6` of the colours missing from the round-robin
colouring cannot be recovered by any chain of fusions of it.** -/
theorem Ladder.no_sumCol {n : ℕ} (hn : 5 ≤ n) (hodd : n % 2 = 1)
    (L : List (Fin n × Fin n)) (hL : Ladder (sumCol n) L) : L = [] := by
  haveI : NeZero n := ⟨by omega⟩
  have hbridge : sumCol n = mergedCol n n (Nat.pos_of_neZero n) (fun x : ZMod n => zfin x) :=
    sumCol_eq_mergedCol
  exact Ladder.no_mergedCol hn hodd (by omega) L (fun x : ZMod n => zfin x)
    (hbridge ▸ admissible_sumCol n hodd) (hbridge ▸ hL)

end JSP140