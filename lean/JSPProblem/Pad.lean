import JSPProblem.Grow

/-!
# JSP-000140 — round 69: THE PADDING CRITERION

Round 68 reduced the missing half of `f(n,4,5) = 5n/6 + o(n)` to **one local statement**
(`Grow6`: every admissible colouring of `K_m` extends to an admissible colouring of `K_{m+6}` with
five more colours) and to nothing else.  A growth lemma, however, is only as formalisable as the
description of the extension it asserts: until one can say *what the new vertices must look like*,
neither a proof nor a search certificate can be written down.

This file supplies that description.  **Growth is a padding problem, and padding has an exact
local criterion.**

## The criterion

Write the vertices of `K_{n+1}` as `Option (Verts n)`: the new vertex is `none` and the old ones
are `some a`.  Let `d` be a colouring on `Sym2 (Option (Verts n))` and let `g : Verts n → Fin j` be
the *star map* it induces, `d s(none, some a) = g a`.  Then

    `AdmOn d  ↔  OldOk d ∧ PadOk d g`

where

* `OldOk d` — every four **old** vertices still span five colours inside `d`, and
* `PadOk d g` — every **triple** `T` of old vertices satisfies
  `5 ≤ |(colours of T in d) ∪ (g[T])|`.

This is `admissible_iff_padOk`.  It is a **complete certificate**: `PadOk` is a condition on the
`n` values of `g` alone, with no mention of the extension, so the growth problem of round 68
becomes a *finite search over maps*; being a statement about explicit finsets it is also
`decidable` (`padOk_decidable`).

## What the criterion forces on the padding map

A triple carries at most three colours, so it must receive at least `5 − 3 = 2` *different* star
colours.  Hence no colour occurs three times in the star map, and:

* `padOk_fibre_le_two` — each colour is used **at most twice** in the star map;
* `padOk_image_card` — `n ≤ 2 * |g[univ]|`: the star of a new vertex sees **at least `⌈n/2⌉`
  colours**;
* `padOk_three_colours` — for `n ≥ 5` the star map takes **at least three** values, so padding one
  vertex with a two-colour star is impossible for every `n ≥ 5`;
* `padOk_fresh_half` — if the star map uses only a palette `P`, then `|P| ≥ ⌈n/2⌉`: **fresh
  colours cannot pad**.

## The price of fresh colours in the six-step route (the acceptance test)

The same pigeonhole, at any vertex of any admissible colouring (`fresh_star_le`), says: at most
`2 * |P|` edges at a vertex carry colours from a palette `P`.  Concretely (`six_step_test`): in a
growth map on `K_{m+6}` whose new palette `P` has five colours, **every new vertex has at most ten
cross edges into the old `m` vertices carrying new colours**, so at least `m − 10` of them must
reuse the old palette.  At the `K₁₂` anchor of round 68 (`m = 12`) that is **at least two** — a
falsifiable test for any growth construction, and the reason the five new colours can never do the
job alone.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

namespace JSP140

variable {n k : ℕ}

/-! ### §1  A colouring on an arbitrary finite vertex type -/

/-- The edges of the complete graph on a vertex set of an arbitrary finite type: all unordered
pairs of two **distinct** elements.  For `α = Verts n` this is `edgeFinset`. -/
def edgesOn {α : Type*} [DecidableEq α] (S : Finset α) : Finset (Sym2 α) :=
  S.sym2 \ S.image fun a => s(a, a)

/-- The colours appearing on the edges of the complete graph on `S`. -/
def colsOn {α β : Type*} [DecidableEq α] [DecidableEq β] (d : Sym2 α → β) (S : Finset α) :
    Finset β := (edgesOn S).image d

/-- **The catalog condition on an arbitrary vertex type**: every four-element vertex set spans at
least five colours.  On `α = Verts n`, `β = Fin k` this is literally `Admissible`. -/
def AdmOn {α β : Type*} [DecidableEq α] [DecidableEq β] (d : Sym2 α → β) : Prop :=
  ∀ S : Finset α, S.card = 4 → 5 ≤ (colsOn d S).card

theorem edgesOn_eq_edgeFinset (S : Finset (Verts n)) : edgesOn S = edgeFinset S := rfl

theorem colsOn_eq_colorsOn {c : Col n k} (S : Finset (Verts n)) : colsOn c S = colorsOn c S := by
  simp only [colsOn, colorsOn, edgesOn, edgeFinset, loops]

theorem AdmOn_iff {c : Col n k} : AdmOn c ↔ Admissible c := by
  constructor
  · intro h S hS
    rw [← colsOn_eq_colorsOn (c := c) S]
    exact h S hS
  · intro h S hS
    rw [colsOn_eq_colorsOn (c := c) S]
    exact h S hS

theorem mem_colsOn {α β : Type*} [DecidableEq α] [DecidableEq β] {d : Sym2 α → β} {S : Finset α}
    {x : β} :
    x ∈ colsOn d S ↔ ∃ e ∈ edgesOn S, d e = x := by
  simp only [colsOn, Finset.mem_image]

theorem mem_edgesOn {α : Type*} [DecidableEq α] {S : Finset α} {e : Sym2 α} :
    e ∈ edgesOn S ↔ e ∈ S.sym2 ∧ e ∉ S.image (fun a => s(a, a)) := by
  simp only [edgesOn, Finset.mem_sdiff]

theorem mem_edgesOn_pair {α : Type*} [DecidableEq α] {S : Finset α} {x y : α}
    (hx : x ∈ S) (hy : y ∈ S) (hne : x ≠ y) : s(x, y) ∈ edgesOn S := by
  rw [edgesOn, Finset.mem_sdiff]
  refine ⟨Finset.mk_mem_sym2_iff.mpr ⟨hx, hy⟩, fun hmem => ?_⟩
  obtain ⟨z, -, he⟩ := Finset.mem_image.mp hmem
  exact hne ((sym2_inj he).elim (fun hp => hp.1.symm.trans hp.2)
    (fun hp => hp.2.symm.trans hp.1))

theorem colsOn_mono {α β : Type*} [DecidableEq α] [DecidableEq β] {S T : Finset α} (hST : S ⊆ T)
    (d : Sym2 α → β) : colsOn d S ⊆ colsOn d T := by
  intro x hx
  obtain ⟨e, he, heq⟩ := mem_colsOn.mp hx
  obtain ⟨he1, he2⟩ := mem_edgesOn.mp he
  refine mem_colsOn.mpr ⟨e, mem_edgesOn.mpr ⟨Finset.sym2_mono hST he1, ?_⟩, heq⟩
  intro hmem
  obtain ⟨t, ht, heq'⟩ := Finset.mem_image.mp hmem
  have hts : t ∈ S := by
    rw [← heq'] at he1
    exact (Finset.mk_mem_sym2_iff.mp he1).1
  exact he2 (Finset.mem_image.mpr ⟨t, hts, heq'⟩)

theorem card_loopsOn {α : Type*} [DecidableEq α] (S : Finset α) :
    (S.image fun a => s(a, a)).card = S.card :=
  Finset.card_image_of_injective S fun {a b} h =>
    (sym2_inj h).elim (fun hp => hp.1) (fun hp => hp.1)

/-- A vertex set of `t` elements spans `choose (t+1) 2 - t` edges. -/
theorem card_edgesOn {α : Type*} [DecidableEq α] (S : Finset α) :
    (edgesOn S).card = Nat.choose (S.card + 1) 2 - S.card := by
  have hsub : S.image (fun a => s(a, a)) ⊆ S.sym2 := by
    intro e he
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp he
    exact Finset.mk_mem_sym2_iff.mpr ⟨ha, ha⟩
  rw [edgesOn, Finset.card_sdiff_of_subset hsub, Finset.card_sym2, card_loopsOn]

theorem card_edgesOn_four {α : Type*} [DecidableEq α] {S : Finset α} (hS : S.card = 4) :
    (edgesOn S).card = 6 := by
  rw [card_edgesOn, hS]
  decide

theorem card_colsOn_le {α β : Type*} [DecidableEq α] [DecidableEq β] {S : Finset α}
    (d : Sym2 α → β) {t : ℕ}
    (hS : S.card = t) : (colsOn d S).card ≤ Nat.choose (t + 1) 2 - t := by
  calc (colsOn d S).card = ((edgesOn S).image d).card := rfl
    _ ≤ (edgesOn S).card := Finset.card_image_le
    _ = Nat.choose (t + 1) 2 - t := by rw [card_edgesOn, hS]

/-- **A THREE-ELEMENT SET SPANS AT MOST THREE COLOURS.** -/
theorem card_colsOn_three {α β : Type*} [DecidableEq α] [DecidableEq β] {S : Finset α}
    (d : Sym2 α → β) (hS : S.card = 3) : (colsOn d S).card ≤ 3 := by
  calc (colsOn d S).card ≤ Nat.choose (3 + 1) 2 - 3 := card_colsOn_le d hS
    _ ≤ 3 := by decide

/-- Three pairwise distinct elements of a finset of cardinality at least three.  No order on the
ambient type is needed, which is why `ColorClass.exists_three_mem` cannot be reused on the vertex
type `Option (Verts n)` of the padding. -/
theorem exists_three_mem' {α : Type*} [DecidableEq α] {s : Finset α} (h : 3 ≤ s.card) :
    ∃ a b c : α, a ∈ s ∧ b ∈ s ∧ c ∈ s ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c := by
  obtain ⟨a, ha⟩ := s.card_pos.mp (by omega)
  have h1 : (s.erase a).card = s.card - 1 := Finset.card_erase_of_mem ha
  obtain ⟨b, hb⟩ := (s.erase a).card_pos.mp (by omega)
  have hba : b ≠ a := (Finset.mem_erase.mp hb).1
  have hbs : b ∈ s := (Finset.mem_erase.mp hb).2
  have hbm : b ∈ s.erase a := Finset.mem_erase.mpr ⟨hba, hbs⟩
  have h2 : ((s.erase a).erase b).card = (s.erase a).card - 1 := Finset.card_erase_of_mem hbm
  have h3 : ((s.erase a).erase b).card = s.card - 2 := by rw [h2, h1]; omega
  obtain ⟨c, hc⟩ := ((s.erase a).erase b).card_pos.mp (by omega)
  have hca : c ≠ a := (Finset.mem_erase.mp (Finset.mem_erase.mp hc).2).1
  have hcb : c ≠ b := (Finset.mem_erase.mp hc).1
  have hcs : c ∈ s := (Finset.mem_erase.mp (Finset.mem_erase.mp hc).2).2
  exact ⟨a, b, c, ha, hbs, hcs, hba.symm, hca.symm, hcb.symm⟩

/-! ### §2  Three edges of one colour in a `K₄` leave at most four colours -/

/-- **THREE OF THE SIX EDGES OF A FOUR-SET CARRYING ONE COLOUR.**  If three edges of a `K₄` have
colour `i`, that four-set spans at most four colours — so it cannot be admissible.  This is
`Definitions.classIn_card_le_two` read at a vertex, and it is the only input of the padding
criterion. -/
theorem card_colsOn_le_of_three {α β : Type*} [DecidableEq α] [DecidableEq β] {d : Sym2 α → β}
    {w x y z : α}
    (hwx : x ≠ w) (hwy : y ≠ w) (hwz : z ≠ w) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    {i : β} (hx : d s(w, x) = i) (hy : d s(w, y) = i) (hz : d s(w, z) = i) :
    (colsOn d (insert w (insert x (insert y (insert z (∅ : Finset α)))))).card ≤ 4 := by
  set U := insert w (insert x (insert y (insert z (∅ : Finset α)))) with hUdef
  have hUcard : U.card = 4 := by
    rw [hUdef, Finset.card_insert_of_notMem (by simp [hwx.symm, hwy.symm, hwz.symm]),
      Finset.card_insert_of_notMem (by simp [hxy, hxz]),
      Finset.card_insert_of_notMem (by simp [hyz]),
      Finset.card_insert_of_notMem (by simp)]
    simp
  have hwmem : w ∈ U := by rw [hUdef]; exact Finset.mem_insert_self w _
  have hxmem : x ∈ U := by
    rw [hUdef]
    exact Finset.mem_insert_of_mem (Finset.mem_insert_self x (insert y (insert z (∅ : Finset α))))
  have hymem : y ∈ U := by
    rw [hUdef]
    exact Finset.mem_insert_of_mem
      (Finset.mem_insert_of_mem (Finset.mem_insert_self y (insert z (∅ : Finset α))))
  have hzmem : z ∈ U := by
    rw [hUdef]
    exact Finset.mem_insert_of_mem
      (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_self z (∅ : Finset α))))
  have hm1 : s(w, x) ∈ edgesOn U := mem_edgesOn_pair hwmem hxmem hwx.symm
  have hm2 : s(w, y) ∈ edgesOn U := mem_edgesOn_pair hwmem hymem hwy.symm
  have hm3 : s(w, z) ∈ edgesOn U := mem_edgesOn_pair hwmem hzmem hwz.symm
  have hne1 : s(w, x) ≠ s(w, y) := fun h => hxy (sym2_inj_right h)
  have hne2 : s(w, x) ≠ s(w, z) := fun h => hxz (sym2_inj_right h)
  have hne3 : s(w, y) ≠ s(w, z) := fun h => hyz (sym2_inj_right h)
  set A := (edgesOn U).filter fun e : Sym2 α => d e = i with hAdef
  set B := (edgesOn U).filter fun e : Sym2 α => ¬ d e = i with hBdef
  have hsubA : ({s(w, x), s(w, y), s(w, z)} : Finset (Sym2 α)) ⊆ A := by
    rw [hAdef]
    intro e he
    simp only [Finset.mem_insert] at he
    rcases he with he | he
    · rw [he, Finset.mem_filter]
      exact ⟨hm1, hx⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton] at he
      rcases he with he | he
      · rw [he, Finset.mem_filter]
        exact ⟨hm2, hy⟩
      · rw [he, Finset.mem_filter]
        exact ⟨hm3, hz⟩
  have hcard3 : ({s(w, x), s(w, y), s(w, z)} : Finset (Sym2 α)).card = 3 := by
    simp [hne1, hne2, hne3]
  have hcardA : 3 ≤ A.card := calc
    3 = ({s(w, x), s(w, y), s(w, z)} : Finset (Sym2 α)).card := hcard3.symm
    _ ≤ A.card := Finset.card_le_card hsubA
  have hsum : A.card + B.card = (edgesOn U).card := by
    have h := Finset.card_filter_add_card_filter_not (s := edgesOn U)
      (p := fun e : Sym2 α => d e = i)
    rw [hAdef, hBdef]
    exact h
  have hU6 : (edgesOn U).card = 6 := card_edgesOn_four hUcard
  have hBcard : B.card ≤ 3 := by omega
  have hAimage : A.image d = {i} := by
    ext y
    simp only [Finset.mem_image, Finset.mem_singleton]
    constructor
    · rintro ⟨e, he, rfl⟩
      exact (Finset.mem_filter.mp he).2
    · intro hyi
      exact ⟨s(w, x), Finset.mem_filter.mpr ⟨hm1, hx⟩, hx.trans hyi.symm⟩
  have hsplit : (edgesOn U).image d = {i} ∪ B.image d := by
    ext y
    simp only [Finset.mem_union, Finset.mem_singleton]
    constructor
    · intro hy
      obtain ⟨e, he, heq⟩ := Finset.mem_image.mp hy
      by_cases h1 : d e = i
      · exact Or.inl (heq ▸ h1)
      · exact Or.inr (Finset.mem_image.mpr ⟨e, Finset.mem_filter.mpr ⟨he, h1⟩, heq⟩)
    · rintro (rfl | hy)
      · exact Finset.mem_image.mpr ⟨s(w, x), hm1, hx⟩
      · obtain ⟨e, he, heq⟩ := Finset.mem_image.mp hy
        exact Finset.mem_image.mpr ⟨e, (Finset.mem_filter.mp he).1, heq⟩
  have hcardle : (({i} : Finset β) ∪ B.image d).card ≤ 1 + B.card := by
    calc (({i} : Finset β) ∪ B.image d).card ≤ ({i} : Finset β).card + (B.image d).card :=
          Finset.card_union_le _ _
      _ ≤ 1 + B.card := by
        have h2 := Finset.card_image_le (s := B) (f := d)
        rw [Finset.card_singleton]
        omega
  calc (colsOn d U).card = ((edgesOn U).image d).card := rfl
    _ = ({i} ∪ B.image d).card := congrArg Finset.card hsplit
    _ ≤ 1 + B.card := hcardle
    _ ≤ 4 := by omega

/-- **THE STAR-FIBRE LEMMA.**  In an admissible colouring a colour occurs **at most twice** in the
star of a vertex. -/
theorem starAt_fibre_le_two {α β : Type*} [DecidableEq α] [DecidableEq β] {d : Sym2 α → β}
    (hd : AdmOn d)
    {w : α} (S : Finset α) (hw : w ∉ S) (i : β) :
    (S.filter fun v => d s(w, v) = i).card ≤ 2 := by
  by_contra h
  push_neg at h
  obtain ⟨x, y, z, hx, hy, hz, hxy, hxz, hyz⟩ := exists_three_mem' h
  have hxS : x ∈ S := (Finset.mem_filter.mp hx).1
  have hyS : y ∈ S := (Finset.mem_filter.mp hy).1
  have hzS : z ∈ S := (Finset.mem_filter.mp hz).1
  have hw' : w ≠ x := fun hh => hw (hh ▸ hxS)
  have hwy' : w ≠ y := fun hh => hw (hh ▸ hyS)
  have hwz' : w ≠ z := fun hh => hw (hh ▸ hzS)
  have hcard : (insert w (insert x (insert y (insert z (∅ : Finset α))))).card = 4 := by
    simp [hw', hwy', hwz', hxy, hxz, hyz]
  have hle : (colsOn d (insert w (insert x (insert y (insert z (∅ : Finset α)))))).card ≤ 4 :=
    card_colsOn_le_of_three (hwx := hw'.symm) (hwy := hwy'.symm) (hwz := hwz'.symm) hxy hxz hyz
      (Finset.mem_filter.mp hx).2 (Finset.mem_filter.mp hy).2 (Finset.mem_filter.mp hz).2
  exact absurd (hd _ hcard) (by omega)

/-! ### §3  Fresh colours at a vertex: at most `2 |P|` -/

/-- **THE FRESH-STAR BOUND.**  For an admissible colouring, at most `2 * |P|` of the edges at a
vertex carry colours from a palette `P`. -/
theorem starAt_fresh_le {α β : Type*} [DecidableEq α] [DecidableEq β] {d : Sym2 α → β} (hd : AdmOn d)
    {w : α} (S : Finset α) (hw : w ∉ S) (P : Finset β) :
    (S.filter fun v => d s(w, v) ∈ P).card ≤ 2 * P.card := by
  set S' := S.filter fun v => d s(w, v) ∈ P with hS'
  have hwn : w ∉ S' := fun hmem => hw ((Finset.mem_filter.mp hmem).1)
  have himg : S'.image (fun v => d s(w, v)) ⊆ P := by
    intro b hb
    obtain ⟨v, hv, he⟩ := Finset.mem_image.mp hb
    exact he ▸ (Finset.mem_filter.mp hv).2
  calc S'.card = ∑ b ∈ S'.image (fun v => d s(w, v)),
        (S'.filter fun v => d s(w, v) = b).card := Finset.card_eq_sum_card_image _ _
    _ ≤ ∑ _ ∈ S'.image (fun v => d s(w, v)), 2 :=
        Finset.sum_le_sum fun _ _ => starAt_fibre_le_two hd S' hwn _
    _ = 2 * (S'.image (fun v => d s(w, v))).card := by
      rw [Finset.sum_const_nat (fun _ _ => rfl)]
      omega
    _ ≤ 2 * P.card := Nat.mul_le_mul_left 2 (Finset.card_le_card himg)

/-- **THE PRICE OF A PALETTE.**  At least `|S| - 2|P|` edges at `w` do **not** carry colours from
`P`. -/
theorem starAt_out_le {α β : Type*} [DecidableEq α] [DecidableEq β] {d : Sym2 α → β} (hd : AdmOn d)
    {w : α} (S : Finset α) (hw : w ∉ S) (P : Finset β) :
    S.card - 2 * P.card ≤ (S.filter fun v => d s(w, v) ∉ P).card := by
  have hsum : S.card = (S.filter fun v => d s(w, v) ∈ P).card
      + (S.filter fun v => ¬ d s(w, v) ∈ P).card :=
    (Finset.card_filter_add_card_filter_not (s := S) (p := fun v => d s(w, v) ∈ P)).symm
  have hle := starAt_fresh_le hd S hw P
  omega

/-! ### §4  The padding criterion -/

/-- The star map induced by a padding: the colour of the edge from the new vertex `none` to an old
vertex `a`. -/
def StarAt0 {n j : ℕ} (d : Sym2 (Option (Verts n)) → Fin j) (g : Option (Verts n) → Fin j) : Prop :=
  ∀ a : Option (Verts n), a ≠ none → d s(none, a) = g a

/-- **THE OLD SIDE.**  Every four-element set of *old* vertices still spans five colours inside `d`:
the restriction of the padding to the old vertices is admissible. -/
def OldOk {n j : ℕ} (d : Sym2 (Option (Verts n)) → Fin j) : Prop :=
  ∀ S : Finset (Option (Verts n)), none ∉ S → S.card = 4 → 5 ≤ (colsOn d S).card

/-- **THE PADDING CONDITION.**  Every triple of old vertices, together with the star colours of the
new vertex, spans at least five colours. -/
def PadOk {n j : ℕ} (d : Sym2 (Option (Verts n)) → Fin j) (g : Option (Verts n) → Fin j) : Prop :=
  ∀ T : Finset (Option (Verts n)), none ∉ T → T.card = 3 →
    5 ≤ ((colsOn d T) ∪ T.image g).card

instance padOk_decidable {n j : ℕ} (d : Sym2 (Option (Verts n)) → Fin j)
    (g : Option (Verts n) → Fin j) : Decidable (PadOk d g) := by
  unfold PadOk
  infer_instance

/-- The old vertices of the padded colouring: all of them but the new one. -/
def oldVerts {n : ℕ} : Finset (Option (Verts n)) :=
  (Finset.univ : Finset (Option (Verts n))).erase none

theorem card_oldVerts {n : ℕ} : (oldVerts (n := n)).card = n := by
  rw [oldVerts, Finset.card_erase_of_mem (by simp)]
  simp [Fintype.card_option]

/-- The star colours of a set of old vertices, read off the colouring. -/
private theorem image_star {n j : ℕ} {d : Sym2 (Option (Verts n)) → Fin j}
    {g : Option (Verts n) → Fin j} (hs : StarAt0 d g) {T : Finset (Option (Verts n))}
    (hT : none ∉ T) : T.image (fun a => d s(none, a)) = T.image g := by
  ext x
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨a, ha, he⟩
    exact ⟨a, ha, (hs a (fun hh => hT (hh ▸ ha))).symm.trans he⟩
  · rintro ⟨a, ha, he⟩
    exact ⟨a, ha, (hs a (fun hh => hT (hh ▸ ha))).trans he⟩

/-- **THE FOUR-SET LEMMA OF THE PADDING.**  The colours of `insert none T` are exactly the colours
of `T` together with the star colours of the vertices of `T`: the six edges of the new four-set are
the three edges of `T` and the three star edges. -/
private theorem colsOn_insert_none {n j : ℕ} {d : Sym2 (Option (Verts n)) → Fin j}
    {T : Finset (Option (Verts n))} (hT : none ∉ T) (x : Fin j)
    (hx : x ∈ colsOn d (insert none T)) :
    x ∈ colsOn d T ∨ ∃ a ∈ T, d s(none, a) = x := by
  obtain ⟨e, he, heq⟩ := mem_colsOn.mp hx
  obtain ⟨he1, he2⟩ := mem_edgesOn.mp he
  rw [Finset.sym2_insert, Finset.mem_union] at he1
  rcases he1 with he1 | he1
  · obtain ⟨b, hb, heb⟩ := Finset.mem_image.mp he1
    rcases b with _ | a
    · have hebb : e = s(none, none) := heb.symm
      exact absurd (hebb ▸ Finset.mem_image.mpr ⟨none, Finset.mem_insert_self none T, rfl⟩) he2
    · rcases Finset.mem_insert.mp hb with hb0 | hb'
      · rcases Finset.mem_insert.mp (hb0 ▸ Finset.mem_insert_self none T) with _ | hb''
        · exact absurd hb0 (by simp)
        · exact absurd (hb0 ▸ hb'') hT
      · rw [← heb] at heq
        refine Or.inr ⟨some a, hb', ?_⟩
        exact heq
  · refine Or.inl (mem_colsOn.mpr ⟨e, mem_edgesOn.mpr ⟨he1, ?_⟩, heq⟩)
    intro hmem
    obtain ⟨z, hz, hez⟩ := Finset.mem_image.mp hmem
    have hzT : z ∈ T := Finset.mem_sym2_iff.mp he1 z (by rw [← hez]; simp)
    have hmem' : e ∈ (insert none T).image fun a : Option (Verts n) => s(a, a) :=
      Finset.mem_image.mpr ⟨z, Finset.mem_insert_of_mem hzT, hez⟩
    exact absurd hmem' he2

/-- **`PadOk` is necessary**: every admissible padding satisfies it. -/
theorem padOk_of_admissible {n j : ℕ} {d : Sym2 (Option (Verts n)) → Fin j}
    {g : Option (Verts n) → Fin j} (hd : AdmOn d) (hs : StarAt0 d g) : PadOk d g := by
  intro T hTnone hT
  have hcard : (insert none T).card = 4 := by
    rw [Finset.card_insert_of_notMem hTnone]
    omega
  have h1 : (colsOn d (insert none T)).card ≤ ((colsOn d T) ∪ T.image g).card := by
    refine Finset.card_le_card (fun x hx => ?_)
    rw [← image_star hs hTnone]
    rcases colsOn_insert_none hTnone x hx with hx | hx
    · exact Finset.mem_union_left _ hx
    · obtain ⟨a, ha, he⟩ := hx
      refine Finset.mem_union_right _ ?_
      have hmem' : x ∈ T.image fun b => d s(none, b) := Finset.mem_image.mpr ⟨a, ha, he⟩
      exact hmem'
  exact (hd _ hcard).trans h1  -- 5 ≤ card of the padded four-set

/-- **`PadOk` is sufficient**: together with `OldOk` it certifies admissibility. -/
theorem admissible_of_padOk {n j : ℕ} {d : Sym2 (Option (Verts n)) → Fin j}
    {g : Option (Verts n) → Fin j} (hs : StarAt0 d g) (ho : OldOk d) (hp : PadOk d g) : AdmOn d := by
  intro S hS
  by_cases hnone : none ∈ S
  · have herase : none ∉ S.erase none := Finset.notMem_erase none S
    have hcard : (S.erase none).card = 3 := by
      have h1 : (S.erase none).card = S.card - 1 := Finset.card_erase_of_mem hnone
      omega
    have hle := hp (S.erase none) herase hcard
    have hsub : (colsOn d (S.erase none)) ∪ (S.erase none).image g ⊆ colsOn d S := by
      refine Finset.union_subset (colsOn_mono (Finset.erase_subset _ _) d) ?_
      intro y hy
      obtain ⟨a, ha, he⟩ := Finset.mem_image.mp hy
      refine mem_colsOn.mpr ⟨s(none, a), ?_, ?_⟩
      · exact mem_edgesOn_pair hnone (Finset.mem_of_mem_erase ha) (fun hh => herase (hh ▸ ha))
      · exact (hs a (fun hh => herase (hh ▸ ha))).trans he
    exact hle.trans (Finset.card_le_card hsub)
  · exact ho S hnone hS

/-- **THE PADDING CRITERION.**  A colouring of `K_{n+1}` is admissible **iff** the old part is
admissible and its star map satisfies `PadOk`. -/
theorem admissible_iff_padOk {n j : ℕ} {d : Sym2 (Option (Verts n)) → Fin j}
    {g : Option (Verts n) → Fin j} (hs : StarAt0 d g) : AdmOn d ↔ (OldOk d ∧ PadOk d g) :=
  ⟨fun hd => ⟨fun S _ hS => hd S hS, padOk_of_admissible hd hs⟩,
    fun h => admissible_of_padOk hs h.1 h.2⟩

/-! ### §5  What the padding map must look like -/

/-- **THE FIBRE BOUND FOR A PADDING MAP.**  No colour occurs three times in the star map over the
old vertices: a monochromatic triple of star colours over a triangle of old vertices spans at most
four colours. -/
theorem padOk_fibre_le_two {n j : ℕ} {d : Sym2 (Option (Verts n)) → Fin j}
    {g : Option (Verts n) → Fin j} (hp : PadOk d g) (i : Fin j) :
    ((oldVerts (n := n)).filter (fun v => g v = i)).card ≤ 2 := by
  by_contra h
  push_neg at h
  obtain ⟨x, y, z, hx, hy, hz, hxy, hxz, hyz⟩ := exists_three_mem' h
  have hxn : x ≠ none := (Finset.mem_erase.mp (Finset.mem_filter.mp hx).1).1
  have hyn : y ≠ none := (Finset.mem_erase.mp (Finset.mem_filter.mp hy).1).1
  have hzn : z ≠ none := (Finset.mem_erase.mp (Finset.mem_filter.mp hz).1).1
  set T3 := insert x (insert y (insert z (∅ : Finset (Option (Verts n))))) with hT3
  have hT3card : T3.card = 3 := by
    rw [hT3]
    rw [Finset.card_insert_of_notMem (by simp [hxy, hxz]),
      Finset.card_insert_of_notMem (by simp [hxy, hyz]),
      Finset.card_insert_of_notMem (by simp [hyz])]
    simp
  have hnone : none ∉ T3 := by
    rw [hT3]
    simp [hxn.symm, hyn.symm, hzn.symm]
  have himg : T3.image g = {i} := by
    rw [hT3]
    ext b
    simp only [Finset.mem_image, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨v, hv, rfl⟩
      rcases hv with rfl | rfl | rfl | hv
      · exact (Finset.mem_filter.mp hx).2
      · exact (Finset.mem_filter.mp hy).2
      · exact (Finset.mem_filter.mp hz).2
      · exact absurd hv (by simp)
    · rintro rfl
      exact ⟨x, Or.inl rfl, (Finset.mem_filter.mp hx).2⟩
  have h1 : (colsOn d T3).card ≤ 3 := by
    rw [hT3]
    exact card_colsOn_three d hT3card
  have h2 : ((colsOn d T3) ∪ T3.image g).card ≤ 4 := by
    rw [himg]
    have h3 := Finset.card_union_le (colsOn d T3) ({i} : Finset (Fin j))
    rw [Finset.card_singleton] at h3
    omega
  have h3 := hp T3 hnone hT3card
  omega

/-- **THE STAR OF A NEW VERTEX SEES AT LEAST `⌈n/2⌉` COLOURS.** -/
theorem padOk_image_card {n j : ℕ} {d : Sym2 (Option (Verts n)) → Fin j}
    {g : Option (Verts n) → Fin j} (hp : PadOk d g) :
    n ≤ 2 * ((oldVerts (n := n)).image g).card := by
  set S := oldVerts (n := n) with hS
  set im := S.image g with him
  calc n = S.card := by rw [hS]; exact card_oldVerts.symm
    _ = ∑ b ∈ im, (S.filter fun v => g v = b).card := Finset.card_eq_sum_card_image g S
    _ ≤ ∑ _ ∈ im, 2 := Finset.sum_le_sum fun _ _ => padOk_fibre_le_two hp _
    _ = 2 * im.card := by rw [Finset.sum_const_nat (fun _ _ => rfl)]; omega
    _ = 2 * (S.image g).card := by rw [him]

/-- **FRESH COLOURS CANNOT PAD.**  If the padding map only takes values in a palette `P` on the old
vertices, then `|P| ≥ ⌈n/2⌉`. -/
theorem padOk_fresh_half {n j : ℕ} {d : Sym2 (Option (Verts n)) → Fin j}
    {g : Option (Verts n) → Fin j} (hp : PadOk d g) (P : Finset (Fin j))
    (hP : (oldVerts (n := n)).image g ⊆ P) : n ≤ 2 * P.card :=
  (padOk_image_card hp).trans (Nat.mul_le_mul_left 2 (Finset.card_le_card hP))

/-- **NO CHEAP PADDING.**  For `n ≥ 5` the star map of an admissible padding takes at least three
values on the old vertices: padding one vertex with a two-colour star is impossible for every
`n ≥ 5`. -/
theorem padOk_three_colours {n j : ℕ} {d : Sym2 (Option (Verts n)) → Fin j}
    {g : Option (Verts n) → Fin j} (hd : AdmOn d) (hs : StarAt0 d g) (hn : 5 ≤ n) :
    3 ≤ ((oldVerts (n := n)).image g).card := by
  have h := padOk_image_card (padOk_of_admissible hd hs)
  omega

/-! ### §6  The `Col`-language version: what a growth map must reuse -/

/-- **THE FRESH-STAR BOUND FOR A COLOURING OF `K_N`.**  At most `2 * |P|` of the edges at `w`
carry colours from `P`. -/
theorem fresh_star_le {N : ℕ} {k : ℕ} {c : Col N k} (hc : Admissible c) {w : Verts N}
    (S : Finset (Verts N)) (hw : w ∉ S) (P : Finset (Fin k)) :
    (S.filter fun v => c s(w, v) ∈ P).card ≤ 2 * P.card :=
  starAt_fresh_le (AdmOn_iff.mp hc) S hw P

/-- **THE PRICE OF A PALETTE AT A VERTEX OF `K_N`.** -/
theorem cross_old_ge {N : ℕ} {k : ℕ} {c : Col N k} (hc : Admissible c) {w : Verts N}
    (S : Finset (Verts N)) (hw : w ∉ S) (P : Finset (Fin k)) :
    S.card - 2 * P.card ≤ (S.filter fun v => ¬ c s(w, v) ∈ P).card :=
  starAt_out_le (AdmOn_iff.mp hc) S hw P

/-- **THE ACCEPTANCE TEST FOR THE SIX-STEP OF ROUND 68.**  Let `new` be the six new vertices of a
growth map on `K_{m+6}`, `old` the `m` old ones, and `P` the palette of the five new colours.  Then
**every new vertex has at most `10` cross edges into the old vertices carrying new colours**, i.e. at
least `|old| - 10` of them must reuse the old palette.  At the `K₁₂` anchor (`|old| = 12`) that is
**at least two**. -/
theorem six_step_test {N : ℕ} {k : ℕ} {c : Col N k} (hc : Admissible c)
    (new old : Finset (Verts N)) (P : Finset (Fin k))
    (hdisj : new ∩ old = ∅) (hcov : new ∪ old = (Finset.univ : Finset (Verts N)))
    (hnew : new.card = 6) (hP : P.card = 5) :
    ∀ w ∈ new, old.card - 10 ≤ (old.filter fun v => ¬ c s(w, v) ∈ P).card := by
  intro w hwm
  have h := cross_old_ge (w := w) hc old ?_ P
  · rwa [hP] at h
  · intro hmem
    have hmem' : w ∈ new ∩ old := Finset.mem_inter.mpr ⟨hwm, hmem⟩
    rw [hdisj] at hmem'
    exact absurd hmem' (by simp)

/-! ### §7  The old side is exactly "the restriction is admissible" -/

private theorem eq_some_of_mem {n : ℕ} {S : Finset (Option (Verts n))} (h : none ∉ S)
    {x : Option (Verts n)} (hx : x ∈ S) : ∃ a : Verts n, x = some a := by
  cases x with
  | none => exact absurd hx h
  | some a => exact ⟨a, rfl⟩

private theorem exists_four_mem {α : Type*} [DecidableEq α] {S : Finset α} (hS : S.card = 4) :
    ∃ w x y z : α, w ∈ S ∧ x ∈ S ∧ y ∈ S ∧ z ∈ S ∧ w ≠ x ∧ w ≠ y ∧ w ≠ z ∧ x ≠ y ∧ x ≠ z ∧
      y ≠ z := by
  obtain ⟨w, hw⟩ := S.card_pos.mp (by omega)
  have h1 : (S.erase w).card = S.card - 1 := Finset.card_erase_of_mem hw
  obtain ⟨x, hx⟩ := (S.erase w).card_pos.mp (by omega)
  have hxw : x ≠ w := (Finset.mem_erase.mp hx).1
  have hxw' : x ∈ S := (Finset.mem_erase.mp hx).2
  have h2 : ((S.erase w).erase x).card = (S.erase w).card - 1 :=
    Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hxw, hxw'⟩)
  obtain ⟨y, hy⟩ := ((S.erase w).erase x).card_pos.mp (by omega)
  have hy' : y ∈ S.erase w := (Finset.mem_erase.mp hy).2
  have hyw : y ≠ w := (Finset.mem_erase.mp hy').1
  have hyx : y ≠ x := (Finset.mem_erase.mp hy).1
  have hyw' : y ∈ S := (Finset.mem_erase.mp hy').2
  have h3 : (((S.erase w).erase x).erase y).card = ((S.erase w).erase x).card - 1 :=
    Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hyx, hy'⟩)
  have h4 : (((S.erase w).erase x).erase y).card = S.card - 3 := by rw [h3, h2, h1]; omega
  obtain ⟨z, hz⟩ := (((S.erase w).erase x).erase y).card_pos.mp (by omega)
  have hzy : z ∈ (S.erase w).erase x := (Finset.mem_erase.mp hz).2
  have hzx : z ∈ S.erase w := (Finset.mem_erase.mp hzy).2
  have hzw : z ∈ S := (Finset.mem_erase.mp hzx).2
  refine ⟨w, x, y, z, hw, hxw', hyw', hzw, hxw.symm, hyw.symm,
    (Finset.mem_erase.mp hzx).1.symm, hyx.symm, (Finset.mem_erase.mp hzy).1.symm,
    (Finset.mem_erase.mp hz).1.symm⟩

private theorem ne_of_some {n : ℕ} {p q : Verts n} {w x : Option (Verts n)} (ha : w = some p)
    (hb : x = some q) (hne : w ≠ x) : p ≠ q := by
  intro h
  subst h
  exact hne (hb.trans ha.symm).symm

/-- **`OldOk` is the admissibility of the restriction.**  If `d` agrees with `c` on the old edges (in
the extended palette) and `c` is admissible, then `OldOk d`: the four old vertices of any old
four-set of the padded colouring span five colours. -/
theorem oldOk_of_restrict {n k j : ℕ} (hk : k ≤ j) {c : Col n k}
    {d : Sym2 (Option (Verts n)) → Fin j} (hc : Admissible c)
    (hrest : ∀ a b : Verts n, d s(some a, some b) = Fin.castLE hk (c s(a, b))) : OldOk d := by
  intro S hnone hS
  obtain ⟨w, x, y, z, hw, hx, hy, hz, hwx, hwy, hwz, hxy, hxz, hyz⟩ := exists_four_mem hS
  obtain ⟨a, ha⟩ := eq_some_of_mem hnone hw
  obtain ⟨b, hb⟩ := eq_some_of_mem hnone hx
  obtain ⟨u, hu⟩ := eq_some_of_mem hnone hy
  obtain ⟨v, hv⟩ := eq_some_of_mem hnone hz
  set T := insert a (insert b (insert u (insert v (∅ : Finset (Verts n))))) with hT
  have hab : a ≠ b := ne_of_some ha hb hwx
  have hau : a ≠ u := ne_of_some ha hu hwy
  have hav : a ≠ v := ne_of_some ha hv hwz
  have hbu : b ≠ u := ne_of_some hb hu hxy
  have hbv : b ≠ v := ne_of_some hb hv hxz
  have huv : u ≠ v := ne_of_some hu hv hyz
  have hTcard : T.card = 4 := by simp [hT, hab, hau, hav, hbu, hbv, huv]
  have memS : ∀ p : Verts n, p ∈ T → some p ∈ S := by
    intro p hp
    simp only [hT, Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl | hp'
    · rw [← ha]; exact hw
    · rw [← hb]; exact hx
    · rw [← hu]; exact hy
    · rw [← hv]; exact hz
    · exact absurd hp' (by simp)
  have memE : ∀ p q : Verts n, p ∈ T → q ∈ T → p ≠ q → s(some p, some q) ∈ edgesOn S := by
    intro p q hp hq hpq
    exact mem_edgesOn_pair (memS p hp) (memS q hq) (fun hh => hpq (Option.some.inj hh))
  have hle : ∀ x : Fin k, x ∈ colorsOn c T → Fin.castLE hk x ∈ colsOn d S := by
    intro x hx
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨h1, h2⟩ := mem_edgeFinset.mp he
    refine Sym2.ind (f := fun e : Sym2 (Verts n) => e ∈ T.sym2 → OffDiag e →
      Fin.castLE hk (c e) ∈ colsOn d S) ?_ e h1 h2
    intro p q hpq he1
    have hp' : p ∈ T := Finset.mem_sym2_iff.mp hpq p (by simp [Multiset.mem_cons])
    have hq' : q ∈ T := Finset.mem_sym2_iff.mp hpq q (by simp [Multiset.mem_cons])
    refine mem_colsOn.mpr ⟨s(some p, some q), ?_, hrest p q⟩
    · have hpq : p ≠ q := he1 p q rfl
      refine mem_edgesOn.mpr ⟨?_, ?_⟩
      · exact Finset.mk_mem_sym2_iff.mpr ⟨memS p hp', memS q hq'⟩
      · intro hmem
        obtain ⟨z, hz, hez⟩ := Finset.mem_image.mp hmem
        rcases sym2_inj hez with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact absurd (Option.some.inj (h1.symm.trans h2)) hpq
        · exact absurd (Option.some.inj (h1.symm.trans h2)) hpq.symm
  have hcard2 : (colorsOn c T).card ≤ ((colorsOn c T).image (Fin.castLE hk)).card := by
    have heq : ((colorsOn c T).image (Fin.castLE hk)).card = (colorsOn c T).card :=
      Finset.card_image_of_injective _ fun a b h => Fin.castLE_inj.mp h
    exact heq.symm.le
  have hcard3 : ((colorsOn c T).image (Fin.castLE hk)).card ≤ (colsOn d S).card := by
    refine Finset.card_le_card fun _ hy => ?_
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    exact hle x hx
  exact (hc T hTcard).trans (hcard2.trans hcard3)

end JSP140
