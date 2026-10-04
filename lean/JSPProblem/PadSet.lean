import JSPProblem.Pad

/-!
# JSP-000140 — round 83: THE MULTI-VERTEX PADDING CRITERION

Round 68 reduced the missing half of `f(n,4,5) = 5n/6 + o(n)` to the **six-step growth lemma**
`Grow6` — every admissible colouring of `K_m` extends to an admissible colouring of `K_{m+6}` with
five more colours — and `One.lean` (this round) weakened it further to the mere *existence* of one
admissible colouring of `K_{18+6t}` with `16+5t` colours for every `t`.  Either way the remaining
object is a **finite** one: an admissible colouring of `K_{18}` with sixteen colours.

Round 69 gave the exact local criterion for adding **one** vertex (`Pad.admissible_iff_padOk`:
the old side stays admissible, and every *triple* of old vertices together with the star colours
spans five colours).  A six-step adds **six** vertices at once, and no criterion for that existed,
so no certificate for a six-step could even be written down.  This file supplies it.

## The criterion

Write the vertices of `K_{n+m}` as `Verts n ⊕ Verts m`: the old vertices are `Sum.inl w`, the new
ones `Sum.inr u`, and the cross colours are read off by

    `Star d w u = d s(Sum.inl w, Sum.inr u)`,

so `Star d` is the **star matrix** of the extension: rows = old vertices, columns = new vertices,
entries = colours of the cross edges.  Then

    `AdmOn d  ↔  OldOk4 ∧ NewOk4 ∧ TriOld ∧ TriNew ∧ PairOk`   (`admissible_iff_padSet`)

with one condition per shape a four-element vertex set can have:

| condition | shape | content |
|---|---|---|
| `OldOk4` | 4 old | the restriction is admissible |
| `NewOk4` | 4 new | the colouring of `K_m` is admissible |
| `TriOld` | 3 old + 1 new | old colours of the triple ∪ the three star colours span 5 |
| `TriNew` | 1 old + 3 new | new colours of the triple ∪ the three star colours span 5 |
| `PairOk` | 2 old + 2 new | the six colours of the four-set span 5 |

So a six-step is certified by **five finite statements** (`padSetOk_decidable`), each of them
`Decidable` and each mentioning only the extension data — no search has to enumerate `16^153`
colourings of `K_{18}`.

## What the criterion forces on the star matrix

* `fibre_le_two_of_triOld`, `fibre_le_two_of_triNew` — **no colour occurs three times in a row and
  no colour occurs three times in a column** of the star matrix (a monochromatic triple of star
  colours over a triangle spans at most four colours).  Hence `image_card_le` and `image_card_le'`:
  a row of `n` entries takes at least `⌈n/2⌉` values, a column of `m` entries at least `⌈m/2⌉`; at
  the `K₁₂` anchor (six new vertices, sixteen colours) **each new vertex sees at least six of the
  sixteen colours, and each old vertex at least three**;

* `pair_inj` — **NO `2 × 2` MONOCHROMATIC BLOCK**: for `x ≠ y` new vertices the map
  `w ↦ (Star d w x, Star d w y)` is *injective*, i.e. two old vertices never agree on two new
  vertices at once.  This is the combinatorial core of a six-step: a repeated colour in one column
  must be paid for by fresh colours in every other column, and it cannot be paid twice.  The
  consequences `card_le_sq` and `pair_five_distinct` (when a colour *is* repeated in a column, the
  four remaining colours of the corresponding four-set are pairwise distinct and different from it)
  are the two local rules a growth map has to satisfy;

* `quad_col_ge_five` / `quad_col_le_four_of_agree` — the exact colour set `QuadCol d w v x y` of a
  `2 + 2` four-set, with `5 ≤ |QuadCol|` from `PairOk` and `|QuadCol| ≤ 4` as soon as the two old
  vertices agree on one of the two new ones.  That is `pair_inj` in a directly checkable form.

Nothing here assumes `Grow6`: the file is a description of an extension, usable by any search and
by any hand construction of a six-step out of `Window.admissible_r66Col`.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace JSP140

/-! ### §1  `n` old vertices and `m` new ones -/

/-- A vertex of `K_{n+m}` is **old** when it comes from `Verts n`. -/
def IsOld {n m : ℕ} (v : Verts n ⊕ Verts m) : Prop := ∃ w : Verts n, v = Sum.inl w

/-- A vertex of `K_{n+m}` is **new** when it comes from `Verts m`. -/
def IsNew {n m : ℕ} (v : Verts n ⊕ Verts m) : Prop := ∃ u : Verts m, v = Sum.inr u

/-- An old vertex and a new vertex are never equal. -/
theorem isOld_ne_isNew {n m : ℕ} {v : Verts n ⊕ Verts m} {u : Verts n ⊕ Verts m}
    (hv : IsOld v) (hu : IsNew u) : v ≠ u := by
  intro hcon
  obtain ⟨w, hw⟩ := hv
  obtain ⟨y, hy⟩ := hu
  rw [hw, hy] at hcon
  exact Sum.inl_ne_inr hcon

/-- The two classes of vertices are disjoint: **a vertex is never both old and new**.  This is the
one-line form used by the criterion below. -/
theorem not_isOld_isNew {n m : ℕ} {v : Verts n ⊕ Verts m} (hv : IsOld v) : ¬ IsNew v :=
  fun hu => isOld_ne_isNew hv hu rfl

instance decidablePred_isOld {n m : ℕ} : DecidablePred (IsOld (n := n) (m := m)) := by
  intro v; unfold IsOld; infer_instance

instance decidablePred_isNew {n m : ℕ} : DecidablePred (IsNew (n := n) (m := m)) := by
  intro v; unfold IsNew; infer_instance

/-- **THE STAR MATRIX OF AN EXTENSION.**  `Star d w u` is the colour of the edge from the old
vertex `w` to the new vertex `u`. -/
def Star {n m k : ℕ} (d : Sym2 (Verts n ⊕ Verts m) → Fin k) : Verts n → Verts m → Fin k :=
  fun w u => d s(Sum.inl w, Sum.inr u)

/-! ### §2  The five conditions, one per shape -/

/-- **Four old vertices**: the restriction of the extension to the old vertices is admissible. -/
def OldOk4 {n m k : ℕ} (d : Sym2 (Verts n ⊕ Verts m) → Fin k) : Prop :=
  ∀ T : Finset (Verts n ⊕ Verts m), (∀ v ∈ T, IsOld v) → T.card = 4 →
    5 ≤ (colsOn d T).card

/-- **Four new vertices**: the colouring induced on the new vertices is admissible. -/
def NewOk4 {n m k : ℕ} (d : Sym2 (Verts n ⊕ Verts m) → Fin k) : Prop :=
  ∀ U : Finset (Verts n ⊕ Verts m), (∀ v ∈ U, IsNew v) → U.card = 4 →
    5 ≤ (colsOn d U).card

/-- **Three old and one new vertex**: the colours of the old triple, together with the three star
colours read at the new vertex, span at least five colours. -/
def TriOld {n m k : ℕ} (d : Sym2 (Verts n ⊕ Verts m) → Fin k) : Prop :=
  ∀ T : Finset (Verts n ⊕ Verts m), (∀ v ∈ T, IsOld v) → T.card = 3 →
    ∀ x : Verts n ⊕ Verts m, IsNew x →
      5 ≤ ((colsOn d T) ∪ T.image (fun v => d s(v, x))).card

/-- **One old and three new vertices**: the colours of the new triple, together with the three star
colours read at the old vertex, span at least five colours.  This is the shape `PadOk` cannot
see: it is invisible to a one-vertex padding. -/
def TriNew {n m k : ℕ} (d : Sym2 (Verts n ⊕ Verts m) → Fin k) : Prop :=
  ∀ U : Finset (Verts n ⊕ Verts m), (∀ v ∈ U, IsNew v) → U.card = 3 →
    ∀ w : Verts n ⊕ Verts m, IsOld w →
      5 ≤ ((colsOn d U) ∪ U.image (fun v => d s(v, w))).card

/-- **Two old and two new vertices**: the six colours of the four-set span at least five. -/
def PairOk {n m k : ℕ} (d : Sym2 (Verts n ⊕ Verts m) → Fin k) : Prop :=
  ∀ T : Finset (Verts n ⊕ Verts m), (∀ v ∈ T, IsOld v) → T.card = 2 →
    ∀ U : Finset (Verts n ⊕ Verts m), (∀ v ∈ U, IsNew v) → U.card = 2 →
      5 ≤ (((colsOn d T) ∪ colsOn d U) ∪ (T.product U).image (fun p => d s(p.1, p.2))).card

/-- **THE FIVE CONDITIONS, AS ONE DECIDABLE STATEMENT.**  A six-step out of `K_n` (six new vertices,
five new colours) is therefore certified by evaluating one decidable proposition. -/
def PadSetOk {n m k : ℕ} (d : Sym2 (Verts n ⊕ Verts m) → Fin k) : Prop :=
  OldOk4 d ∧ NewOk4 d ∧ TriOld d ∧ TriNew d ∧ PairOk d

instance padSetOk_decidable {n m k : ℕ} (d : Sym2 (Verts n ⊕ Verts m) → Fin k) :
    Decidable (PadSetOk d) := by
  have h1 : Decidable (OldOk4 d) := by unfold OldOk4 IsOld; infer_instance
  have h2 : Decidable (NewOk4 d) := by unfold NewOk4 IsNew; infer_instance
  have h3 : Decidable (TriOld d) := by unfold TriOld IsOld IsNew; infer_instance
  have h4 : Decidable (TriNew d) := by unfold TriNew IsOld IsNew; infer_instance
  have h5 : Decidable (PairOk d) := by unfold PairOk IsOld IsNew; infer_instance
  exact inferInstanceAs
    (Decidable (OldOk4 d ∧ NewOk4 d ∧ TriOld d ∧ TriNew d ∧ PairOk d))

/-! ### §3  Two four-set lemmas -/

/-- **THE `3 + 1` FOUR-SET LEMMA.**  If `x ∉ T` then the colours of `insert x T` are *exactly*
the colours of `T` together with the colours of the edges from `x` into `T`: the six edges of the
four-set `insert x T` are the edges of `T` and the three edges at `x`. -/
theorem cross_eq {α β : Type*} [DecidableEq α] [DecidableEq β] {d : Sym2 α → β}
    {T : Finset α} {x : α} (hx : x ∉ T) :
    colsOn d (insert x T) = colsOn d T ∪ T.image (fun v => d s(v, x)) := by
  apply Finset.Subset.antisymm
  · intro y hy
    obtain ⟨e, he, heq⟩ := mem_colsOn.mp hy
    obtain ⟨he1, he2⟩ := mem_edgesOn.mp he
    rw [Finset.sym2_insert x T, Finset.mem_union] at he1
    rcases he1 with he1 | he1
    · obtain ⟨b, hb, heb⟩ := Finset.mem_image.mp he1
      have he3 : e = s(x, b) := heb.symm
      rw [he3] at heq
      rcases Finset.mem_insert.mp hb with hbx | hb
      · exact (he2 (Finset.mem_image.mpr
          ⟨x, Finset.mem_insert_self x T, by rw [he3, hbx]⟩)).elim
      · have hy1 : y = d s(b, x) := by
          calc y = d s(x, b) := heq.symm
            _ = d s(b, x) := congrArg d Sym2.eq_swap.symm
        exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨b, hb, hy1.symm⟩)
    · have he2' : ¬ e ∈ T.image (fun a : α => s(a, a)) := by
        intro hm
        obtain ⟨a, ha, heq2⟩ := Finset.mem_image.mp hm
        exact he2 (Finset.mem_image.mpr ⟨a, Finset.mem_insert_of_mem ha, heq2⟩)
      exact Finset.mem_union_left _ (mem_colsOn.mpr ⟨e, mem_edgesOn.mpr ⟨he1, he2'⟩, heq⟩)
  · intro y hy
    rcases Finset.mem_union.mp hy with hy | hy
    · exact colsOn_mono (fun v hv => Finset.mem_insert_of_mem hv) d hy
    · obtain ⟨v, hv, he⟩ := Finset.mem_image.mp hy
      refine mem_colsOn.mpr ⟨s(v, x), ?_, he⟩
      exact mem_edgesOn_pair (Finset.mem_insert_of_mem hv) (Finset.mem_insert_self x T)
        (fun hh => hx (hh ▸ hv))

/-- **THE `2 + 2` FOUR-SET LEMMA.**  If no element of `T` equals an element of `U` then the
colours of `T ∪ U` are *exactly* the colours of `T`, of `U` and of the edges between them: the six
edges of the four-set are the edge of `T`, the edge of `U` and the four crossing edges. -/
theorem quad_eq {α β : Type*} [DecidableEq α] [DecidableEq β] {d : Sym2 α → β}
    {T U : Finset α} (hTU : ∀ a ∈ T, ∀ b ∈ U, a ≠ b) :
    colsOn d (T ∪ U) =
      ((colsOn d T) ∪ colsOn d U) ∪ (T.product U).image (fun p => d s(p.1, p.2)) := by
  have memT : T.image (fun a : α => s(a, a)) ⊆ (T ∪ U).image (fun a : α => s(a, a)) := by
    intro x hx
    obtain ⟨a, ha, hb⟩ := Finset.mem_image.mp hx
    exact Finset.mem_image.mpr ⟨a, Finset.mem_union_left _ ha, hb⟩
  have memU : U.image (fun a : α => s(a, a)) ⊆ (T ∪ U).image (fun a : α => s(a, a)) := by
    intro x hx
    obtain ⟨a, ha, hb⟩ := Finset.mem_image.mp hx
    exact Finset.mem_image.mpr ⟨a, Finset.mem_union_right _ ha, hb⟩
  apply Finset.Subset.antisymm
  · intro y hy
    obtain ⟨e, he, heq⟩ := mem_colsOn.mp hy
    obtain ⟨he1, he2⟩ := mem_edgesOn.mp he
    rw [Finset.sym2_eq_image] at he1
    obtain ⟨p, hp, hpe⟩ := Finset.mem_image.mp he1
    obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
    have heq' : d s(p.1, p.2) = y := (congrArg d hpe).trans heq
    have hn : ¬ s(p.1, p.2) ∈ (T ∪ U).image (fun a : α => s(a, a)) := fun hm => he2 (hpe ▸ hm)
    rcases Finset.mem_union.mp hp1 with h1 | h1
    · rcases Finset.mem_union.mp hp2 with h2 | h2
      · exact Finset.mem_union_left _ (Finset.mem_union_left _
          (mem_colsOn.mpr ⟨s(p.1, p.2), mem_edgesOn.mpr
            ⟨Finset.mk_mem_sym2_iff.mpr ⟨h1, h2⟩, fun hm => hn (memT hm)⟩, heq'⟩))
      · exact Finset.mem_union_right _ (Finset.mem_image.mpr
          (show ∃ a, a ∈ T.product U ∧ d s(a.1, a.2) = y from
            ⟨p, Finset.mem_product.mpr ⟨h1, h2⟩, heq'⟩))
    · rcases Finset.mem_union.mp hp2 with h2 | h2
      · exact Finset.mem_union_right _ (Finset.mem_image.mpr
          (show ∃ a, a ∈ T.product U ∧ d s(a.1, a.2) = y from ⟨p.swap,
            Finset.mem_product.mpr ⟨h2, h1⟩, (congrArg d Sym2.eq_swap).trans heq'⟩))
      · exact Finset.mem_union_left _ (Finset.mem_union_right _
          (mem_colsOn.mpr ⟨s(p.1, p.2), mem_edgesOn.mpr
            ⟨Finset.mk_mem_sym2_iff.mpr ⟨h1, h2⟩, fun hm => hn (memU hm)⟩, heq'⟩))
  · intro y hy
    rcases Finset.mem_union.mp hy with hy | hy
    · rcases Finset.mem_union.mp hy with hy | hy
      · exact colsOn_mono (S := T) (T := T ∪ U) (fun v hv => Finset.mem_union_left U hv) d hy
      · exact colsOn_mono (S := U) (T := T ∪ U) (fun v hv => Finset.mem_union_right T hv) d hy
    · obtain ⟨p, hp, he⟩ := Finset.mem_image.mp hy
      obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
      refine mem_colsOn.mpr ⟨s(p.1, p.2), ?_, he⟩
      refine mem_edgesOn_pair ?_ ?_ (hTU p.1 hp1 p.2 hp2)
      · exact Finset.mem_union_left U hp1
      · exact Finset.mem_union_right T hp2

/-! ### §4  THE MULTI-VERTEX PADDING CRITERION -/

/-- **THE CRITERION, FORWARD.**  An admissible colouring of `K_{n+m}` satisfies all five
conditions. -/
theorem padSet_of_admissible {n m k : ℕ} {d : Sym2 (Verts n ⊕ Verts m) → Fin k} (hd : AdmOn d) :
    PadSetOk d := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro T _ hT4
    exact hd T hT4
  · intro U _ hU4
    exact hd U hU4
  · intro T hT hT3 x hx
    have hxn : x ∉ T := fun hmem => not_isOld_isNew (hT x hmem) hx
    have hcard : (insert x T).card = 4 := by
      rw [Finset.card_insert_of_notMem hxn]
      omega
    rw [← cross_eq hxn]
    exact hd _ hcard
  · intro U hU hU3 w hw
    have hwn : w ∉ U := fun hmem => not_isOld_isNew hw (hU w hmem)
    have hcard : (insert w U).card = 4 := by
      rw [Finset.card_insert_of_notMem hwn]
      omega
    rw [← cross_eq hwn]
    exact hd _ hcard
  · intro T hT hT2 U hU hU2
    have hdisj : Disjoint T U := Finset.disjoint_left.2 fun v hvT hvU =>
      (isOld_ne_isNew (hT v hvT) (hU v hvU)) rfl
    have hcard : (T ∪ U).card = 4 := by
      rw [Finset.card_union_of_disjoint hdisj]
      omega
    rw [← quad_eq fun v hvT u hvU => isOld_ne_isNew (hT v hvT) (hU u hvU)]
    exact hd _ hcard

/-- A four-element set splits into an old part and a new part of total size four. -/
private theorem split_card {n m : ℕ} {S : Finset (Verts n ⊕ Verts m)} (hS : S.card = 4) :
    (S.filter IsOld).card + (S.filter (fun v => ¬ IsOld v)).card = 4 := by
  classical
  have h := Finset.card_filter_add_card_filter_not (s := S) (p := IsOld)
  omega

/-- ... and their union is the set itself. -/
private theorem split_union {n m : ℕ} (S : Finset (Verts n ⊕ Verts m)) :
    S.filter IsOld ∪ S.filter (fun v => ¬ IsOld v) = S := by
  apply Finset.Subset.antisymm
  · intro v hv
    rcases Finset.mem_union.mp hv with h | h
    · exact (Finset.mem_filter.mp h).1
    · exact (Finset.mem_filter.mp h).1
  · intro v hv
    by_cases hvv : IsOld v
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hv, hvv⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hv, hvv⟩)

/-- **THE CRITERION, BACKWARD.**  The five conditions certify admissibility of the extension.  The
proof splits a four-element set into its old and new parts, of sizes `(4,0)`, `(3,1)`, `(2,2)`,
`(1,3)` or `(0,4)` — the five conditions and nothing else. -/
theorem admissible_of_padSet {n m k : ℕ} {d : Sym2 (Verts n ⊕ Verts m) → Fin k}
    (h : PadSetOk d) : AdmOn d := by
  intro S hS
  have hsplit := split_card (S := S) hS
  have hunion := split_union S
  have hOld : ∀ v ∈ S.filter IsOld, IsOld v := by
    intro v hv
    exact (Finset.mem_filter.mp hv).2
  have hNew : ∀ v ∈ S.filter (fun v => ¬ IsOld v), IsNew v := by
    intro v hv
    obtain ⟨hv1, hv2⟩ := Finset.mem_filter.mp hv
    show ∃ u, v = Sum.inr u
    by_cases h : IsNew v
    · exact h
    · exfalso
      rcases v with w | y
      · exact hv2 ⟨w, rfl⟩
      · exact h ⟨y, rfl⟩
  have inS_of_union : ∀ v : Verts n ⊕ Verts m,
      v ∈ S.filter IsOld ∨ v ∈ S.filter (fun v => ¬ IsOld v) → v ∈ S := by
    intro v hv
    rw [← hunion]
    exact Finset.mem_union.mpr hv
  by_cases h4 : (S.filter IsOld).card = 4
  · have hN0 : (S.filter fun v => ¬ IsOld v).card = 0 := by omega
    have hNnil : S.filter (fun v => ¬ IsOld v) = ∅ := Finset.card_eq_zero.mp hN0
    have hOS : S.filter IsOld = S := by
      refine Finset.Subset.antisymm (fun v hv => (Finset.mem_filter.mp hv).1) ?_
      intro v hv
      by_cases hvv : IsOld v
      · exact Finset.mem_filter.mpr ⟨hv, hvv⟩
      · have hvm : v ∈ S.filter (fun w => ¬ IsOld w) := Finset.mem_filter.mpr ⟨hv, hvv⟩
        rw [hNnil] at hvm
        exact absurd hvm (by simp)
    rw [← hOS]
    exact h.1 (S.filter IsOld) hOld h4
  by_cases h0 : (S.filter IsOld).card = 0
  · have hN4 : (S.filter fun v => ¬ IsOld v).card = 4 := by omega
    have hOnil : S.filter IsOld = ∅ := Finset.card_eq_zero.mp h0
    have hNS : S.filter (fun v => ¬ IsOld v) = S := by
      refine Finset.Subset.antisymm (fun v hv => (Finset.mem_filter.mp hv).1) ?_
      intro v hv
      by_cases hvv : IsOld v
      · have hvm : v ∈ S.filter IsOld := Finset.mem_filter.mpr ⟨hv, hvv⟩
        rw [hOnil] at hvm
        exact absurd hvm (by simp)
      · exact Finset.mem_filter.mpr ⟨hv, hvv⟩
    rw [← hNS]
    exact h.2.1 (S.filter fun v => ¬ IsOld v) hNew hN4
  · by_cases h3 : (S.filter IsOld).card = 3
    · obtain ⟨x, hx⟩ :=
        Finset.card_pos.mp (show 1 ≤ (S.filter fun v => ¬ IsOld v).card by omega)
      have hxn : ¬ IsOld x := (Finset.mem_filter.mp hx).2
      have hxn' : x ∉ S.filter IsOld := fun hm => hxn ((Finset.mem_filter.mp hm).2)
      have hxnew : IsNew x := by
        rcases x with w | y
        · exact absurd (hxn ⟨w, rfl⟩) (by simp)
        · exact ⟨y, rfl⟩
      have hins : insert x (S.filter IsOld) ⊆ S := by
        intro v hv
        rcases Finset.mem_insert.mp hv with hxv | hv
        · exact hxv ▸ inS_of_union x (Or.inr hx)
        · exact inS_of_union v (Or.inl hv)
      have hsub2 : (colsOn d (S.filter IsOld))
          ∪ (S.filter IsOld).image (fun v => d s(v, x)) ⊆ colsOn d S := by
        rw [← cross_eq hxn']
        exact colsOn_mono hins d
      have h1 := h.2.2.1 (S.filter IsOld) hOld h3 x hxnew
      exact h1.trans (Finset.card_le_card hsub2)
    · by_cases h2 : (S.filter IsOld).card = 2
      · have hN2 : (S.filter fun v => ¬ IsOld v).card = 2 := by omega
        have hsubSU : S.filter IsOld ∪ S.filter (fun v => ¬ IsOld v) ⊆ S := by
          rw [hunion]
        have hA : ((colsOn d (S.filter IsOld)) ∪ colsOn d (S.filter fun v => ¬ IsOld v)) ∪
              ((S.filter IsOld).product (S.filter fun v => ¬ IsOld v)).image
                (fun p => d s(p.1, p.2))
            ⊆ colsOn d (S.filter IsOld ∪ S.filter (fun v => ¬ IsOld v)) := by
          rw [← quad_eq (fun v hvT u hvU => isOld_ne_isNew (hOld v hvT) (hNew u hvU))]
        have hsub2 : ((colsOn d (S.filter IsOld)) ∪ colsOn d (S.filter fun v => ¬ IsOld v)) ∪
              ((S.filter IsOld).product (S.filter fun v => ¬ IsOld v)).image
                (fun p => d s(p.1, p.2)) ⊆ colsOn d S :=
          hA.trans (colsOn_mono hsubSU d)
        have h1 := h.2.2.2.2 (S.filter IsOld) hOld h2
          (S.filter fun v => ¬ IsOld v) hNew hN2
        exact h1.trans (Finset.card_le_card hsub2)
      · have h1c : (S.filter IsOld).card = 1 := by omega
        obtain ⟨a, ha⟩ := Finset.card_pos.mp (show 1 ≤ (S.filter IsOld).card by omega)
        have hN3 : (S.filter fun v => ¬ IsOld v).card = 3 := by omega
        have ha' : IsOld a := (Finset.mem_filter.mp ha).2
        have hxn : a ∉ S.filter (fun v => ¬ IsOld v) :=
          fun hm => (Finset.mem_filter.mp hm).2 ha'
        have hins : insert a (S.filter fun v => ¬ IsOld v) ⊆ S := by
          intro v hv
          rcases Finset.mem_insert.mp hv with hav | hv
          · exact hav ▸ inS_of_union a (Or.inl ha)
          · exact inS_of_union v (Or.inr hv)
        have hsub2 : (colsOn d (S.filter fun v => ¬ IsOld v))
            ∪ (S.filter fun v => ¬ IsOld v).image (fun v => d s(v, a)) ⊆ colsOn d S := by
          rw [← cross_eq hxn]
          exact colsOn_mono hins d
        have h1 := h.2.2.2.1 (S.filter fun v => ¬ IsOld v) hNew hN3 a ha'
        exact h1.trans (Finset.card_le_card hsub2)

/-- **THE MULTI-VERTEX PADDING CRITERION.**  A colouring of `K_{n+m}` is admissible **iff** its old
side, its new side and the `3+1`, `1+3`, `2+2` shapes of four-sets satisfy the five conditions.
For `m = 1` this is `Pad.admissible_iff_padOk`. -/
theorem admissible_iff_padSet {n m k : ℕ} (d : Sym2 (Verts n ⊕ Verts m) → Fin k) :
    AdmOn d ↔ PadSetOk d :=
  ⟨padSet_of_admissible, admissible_of_padSet⟩


/-! ### §5  What the criterion forces on the star matrix -/

/-- **NO COLOUR OCCURS THREE TIMES IN A COLUMN.**  If three distinct old vertices give the same
colour to one new vertex, the four-set they form spans at most four colours, so the extension is
not admissible. -/
theorem fibre_le_two_of_triOld {n m k : ℕ} {d : Sym2 (Verts n ⊕ Verts m) → Fin k} (hp : TriOld d)
    (y : Verts m) (i : Fin k) :
    ((Finset.univ : Finset (Verts n)).filter (fun w => Star d w y = i)).card ≤ 2 := by
  by_contra hc
  push Not at hc
  obtain ⟨a, b, c, ha, hb, hc', hab, hac, hbc⟩ := exists_three_mem' hc
  have ha' : d s(Sum.inl a, Sum.inr y) = i := (Finset.mem_filter.mp ha).2
  have hb' : d s(Sum.inl b, Sum.inr y) = i := (Finset.mem_filter.mp hb).2
  have hcx : d s(Sum.inl c, Sum.inr y) = i := (Finset.mem_filter.mp hc').2
  set T := insert (Sum.inl a) (insert (Sum.inl b) (insert (Sum.inl c)
    (∅ : Finset (Verts n ⊕ Verts m)))) with hT
  have hTcard : T.card = 3 := by rw [hT]; simp [hab, hac, hbc]
  have hTold : ∀ v ∈ T, IsOld v := by
    intro v hv
    rw [hT] at hv
    rcases Finset.mem_insert.mp hv with hv | hv
    · exact ⟨a, hv⟩
    · rcases Finset.mem_insert.mp hv with hv | hv
      · exact ⟨b, hv⟩
      · rcases Finset.mem_insert.mp hv with hv | hv
        · exact ⟨c, hv⟩
        · exact absurd hv (by simp)
  have himg : T.image (fun v => d s(v, Sum.inr y)) ⊆ insert i (∅ : Finset (Fin k)) := by
    intro z hz
    obtain ⟨v, hv, he⟩ := Finset.mem_image.mp hz
    rw [hT] at hv
    rw [← he]
    rcases Finset.mem_insert.mp hv with hv | hv
    · rw [hv, ha']
      exact Finset.mem_insert_self _ _
    · rcases Finset.mem_insert.mp hv with hv | hv
      · rw [hv, hb']
        exact Finset.mem_insert_self _ _
      · rcases Finset.mem_insert.mp hv with hv | hv
        · rw [hv, hcx]
          exact Finset.mem_insert_self _ _
        · exact absurd hv (by simp)
  have hle : ((colsOn d T) ∪ T.image (fun v => d s(v, Sum.inr y))).card ≤ 4 := by
    have h1 := card_colsOn_three d hTcard
    have h2 : (T.image (fun v => d s(v, Sum.inr y))).card ≤ 1 :=
      (Finset.card_le_card himg).trans (by simp)
    calc ((colsOn d T) ∪ T.image (fun v => d s(v, Sum.inr y))).card
        ≤ (colsOn d T).card + (T.image (fun v => d s(v, Sum.inr y))).card :=
          Finset.card_union_le _ _
      _ ≤ 3 + 1 := by omega
      _ ≤ 4 := by omega
  have h1 := hp T hTold hTcard (Sum.inr y) ⟨y, rfl⟩
  rw [hT] at h1 hle
  omega

/-- **NO COLOUR OCCURS THREE TIMES IN A ROW.**  If three distinct new vertices receive the same
colour from one old vertex, the four-set they form spans at most four colours.  This is the
one-vertex statement `Pad.padOk_fibre_le_two` in the multi-vertex setting. -/
theorem fibre_le_two_of_triNew {n m k : ℕ} {d : Sym2 (Verts n ⊕ Verts m) → Fin k} (hp : TriNew d)
    (w : Verts n) (i : Fin k) :
    ((Finset.univ : Finset (Verts m)).filter (fun u => Star d w u = i)).card ≤ 2 := by
  by_contra hc
  push Not at hc
  obtain ⟨a, b, c, ha, hb, hc', hab, hac, hbc⟩ := exists_three_mem' hc
  have ha' : d s(Sum.inl w, Sum.inr a) = i := (Finset.mem_filter.mp ha).2
  have hb' : d s(Sum.inl w, Sum.inr b) = i := (Finset.mem_filter.mp hb).2
  have hcx : d s(Sum.inl w, Sum.inr c) = i := (Finset.mem_filter.mp hc').2
  set U := insert (Sum.inr a) (insert (Sum.inr b) (insert (Sum.inr c)
    (∅ : Finset (Verts n ⊕ Verts m)))) with hU
  have hUcard : U.card = 3 := by rw [hU]; simp [hab, hac, hbc]
  have hUnew : ∀ v ∈ U, IsNew v := by
    intro v hv
    rw [hU] at hv
    rcases Finset.mem_insert.mp hv with hv | hv
    · exact ⟨a, hv⟩
    · rcases Finset.mem_insert.mp hv with hv | hv
      · exact ⟨b, hv⟩
      · rcases Finset.mem_insert.mp hv with hv | hv
        · exact ⟨c, hv⟩
        · exact absurd hv (by simp)
  have hz : d s(Sum.inr a, Sum.inl w) = i :=
    (congrArg d (Sym2.eq_swap : s(Sum.inl w, Sum.inr a) = s(Sum.inr a, Sum.inl w))).symm.trans ha'
  have hzc : d s(Sum.inr b, Sum.inl w) = i :=
    (congrArg d (Sym2.eq_swap : s(Sum.inl w, Sum.inr b) = s(Sum.inr b, Sum.inl w))).symm.trans hb'
  have hzd : d s(Sum.inr c, Sum.inl w) = i :=
    (congrArg d (Sym2.eq_swap : s(Sum.inl w, Sum.inr c) = s(Sum.inr c, Sum.inl w))).symm.trans hcx
  have himg : U.image (fun v => d s(v, Sum.inl w)) ⊆ insert i (∅ : Finset (Fin k)) := by
    intro z hz'
    obtain ⟨v, hv, he⟩ := Finset.mem_image.mp hz'
    rw [hU] at hv
    rw [← he]
    rcases Finset.mem_insert.mp hv with hv | hv
    · rw [hv, hz]
      exact Finset.mem_insert_self _ _
    · rcases Finset.mem_insert.mp hv with hv | hv
      · rw [hv, hzc]
        exact Finset.mem_insert_self _ _
      · rcases Finset.mem_insert.mp hv with hv | hv
        · rw [hv, hzd]
          exact Finset.mem_insert_self _ _
        · exact absurd hv (by simp)
  have hle : ((colsOn d U) ∪ U.image (fun v => d s(v, Sum.inl w))).card ≤ 4 := by
    have h1 := card_colsOn_three d hUcard
    have h2 : (U.image (fun v => d s(v, Sum.inl w))).card ≤ 1 :=
      (Finset.card_le_card himg).trans (by simp)
    calc ((colsOn d U) ∪ U.image (fun v => d s(v, Sum.inl w))).card
        ≤ (colsOn d U).card + (U.image (fun v => d s(v, Sum.inl w))).card :=
          Finset.card_union_le _ _
      _ ≤ 3 + 1 := by omega
      _ ≤ 4 := by omega
  have h1 := hp U hUnew hUcard (Sum.inl w) ⟨w, rfl⟩
  rw [hU] at h1 hle
  omega

/-- **A COLUMN TAKES AT LEAST `⌈n/2⌉` VALUES.**  The `n` cross edges of a new vertex carry at least
`⌈n/2⌉` different colours.  This is `Pad.padOk_image_card` for a six-step. -/
theorem image_card_le {n m k : ℕ} {d : Sym2 (Verts n ⊕ Verts m) → Fin k} (hp : TriOld d)
    (y : Verts m) :
    n ≤ 2 * ((Finset.univ : Finset (Verts n)).image (fun w => Star d w y)).card := by
  have hsum : (Finset.univ : Finset (Verts n)).card
      = ∑ b ∈ (Finset.univ : Finset (Verts n)).image (fun w => Star d w y),
        ((Finset.univ : Finset (Verts n)).filter (fun w => Star d w y = b)).card :=
    Finset.card_eq_sum_card_image (fun w => Star d w y) _
  calc n = (Finset.univ : Finset (Verts n)).card := by simp
    _ = ∑ b ∈ (Finset.univ : Finset (Verts n)).image (fun w => Star d w y),
        ((Finset.univ : Finset (Verts n)).filter (fun w => Star d w y = b)).card := hsum
    _ ≤ ∑ _ ∈ (Finset.univ : Finset (Verts n)).image (fun w => Star d w y), 2 :=
      Finset.sum_le_sum fun b hb => by exact fibre_le_two_of_triOld (d := d) hp y b
    _ = 2 * ((Finset.univ : Finset (Verts n)).image (fun w => Star d w y)).card := by
      rw [Finset.sum_const_nat (fun _ _ => rfl)]
      omega

/-- **A ROW TAKES AT LEAST `⌈m/2⌉` VALUES.**  The `m` cross edges of an old vertex carry at least
`⌈m/2⌉` different colours.  **This is the first constraint that a six-step search can check on the
star matrix alone, and at the `K₁₂` anchor (six new vertices) it says that every old vertex must
see at least three of the `j+5` colours.** -/
theorem image_card_le' {n m k : ℕ} {d : Sym2 (Verts n ⊕ Verts m) → Fin k} (hp : TriNew d)
    (w : Verts n) :
    m ≤ 2 * ((Finset.univ : Finset (Verts m)).image (fun u => Star d w u)).card := by
  have hsum : (Finset.univ : Finset (Verts m)).card
      = ∑ b ∈ (Finset.univ : Finset (Verts m)).image (fun u => Star d w u),
        ((Finset.univ : Finset (Verts m)).filter (fun u => Star d w u = b)).card :=
    Finset.card_eq_sum_card_image (fun u => Star d w u) _
  calc m = (Finset.univ : Finset (Verts m)).card := by simp
    _ = ∑ b ∈ (Finset.univ : Finset (Verts m)).image (fun u => Star d w u),
        ((Finset.univ : Finset (Verts m)).filter (fun u => Star d w u = b)).card := hsum
    _ ≤ ∑ _ ∈ (Finset.univ : Finset (Verts m)).image (fun u => Star d w u), 2 :=
      Finset.sum_le_sum fun b hb => by exact fibre_le_two_of_triNew (d := d) hp w b
    _ = 2 * ((Finset.univ : Finset (Verts m)).image (fun u => Star d w u)).card := by
      rw [Finset.sum_const_nat (fun _ _ => rfl)]
      omega

/-- **THE COLUMN-PAIR SEPARATION.**  If two old vertices give the same colour to two distinct new
vertices, the four-set they form spans at most four colours — the two old-old and new-new colours,
plus the two repeated star colours. -/
private theorem star_prod_card_le_two {n m k : ℕ} {d : Sym2 (Verts n ⊕ Verts m) → Fin k}
    {w v : Verts n} {x y : Verts m}
    (h1 : Star d w x = Star d v x) (h2 : Star d w y = Star d v y) :
    (((insert (Sum.inl w) (insert (Sum.inl v) (∅ : Finset (Verts n ⊕ Verts m)))).product
        (insert (Sum.inr x) (insert (Sum.inr y)
          (∅ : Finset (Verts n ⊕ Verts m))))).image (fun p => d s(p.1, p.2))).card ≤ 2 := by
  set T := insert (Sum.inl w) (insert (Sum.inl v) (∅ : Finset (Verts n ⊕ Verts m))) with hT
  set U := insert (Sum.inr x) (insert (Sum.inr y)
    (∅ : Finset (Verts n ⊕ Verts m))) with hU
  have h1'' : d s(Sum.inl w, Sum.inr x) = d s(Sum.inl v, Sum.inr x) := h1
  have h2'' : d s(Sum.inl w, Sum.inr y) = d s(Sum.inl v, Sum.inr y) := h2
  have hsub : (T.product U).image (fun p => d s(p.1, p.2)) ⊆
      insert (d s(Sum.inl w, Sum.inr x)) (insert (d s(Sum.inl w, Sum.inr y))
        (∅ : Finset (Fin k))) := by
    intro z hz
    obtain ⟨p, hp, he⟩ := Finset.mem_image.mp hz
    obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
    rw [hT] at hp1
    rw [hU] at hp2
    rw [← he]
    rcases Finset.mem_insert.mp hp1 with e1 | e1
    · rcases Finset.mem_insert.mp hp2 with e2 | e2
      · rw [e1, e2]
        exact Finset.mem_insert_self (d s(Sum.inl w, Sum.inr x))
          (insert (d s(Sum.inl w, Sum.inr y)) (∅ : Finset (Fin k)))
      · rcases Finset.mem_insert.mp e2 with e2 | e2
        · rw [e1, e2]
          exact Finset.mem_insert_of_mem
            (Finset.mem_insert_self (d s(Sum.inl w, Sum.inr y)) (∅ : Finset (Fin k)))
        · exact absurd e2 (by simp)
    · rcases Finset.mem_insert.mp e1 with e1 | e1
      · rcases Finset.mem_insert.mp hp2 with e2 | e2
        · rw [e1, e2, h1'']
          exact Finset.mem_insert_self (d s(Sum.inl v, Sum.inr x))
            (insert (d s(Sum.inl w, Sum.inr y)) (∅ : Finset (Fin k)))
        · rcases Finset.mem_insert.mp e2 with e2 | e2
          · rw [e1, e2, h2'']
            exact Finset.mem_insert_of_mem
              (Finset.mem_insert_self (d s(Sum.inl v, Sum.inr y)) (∅ : Finset (Fin k)))
          · exact absurd e2 (by simp)
      · exact absurd e1 (by simp)
  have h2 : (insert (d s(Sum.inl w, Sum.inr y)) (∅ : Finset (Fin k))).card ≤ 1 := by
    rw [Finset.card_insert_of_notMem (by simp)]
    simp
  have h1 : (insert (d s(Sum.inl w, Sum.inr x))
      (insert (d s(Sum.inl w, Sum.inr y)) (∅ : Finset (Fin k)))).card
      ≤ (insert (d s(Sum.inl w, Sum.inr y)) (∅ : Finset (Fin k))).card + 1 :=
    Finset.card_insert_le _ _
  have h3 := Finset.card_le_card hsub
  omega

/-- **NO `2 × 2` MONOCHROMATIC BLOCK.**  For two distinct new vertices the map
`w ↦ (Star d w x, Star d w y)` from the old vertices to colour pairs is **injective**: two old
vertices never agree on two new vertices at once.  This is the combinatorial core of a six-step — a
repeated colour in one column must be paid for by fresh colours in every other column, and it
cannot be paid twice. -/
theorem pair_inj {n m k : ℕ} {d : Sym2 (Verts n ⊕ Verts m) → Fin k} (hp : PairOk d)
    {x y : Verts m} (hxy : x ≠ y) :
    Function.Injective (fun w : Verts n => (Star d w x, Star d w y)) := by
  intro w v heq
  have h1 : Star d w x = Star d v x := congrArg Prod.fst heq
  have h2 : Star d w y = Star d v y := congrArg Prod.snd heq
  by_contra hcon
  have hwv : w ≠ v := hcon
  set T := insert (Sum.inl w) (insert (Sum.inl v) (∅ : Finset (Verts n ⊕ Verts m))) with hT
  set U := insert (Sum.inr x) (insert (Sum.inr y)
    (∅ : Finset (Verts n ⊕ Verts m))) with hU
  have hTcard : T.card = 2 := by rw [hT]; simp [hwv]
  have hUcard : U.card = 2 := by rw [hU]; simp [hxy]
  have hTold : ∀ e ∈ T, IsOld e := by
    intro e he
    rw [hT] at he
    rcases Finset.mem_insert.mp he with he | he
    · exact ⟨w, he⟩
    · rcases Finset.mem_insert.mp he with he | he
      · exact ⟨v, he⟩
      · exact absurd he (by simp)
  have hUnew : ∀ e ∈ U, IsNew e := by
    intro e he
    rw [hU] at he
    rcases Finset.mem_insert.mp he with he | he
    · exact ⟨x, he⟩
    · rcases Finset.mem_insert.mp he with he | he
      · exact ⟨y, he⟩
      · exact absurd he (by simp)
  have h1' := hp T hTold hTcard U hUnew hUcard
  have hTc : (colsOn d T).card = 1 := by
    have hle := card_colsOn_le d hTcard
    have hle' : (colsOn d T).card ≤ 1 := by simpa using hle
    have hge : 1 ≤ (colsOn d T).card := by
      refine Finset.one_le_card.2 ⟨_, mem_colsOn.mpr ⟨s(Sum.inl w, Sum.inl v), ?_, rfl⟩⟩
      exact mem_edgesOn_pair
        (Finset.mem_insert_self (Sum.inl w) (insert (Sum.inl v) (∅ : Finset (Verts n ⊕ Verts m))))
        (Finset.mem_insert_of_mem (Finset.mem_insert_self (Sum.inl v)
          (∅ : Finset (Verts n ⊕ Verts m))))
        (fun h => hwv (Sum.inl.inj h))
    omega
  have hUc : (colsOn d U).card = 1 := by
    have hle := card_colsOn_le d hUcard
    have hle' : (colsOn d U).card ≤ 1 := by simpa using hle
    have hge : 1 ≤ (colsOn d U).card := by
      refine Finset.one_le_card.2 ⟨_, mem_colsOn.mpr ⟨s(Sum.inr x, Sum.inr y), ?_, rfl⟩⟩
      exact mem_edgesOn_pair
        (Finset.mem_insert_self (Sum.inr x) (insert (Sum.inr y) (∅ : Finset (Verts n ⊕ Verts m))))
        (Finset.mem_insert_of_mem (Finset.mem_insert_self (Sum.inr y)
          (∅ : Finset (Verts n ⊕ Verts m))))
        (fun h => hxy (Sum.inr.inj h))
    omega
  have himg := star_prod_card_le_two h1 h2
  rw [← hT, ← hU] at himg
  have hA := Finset.card_union_le (colsOn d T ∪ colsOn d U)
    ((T.product U).image (fun p => d s(p.1, p.2)))
  have hB := Finset.card_union_le (colsOn d T) (colsOn d U)
  omega

end JSP140
