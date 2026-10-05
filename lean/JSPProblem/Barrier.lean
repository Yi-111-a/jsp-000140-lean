import JSPProblem.Moment
import JSPProblem.Spoil

/-!
# JSP-000140 — round 91: **THE UNION-BOUND BARRIER** — the first moment of the *uniform* random
colouring cannot produce an admissible colouring at any palette size `≤ n + 1`, so any formalisation
of `Main.AdmissibleUpper` must use a **correlated** random colouring

Ninety rounds of this development have reduced the prize statement `jsp_000140_main` to the single
hypothesis `Main.AdmissibleUpper ε` (`0 < ε < 1/6`): the *existence*, for all large `n`, of a
`k ≤ 5n/6 + εn`-edge-colouring of `K_n` in which every `K₄` spans at least five colours.  Both
published proofs are probabilistic (arXiv:2207.02920 §4/§12, arXiv:2208.12563 §4); no such proof
has ever been reproduced here.  Every attempt in the development has gone through deterministic
objects instead — fusions of colour classes (rounds 65–87), four-set censuses (rounds 60–64), path
factors (round 90), the Rödl nibble (round 88).

This file analyses the **simplest** probabilistic proof of `AdmissibleUpper` — the one every such
proof is tempted to use, namely

> draw a colouring of the `C(n,2)` edges of `K_n` **uniformly at random** out of the `k^C(n,2)`
> candidates, and show that the mean number of four-sets spanning at most four colours is `< 1`.

It has two halves, and both are theorems about **all** `k`-colourings of `K_n`.

* **§4 — THE CRITERION (positive).**  `Barrier.unionBound`: in the language of integer weights
  `w c ≥ 0` on colourings, a weighted mean of failing four-sets below `1` certifies the existence
  of an admissible colouring.  `Barrier.AdmissibleUpper_of_firstMoment` then bridges it to the
  prize: a weight function meeting the criterion at every order, with the palette already inside
  the catalogue window, *implies* `AdmissibleUpper ε`.  This is a reusable sufficient condition,
  and it is the shape of statement any Lean formalisation of the probabilistic first stage must
  end with.
* **§3, §5 — THE BARRIER (negative).**  For the uniform distribution the mean number of failing
  four-sets is at least `C(n,4)/k²` (`Barrier.firstMoment_ge`), so the criterion fails as soon as
  `k² ≤ C(n,4)`, i.e. for every `k ≤ n + 1`, because `C(n,4) ≥ n²` for `n ≥ 8`
  (`Barrier.choose_four_ge_sq`) and `C(n,4) = Ω(n⁴)` (`Barrier.choose_four_ge`).  Hence
  **`Barrier.no_certificate_below_trivial`: for `n ≥ 8` the uniform first moment certifies nothing
  for any palette size `2 ≤ k ≤ n + 1`** — while `Construction.EG_le_succ : EG n ≤ n + 1` is an
  explicit admissible colouring.  Quantitatively, `Barrier.firstMoment_needs_quadratic`: a palette
  certified by the uniform first moment must satisfy `n⁴ ≤ 192 k²`, i.e. `k ≥ n²/14`, **a factor
  `Θ(n)` worse than the trivial construction.**

Consequently the probabilistic content of `AdmissibleUpper` must come from a **correlated** random
colouring — the triangle-structure / nibble route of the two papers — and `Barrier.gain_needed`
names the price: the per-four-set failure probability must drop from `Θ(k⁻²) = Θ(36n⁻²)` to
`o(C(n,4)⁻¹) = o(24n⁻⁴)`, a gain of order `n²`.

This is the first rigorous obstruction in the development to the *existence* half of the prize.
-/

namespace JSP140

noncomputable section

variable {n k : ℕ}

/-! ### §0  Counting colourings prescribed on a set of edges

Everything in this file is a *finite counting* statement: no probability and no measure occur.
The only tool needed is the count of functions out of a finite type which are prescribed on a
sub-finset. -/

/-- **COLOURINGS PRESCRIBED ON A SET OF EDGES.**  If a map is forced to take the value `p x` at
every `x ∈ R`, the remaining points are free: `|β|^(card α - card R)` choices. -/
def presetEquiv {α : Type*} [Fintype α] [DecidableEq α] {β : Type*} (R : Finset α) (p : α → β) :
    {c : α → β // ∀ x ∈ R, c x = p x} ≃ ({x : α // x ∉ R} → β) where
  toFun c := fun x => c.1 x
  invFun f := ⟨fun x => if hx : x ∈ R then p x else f ⟨x, hx⟩, by
    intro x hx
    show (if hx : x ∈ R then p x else f ⟨x, hx⟩) = p x
    rw [dif_pos hx]⟩
  left_inv c := Subtype.ext (funext fun x => by
    by_cases hx : x ∈ R
    · simpa only [dif_pos hx] using (c.2 x hx).symm
    · simpa only [dif_neg hx])
  right_inv f := by
    funext x
    show (if hx : (x : α) ∈ R then p x else f ⟨x, x.property⟩) = f x
    rw [dif_neg x.property]

/-- **`|{c : α → β // c x = p x for x ∈ R}| = |β|^(card α - card R)`.** -/
theorem card_preset {α : Type*} [Fintype α] [DecidableEq α] {β : Type*} [Fintype β]
    [DecidableEq β] (R : Finset α) (p : α → β) :
    Fintype.card {c : α → β // ∀ x ∈ R, c x = p x}
      = Fintype.card β ^ (Fintype.card α - R.card) := by
  rw [Fintype.card_congr (presetEquiv R p), Fintype.card_fun]
  congr 1
  have hcard : Fintype.card {x : α // x ∉ R} = Fintype.card α - R.card := by
    rw [Fintype.card_subtype_compl, Fintype.card_coe]
  rw [hcard]

/-- **THE NUMBER OF `k`-COLOURINGS OF `K_n`.** -/
theorem card_col {n k : ℕ} : Fintype.card (Col n k) = k ^ Fintype.card (Sym2 (Verts n)) := by
  rw [Fintype.card_fun, Fintype.card_fin]

/-- **`K_n` HAS AT LEAST SIX EDGES AS SOON AS IT HAS FOUR VERTICES.** -/
theorem card_Sym2_ge_six {n : ℕ} (a b c' d : Verts n) (h : FourDistinct a b c' d) :
    6 ≤ Fintype.card (Sym2 (Verts n)) := by
  have h3 : (edgeFinset (fourSet a b c' d)).card = 6 := card_edgeFinset_four (card_fourSet h)
  have h2 := Finset.card_le_univ (edgeFinset (fourSet a b c' d))
  omega

/-- **FOUR NESTED INSERTS HAVE AT MOST FOUR ELEMENTS.** -/
private theorem card_insert4 {α : Type*} [DecidableEq α] (a b c' d : α) :
    ((insert a (insert b (insert c' (insert d ∅))) : Finset α)).card ≤ 4 := by
  rw [Finset.insert_eq, Finset.insert_eq, Finset.insert_eq, Finset.insert_eq]
  exact le_trans (Finset.card_le_card (Finset.Subset.rfl)) (card_four_le a b c' d)

/-- **THE CARD OF A FILTER IS THE CARD OF THE CORRESPONDING SUBTYPE.** -/
private theorem card_subtype_filter {α : Type*} [Fintype α] {P : α → Prop} [DecidablePred P] :
    ((Finset.univ : Finset α).filter P).card = Fintype.card {x // P x} := by
  have e : {x : α // P x} ≃ (((Finset.univ : Finset α).filter P) : Finset α) :=
    { toFun := fun x => ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, x.property⟩⟩
      invFun := fun y => ⟨y.1, (Finset.mem_filter.mp y.property).2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Fintype.card_congr e, Fintype.card_coe]

/-! ### §1  The six edges of a `K₄` -/

/-- The six edges of the `K₄` spanned by four distinct vertices. -/
noncomputable def sixEdges {n : ℕ} (a b c' d : Verts n) : Finset (Sym2 (Verts n)) :=
  insert (s(a, b))
    (insert (s(a, c'))
      (insert (s(a, d))
        (insert (s(b, c')) (insert (s(b, d)) (insert (s(c', d)) ∅)))))

@[simp] theorem mem_sixEdges {n : ℕ} (a b c' d : Verts n) {e : Sym2 (Verts n)} :
    e ∈ sixEdges a b c' d ↔ e = s(a, b) ∨ e = s(a, c') ∨ e = s(a, d) ∨ e = s(b, c')
      ∨ e = s(b, d) ∨ e = s(c', d) := by
  simp only [sixEdges, Finset.mem_insert]
  tauto

/-- **A PAIR OF VERTICES OF A FOUR-SET SPANS ONE OF THE SIX EDGES.** -/
private theorem mem_sixEdges_pair {n : ℕ} {a b c' d x y : Verts n}
    (hx : x = a ∨ x = b ∨ x = c' ∨ x = d) (hy : y = a ∨ y = b ∨ y = c' ∨ y = d)
    (hne : x ≠ y) : s(x, y) ∈ sixEdges a b c' d := by
  rw [mem_sixEdges]
  rcases hx with hx | hx | hx | hx <;> rcases hy with hy | hy | hy | hy
  · exact False.elim (hne (hy.trans hx.symm).symm)
  · rw [hx, hy]; refine Or.inl ?_; first | rfl | exact Sym2.eq_swap | exact Sym2.eq_swap.symm
  · rw [hx, hy]; refine Or.inr (Or.inl ?_); first | rfl | exact Sym2.eq_swap | exact Sym2.eq_swap.symm
  · rw [hx, hy]; refine Or.inr (Or.inr (Or.inl ?_)); first | rfl | exact Sym2.eq_swap | exact Sym2.eq_swap.symm
  · rw [hx, hy]; refine Or.inl ?_; first | rfl | exact Sym2.eq_swap | exact Sym2.eq_swap.symm
  · exact False.elim (hne (hy.trans hx.symm).symm)
  · rw [hx, hy]; refine Or.inr (Or.inr (Or.inr (Or.inl ?_))); first | rfl | exact Sym2.eq_swap | exact Sym2.eq_swap.symm
  · rw [hx, hy]; refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))); first | rfl | exact Sym2.eq_swap | exact Sym2.eq_swap.symm
  · rw [hx, hy]; refine Or.inr (Or.inl ?_); first | rfl | exact Sym2.eq_swap | exact Sym2.eq_swap.symm
  · rw [hx, hy]; refine Or.inr (Or.inr (Or.inr (Or.inl ?_))); first | rfl | exact Sym2.eq_swap | exact Sym2.eq_swap.symm
  · exact False.elim (hne (hy.trans hx.symm).symm)
  · rw [hx, hy]; refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (?_))))); first | rfl | exact Sym2.eq_swap | exact Sym2.eq_swap.symm
  · rw [hx, hy]; refine Or.inr (Or.inr (Or.inl ?_)); first | rfl | exact Sym2.eq_swap | exact Sym2.eq_swap.symm
  · rw [hx, hy]; refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))); first | rfl | exact Sym2.eq_swap | exact Sym2.eq_swap.symm
  · rw [hx, hy]; refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (?_))))); first | rfl | exact Sym2.eq_swap | exact Sym2.eq_swap.symm
  · exact False.elim (hne (hy.trans hx.symm).symm)

/-- **THE EDGES OF A FOUR-SET ARE ITS SIX PAIRS.** -/
theorem edgeFinset_fourSet {n : ℕ} {a b c' d : Verts n} (h : FourDistinct a b c' d) :
    edgeFinset (fourSet a b c' d) = sixEdges a b c' d := by
  apply Finset.Subset.antisymm
  · intro e
    refine (Sym2.inductionOn e ?_)
    intro x y he
    simp only [mem_edgeFinset, Finset.mk_mem_sym2_iff, mem_fourSet h] at he
    obtain ⟨⟨hx, hy⟩, hne⟩ := he
    exact mem_sixEdges_pair hx hy (offDiag_iff.mp hne)
  · intro e he
    rw [mem_sixEdges] at he
    have ha : a ∈ fourSet a b c' d := (mem_fourSet h (x := a)).2 (Or.inl rfl)
    have hb : b ∈ fourSet a b c' d := (mem_fourSet h (x := b)).2 (Or.inr (Or.inl rfl))
    have hc : c' ∈ fourSet a b c' d := (mem_fourSet h (x := c')).2 (Or.inr (Or.inr (Or.inl rfl)))
    have hd : d ∈ fourSet a b c' d := (mem_fourSet h (x := d)).2 (Or.inr (Or.inr (Or.inr rfl)))
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl
    · exact mem_edgeFinset_mk ha hb h.1
    · exact mem_edgeFinset_mk ha hc h.2.1
    · exact mem_edgeFinset_mk ha hd h.2.2.1
    · exact mem_edgeFinset_mk hb hc h.2.2.2.1
    · exact mem_edgeFinset_mk hb hd h.2.2.2.2.1
    · exact mem_edgeFinset_mk hc hd h.2.2.2.2.2

/-! ### §2  Two of the three perfect matchings of a `K₄` in two colours

The three perfect matchings of a `K₄` are `{a,b}{c',d}`, `{a,c'}{b,d}`, `{a,d}{b,c'}`.  If **two of
them are monochromatic**, the six edges of the `K₄` span at most `2 + 2 = 4` colours, so the
catalog condition fails.  This is the cheapest possible source of failing four-sets, and §3 counts
how many colourings it produces. -/

/-- The four edges of the two matchings `{a,b}, {c',d}` and `{a,c'}, {b,d}`. -/
noncomputable def twoMatchings {n : ℕ} (a b c' d : Verts n) : Finset (Sym2 (Verts n)) :=
  insert (s(a, b))
    (insert (s(a, c')) (insert (s(c', d)) (insert (s(b, d)) ∅)))

@[simp] theorem mem_twoMatchings {n : ℕ} (a b c' d : Verts n) {e : Sym2 (Verts n)} :
    e ∈ twoMatchings a b c' d ↔ e = s(a, b) ∨ e = s(a, c') ∨ e = s(c', d) ∨ e = s(b, d) := by
  simp only [twoMatchings, Finset.mem_insert]
  tauto

/-- **THE TWO MATCHINGS ARE FOUR DIFFERENT EDGES.** -/
theorem card_twoMatchings {n : ℕ} {a b c' d : Verts n} (h : FourDistinct a b c' d) :
    (twoMatchings a b c' d).card = 4 := by
  refine (Finset.card_eq_four).2
    ⟨s(a, b), s(a, c'), s(c', d), s(b, d), ?_, ?_, ?_, ?_, ?_, ?_, rfl⟩
  · intro he
    rcases sym2_inj he with ⟨_, hB⟩ | ⟨hA, _⟩
    · exact h.2.2.2.1 hB
    · exact h.2.1 hA
  · intro he
    rcases sym2_inj he with ⟨hA, _⟩ | ⟨hA, _⟩
    · exact h.2.1 hA
    · exact h.2.2.1 hA
  · intro he
    rcases sym2_inj he with ⟨hA, _⟩ | ⟨hA, _⟩
    · exact h.1 hA
    · exact h.2.2.1 hA
  · intro he
    rcases sym2_inj he with ⟨hA, _⟩ | ⟨hA, _⟩
    · exact h.2.1 hA
    · exact h.2.2.1 hA
  · intro he
    rcases sym2_inj he with ⟨hA, _⟩ | ⟨hA, _⟩
    · exact h.1 hA
    · exact h.2.2.1 hA
  · intro he
    rcases sym2_inj he with ⟨hA, _⟩ | ⟨hA, _⟩
    · exact h.2.2.2.1 hA.symm
    · exact h.2.2.2.2.2 hA

/-- **TWO MONOCHROMATIC MATCHINGS.**  `c` is the constant `v` on `{a,b}, {c',d}` and the constant
`w` on `{a,c'}, {b,d}`: `c` is *prescribed* on the four edges of the two matchings. -/
def TwoMono {n k : ℕ} (c : Col n k) (a b c' d : Verts n) (v w : Fin k) : Prop :=
  ∀ e ∈ twoMatchings a b c' d, c e = if e = s(a, b) ∨ e = s(c', d) then v else w

noncomputable instance decTwoMono {n k : ℕ} (a b c' d : Verts n) (v w : Fin k) :
    DecidablePred (fun c : Col n k => TwoMono c a b c' d v w) :=
  fun _ => Classical.propDecidable _

/-- **THE FOUR EQUATIONS OF "TWO MONOCHROMATIC MATCHINGS".** -/
theorem TwoMono_eq {n k : ℕ} {a b c' d : Verts n} (h : FourDistinct a b c' d) (c : Col n k)
    (v w : Fin k) :
    TwoMono c a b c' d v w ↔
      (c s(a, b) = v ∧ c s(c', d) = v ∧ c s(a, c') = w ∧ c s(b, d) = w) := by
  have n1 : s(a, c') ≠ s(a, b) := by
    intro he
    rcases sym2_inj he with ⟨_, hB⟩ | ⟨hA, _⟩
    · exact h.2.2.2.1 hB.symm
    · exact h.1 hA
  have n2 : s(a, c') ≠ s(c', d) := by
    intro he
    rcases sym2_inj he with ⟨hA, _⟩ | ⟨hA, _⟩
    · exact h.2.1 hA
    · exact h.2.2.1 hA
  have n3 : s(b, d) ≠ s(a, b) := by
    intro he
    rcases sym2_inj he with ⟨hA, _⟩ | ⟨_, hB⟩
    · exact h.1 hA.symm
    · exact h.2.2.1 hB.symm
  have n4 : s(b, d) ≠ s(c', d) := by
    intro he
    rcases sym2_inj he with ⟨hA, _⟩ | ⟨hA, _⟩
    · exact h.2.2.2.1 hA
    · exact h.2.2.2.2.1 hA
  constructor
  · rintro he1
    have e1 := he1 s(a, b) ((mem_twoMatchings a b c' d).2 (Or.inl rfl))
    have e2 := he1 s(c', d) ((mem_twoMatchings a b c' d).2 (Or.inr (Or.inr (Or.inl rfl))))
    have e3 := he1 s(a, c') ((mem_twoMatchings a b c' d).2 (Or.inr (Or.inl rfl)))
    have e4 := he1 s(b, d) ((mem_twoMatchings a b c' d).2 (Or.inr (Or.inr (Or.inr rfl))))
    have c1 : s(a, b) = s(a, b) ∨ s(a, b) = s(c', d) := Or.inl rfl
    have c2 : s(a, c') = s(a, b) ∨ s(a, c') = s(c', d) → False := by
      intro hx; exact hx.elim n1 n2
    have c3 : s(c', d) = s(a, b) ∨ s(c', d) = s(c', d) := Or.inr rfl
    have c4 : s(b, d) = s(a, b) ∨ s(b, d) = s(c', d) → False := by
      intro hx; exact hx.elim n3 n4
    rw [if_pos c1] at e1
    rw [if_pos c3] at e2
    rw [if_neg c2] at e3
    rw [if_neg c4] at e4
    exact ⟨e1, e2, e3, e4⟩
  · rintro ⟨h1, h2, h3, h4⟩ e he
    rw [mem_twoMatchings] at he
    rcases he with rfl | rfl | rfl | rfl
    · have hc : s(a, b) = s(a, b) ∨ s(a, b) = s(c', d) := Or.inl rfl
      rw [if_pos hc]; exact h1
    · have hc : s(a, c') = s(a, b) ∨ s(a, c') = s(c', d) → False := by
        intro hx; exact hx.elim n1 n2
      rw [if_neg hc]; exact h3
    · have hc : s(c', d) = s(a, b) ∨ s(c', d) = s(c', d) := Or.inr rfl
      rw [if_pos hc]; exact h2
    · have hc : s(b, d) = s(a, b) ∨ s(b, d) = s(c', d) → False := by
        intro hx; exact hx.elim n3 n4
      rw [if_neg hc]; exact h4

/-- The four residual colours of a `K₄` with two monochromatic matchings: the two colours `v, w` of
the matchings and the two colours of the remaining matching `{a,d}, {b,c'}`. -/
noncomputable def residual {n k : ℕ} (c : Col n k) (a b c' d : Verts n) (v w : Fin k) :
    Finset (Fin k) :=
  insert v (insert w (insert (c s(a, d)) (insert (c s(b, c')) ∅)))

/-- **A `K₄` WITH TWO OF ITS THREE MATCHINGS MONOCHROMATIC SPANS AT MOST FOUR COLOURS.** -/
theorem colorsOn_le_four_of_TwoMono {n k : ℕ} {a b c' d : Verts n}
    (h : FourDistinct a b c' d) {c : Col n k} {v w : Fin k} (hm : TwoMono c a b c' d v w) :
    (colorsOn c (fourSet a b c' d)).card ≤ 4 := by
  obtain ⟨h1, h2, h3, h4⟩ := (TwoMono_eq h c v w).mp hm
  have hsub : (colorsOn c (fourSet a b c' d)) ⊆ residual c a b c' d v w := by
    intro x hx
    simp only [colorsOn, Finset.mem_image] at hx
    obtain ⟨e, he, hec⟩ := hx
    rw [edgeFinset_fourSet h, mem_sixEdges] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp only [residual, Finset.mem_insert]
    · exact Or.inl (hec.symm.trans h1)
    · exact Or.inr (Or.inl (hec.symm.trans h3))
    · exact Or.inr (Or.inr (Or.inl hec.symm))
    · exact Or.inr (Or.inr (Or.inr (Or.inl hec.symm)))
    · exact Or.inr (Or.inl (hec.symm.trans h4))
    · exact Or.inl (hec.symm.trans h2)
  exact le_trans (Finset.card_le_card hsub) (card_insert4 _ _ _ _)

/-- **THE COLOURINGS WITH TWO MONOCHROMATIC MATCHINGS: `k^(E-4)` OF THEM.**  The four edges are
forced, all other edges are free. -/
theorem card_twoMono {n k : ℕ} {a b c' d : Verts n} (h : FourDistinct a b c' d) (v w : Fin k) :
    ((Finset.univ : Finset (Col n k)).filter fun c => TwoMono c a b c' d v w).card
      = k ^ (Fintype.card (Sym2 (Verts n)) - 4) := by
  have hE : ((Finset.univ : Finset (Col n k)).filter fun c => TwoMono c a b c' d v w)
      = (Finset.univ : Finset (Col n k)).filter fun c => ∀ e ∈ twoMatchings a b c' d,
        c e = (if e = s(a, b) ∨ e = s(c', d) then v else w) := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact Iff.rfl
  rw [hE, card_subtype_filter, card_preset (twoMatchings a b c' d)
      (fun e => if e = s(a, b) ∨ e = s(c', d) then v else w), card_twoMatchings h,
    Fintype.card_fin]

/-! ### §3  The first moment of the uniform distribution -/

/-- **THE COLOURINGS WHICH FAIL THE CATALOG CONDITION ON A FIXED VERTEX SET.** -/
noncomputable def badAt {n k : ℕ} (S : Finset (Verts n)) : Finset (Col n k) :=
  (Finset.univ : Finset (Col n k)).filter fun c => ¬ 5 ≤ (colorsOn c S).card

/-- **`K_n` HAS FOUR DISTINCT VERTICES AS SOON AS `4 ≤ n`.** -/
theorem exists_four_distinct {n : ℕ} (hn : 4 ≤ n) :
    ∃ a b c' d : Verts n, FourDistinct a b c' d := by
  obtain ⟨t, -, -, ht⟩ := Finset.exists_subsuperset_card_eq (s := ∅)
    (t := (Finset.univ : Finset (Verts n))) (n := 4) (Finset.empty_subset _) (by simp)
    (by simpa using hn)
  obtain ⟨a, b, c', d, h1, h2, h3, h4, h5, h6, -⟩ := Finset.card_eq_four.mp ht
  exact ⟨a, b, c', d, h1, h2, h3, h4, h5, h6⟩

/-- **A FOUR-SET IS SPANNED BY FOUR DISTINCT VERTICES.** -/
theorem fourSet_exists {n : ℕ} {S : Finset (Verts n)} (hS : S.card = 4) :
    ∃ a b c' d : Verts n, FourDistinct a b c' d ∧ S = fourSet a b c' d := by
  obtain ⟨a, b, c', d, h1, h2, h3, h4, h5, h6, hs⟩ := Finset.card_eq_four.mp hS
  refine ⟨a, b, c', d, ⟨h1, h2, h3, h4, h5, h6⟩, ?_⟩
  ext x
  rw [hs, fourSet]
  simp

/-- **THE FIRST-MOMENT LOWER BOUND ON ONE FOUR-SET: `k^(E-2)` COLOURINGS OF `K_n` FAIL THERE.**
The `k²` choices of the two colours `v, w` give disjoint families, each of size `k^(E-4)`. -/
theorem badAt_card_ge {n k : ℕ} {S : Finset (Verts n)} (hS : S.card = 4) :
    (badAt (k := k) S).card ≥ k ^ 2 * k ^ (Fintype.card (Sym2 (Verts n)) - 4) := by
  obtain ⟨a, b, c', d, hd, rfl⟩ := fourSet_exists hS
  have hP : ∀ p : Fin k × Fin k,
      ((Finset.univ : Finset (Col n k)).filter fun c => TwoMono c a b c' d p.1 p.2).card
        = k ^ (Fintype.card (Sym2 (Verts n)) - 4) := fun p => card_twoMono hd p.1 p.2
  have hsub : ∀ p : Fin k × Fin k,
      ((Finset.univ : Finset (Col n k)).filter fun c => TwoMono c a b c' d p.1 p.2)
        ⊆ badAt (fourSet a b c' d) := by
    intro p c hc
    rw [Finset.mem_filter] at hc
    rw [badAt, Finset.mem_filter]
    refine ⟨Finset.mem_univ c, ?_⟩
    have h1 := colorsOn_le_four_of_TwoMono hd hc.2
    omega
  have hdisj_pair : ∀ (p q : Fin k × Fin k), p ≠ q →
      Disjoint ((Finset.univ : Finset (Col n k)).filter fun c => TwoMono c a b c' d p.1 p.2)
        ((Finset.univ : Finset (Col n k)).filter fun c => TwoMono c a b c' d q.1 q.2) := by
    intro p q hpq
    refine Finset.disjoint_left.2 ?_
    intro c hc hqc
    rw [Finset.mem_filter] at hc hqc
    have h1 := (TwoMono_eq hd c p.1 p.2).mp hc.2
    have h2 := (TwoMono_eq hd c q.1 q.2).mp hqc.2
    exact hpq (Prod.ext (h1.1.symm.trans h2.1) (h1.2.2.1.symm.trans h2.2.2.1))
  have hdisj : (((Finset.univ ×ˢ Finset.univ : Finset (Fin k × Fin k)) :
      Set (Fin k × Fin k)).PairwiseDisjoint
      (fun p : Fin k × Fin k => ((Finset.univ : Finset (Col n k)).filter fun c =>
        TwoMono c a b c' d p.1 p.2))) :=
    fun p _ q _ hpq => hdisj_pair p q hpq
  have hle : ((Finset.univ ×ˢ Finset.univ : Finset (Fin k × Fin k)).biUnion
      (fun p : Fin k × Fin k => ((Finset.univ : Finset (Col n k)).filter fun c =>
        TwoMono c a b c' d p.1 p.2))).card ≤ (badAt (k := k) (fourSet a b c' d)).card := by
    refine Finset.card_le_card fun x hx => ?_
    rw [Finset.mem_biUnion] at hx
    obtain ⟨p, _, hxp⟩ := hx
    exact hsub p hxp
  have hsum : ∑ p ∈ (Finset.univ ×ˢ Finset.univ : Finset (Fin k × Fin k)),
      ((Finset.univ : Finset (Col n k)).filter fun c => TwoMono c a b c' d p.1 p.2).card
      = k ^ 2 * k ^ (Fintype.card (Sym2 (Verts n)) - 4) := by
    rw [Finset.sum_product,
      Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => hP (x, y),
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, Nat.nsmul_eq_mul,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, Nat.nsmul_eq_mul]
    ring
  rw [Finset.card_biUnion hdisj, hsum] at hle
  exact hle

/-- **THE DOUBLE COUNT: THE MEAN NUMBER OF FAILING FOUR-SETS OVER ALL `k`-COLOURINGS.** -/
theorem firstMoment_eq {n k : ℕ} :
    (∑ c : Col n k, (badFours c).card) = ∑ S ∈ fourSets n, (badAt (k := k) S).card := by
  have hstep : ∀ c : Col n k,
      (badFours c).card = ∑ S ∈ fourSets n, (if S ∈ badFours c then 1 else 0) := by
    intro c
    have hsub : badFours c ⊆ fourSets n := by
      intro S hS
      rw [fourSets, Finset.mem_filter]
      exact ⟨Finset.mem_univ S, (mem_badFours.mp hS).1⟩
    have key : (fourSets n).filter (fun S => S ∈ badFours c) = badFours c := by
      ext S
      simp only [Finset.mem_filter, fourSets, Finset.mem_filter, mem_badFours, Finset.mem_univ,
        true_and]
      tauto
    rw [Finset.sum_boole, key]
    simp
  have hkey : ∀ S : Finset (Verts n), S ∈ fourSets n →
      ((Finset.univ : Finset (Col n k)).filter fun c => S ∈ badFours c).card
        = (badAt (k := k) S).card := by
    intro S hS
    have hS4 : S.card = 4 := mem_fourSets.mp hS
    have key' : ((Finset.univ : Finset (Col n k)).filter fun c => S ∈ badFours c)
        = badAt (k := k) S := by
      ext c
      simp only [Finset.mem_filter, Finset.mem_univ, badAt, true_and]
      constructor
      · exact fun h => (mem_badFours.mp h).2
      · exact fun h => mem_badFours.mpr ⟨hS4, h⟩
    rw [key']
  calc (∑ c : Col n k, (badFours c).card)
      = ∑ c : Col n k, ∑ S ∈ fourSets n, (if S ∈ badFours c then 1 else 0) := by
        rw [Finset.sum_congr rfl fun c _ => hstep c]
    _ = ∑ S ∈ fourSets n, ∑ c : Col n k, (if S ∈ badFours c then 1 else 0) := by
        rw [Finset.sum_comm]
    _ = ∑ S ∈ fourSets n, (badAt S).card := by
        rw [Finset.sum_congr rfl fun S hS => ?_]
        rw [Finset.sum_boole, hkey S hS]
        simp

/-- **THE FIRST MOMENT OF THE UNIFORM DISTRIBUTION: THE MEAN IS AT LEAST `C(n,4)/k²`.**  More
precisely, with `E` the number of edges of `K_n`, the mean number of four-sets spanning at most
four colours is at least `C(n,4)·k^(E-2)` out of `k^E` colourings. -/
theorem firstMoment_ge {n k : ℕ} (hE : 6 ≤ Fintype.card (Sym2 (Verts n))) :
    Nat.choose n 4 * k ^ (Fintype.card (Sym2 (Verts n)) - 2)
      ≤ ∑ c : Col n k, (badFours c).card := by
  have h1 : (∑ S ∈ fourSets n, (badAt S).card)
      ≥ ∑ S ∈ fourSets n, k ^ 2 * k ^ (Fintype.card (Sym2 (Verts n)) - 4) :=
    Finset.sum_le_sum fun S hS => badAt_card_ge (mem_fourSets.mp hS)
  have h2 : (∑ S ∈ fourSets n, k ^ 2 * k ^ (Fintype.card (Sym2 (Verts n)) - 4))
      = Nat.choose n 4 * (k ^ 2 * k ^ (Fintype.card (Sym2 (Verts n)) - 4)) := by
        rw [Finset.sum_const, card_fourSets, Nat.nsmul_eq_mul]
  have h3 : k ^ 2 * k ^ (Fintype.card (Sym2 (Verts n)) - 4)
      = k ^ (Fintype.card (Sym2 (Verts n)) - 2) := by
        rw [← Nat.pow_add]
        congr 1
        omega
  calc Nat.choose n 4 * k ^ (Fintype.card (Sym2 (Verts n)) - 2)
      = Nat.choose n 4 * (k ^ 2 * k ^ (Fintype.card (Sym2 (Verts n)) - 4)) := by rw [h3]
    _ = ∑ S ∈ fourSets n, k ^ 2 * k ^ (Fintype.card (Sym2 (Verts n)) - 4) := by rw [h2]
    _ ≤ ∑ S ∈ fourSets n, (badAt S).card := h1
    _ = ∑ c : Col n k, (badFours c).card := by rw [firstMoment_eq]

/-- **THE FIRST MOMENT OF THE UNIFORM DISTRIBUTION, AT EVERY ORDER WITH FOUR VERTICES.** -/
theorem firstMoment_ge' {n k : ℕ} (hn : 4 ≤ n) :
    Nat.choose n 4 * k ^ (Fintype.card (Sym2 (Verts n)) - 2)
      ≤ ∑ c : Col n k, (badFours c).card := by
  obtain ⟨a, b, c', d, hd⟩ := exists_four_distinct hn
  exact firstMoment_ge (card_Sym2_ge_six a b c' d hd)

/-! ### §4  THE UNION-BOUND CRITERION -/

/-- **A COLOURING THAT IS NOT ADMISSIBLE HAS AT LEAST ONE FAILING FOUR-SET.** -/
theorem card_badFours_pos {n k : ℕ} {c : Col n k} (h : ¬ Admissible c) : 0 < (badFours c).card := by
  by_contra hcon
  have h0 : (badFours c).card = 0 := Nat.eq_zero_of_not_pos hcon
  rw [Finset.card_eq_zero] at h0
  exact h ((badFours_eq_empty_iff (c := c)).mp h0)

/-- **THE FIRST-MOMENT (UNION BOUND) CRITERION.**  If the weighted mean number of four-sets
spanning at most four colours is below `1`, then some colouring is admissible.  `w` is an integer
weight on colourings: `w c = 1` is the uniform distribution, and any (rational) distribution
corresponds to a weight by clearing denominators. -/
theorem unionBound {n k : ℕ} (w : Col n k → ℕ)
    (hw : (∑ c : Col n k, w c * (badFours c).card) < ∑ c : Col n k, w c) :
    ∃ c : Col n k, Admissible c := by
  by_contra hcon
  push_neg at hcon
  refine (Nat.not_lt.mpr (Finset.sum_le_sum fun c _ => ?_)) hw
  have h1' : 1 ≤ (badFours c).card := card_badFours_pos (hcon c)
  simpa using (Nat.mul_le_mul (Nat.le_refl _) h1' : w c * 1 ≤ w c * (badFours c).card)

/-- **THE CRITERION, ON THE WEIGHTS THAT GIVE THE PRIZE.**  A weight function meeting the union
bound at every order, with the palette already inside the catalogue window, certifies
`Main.AdmissibleUpper ε` — the sole remaining content of `jsp_000140_main`. -/
theorem AdmissibleUpper_of_firstMoment
    (h : ∀ (δ : ℝ) (m : ℕ), 0 < δ →
      ∃ (k : ℕ) (w : Col m k → ℕ),
        (∑ c : Col m k, w c * (badFours c).card) < ∑ c : Col m k, w c ∧
          (k : ℝ) ≤ 5 * (m : ℝ) / 6 + δ * m) : AdmissibleUpper 1 := by
  intro δ hδ
  refine ⟨0, fun m _ => ?_⟩
  obtain ⟨k, w, hw, hk⟩ := h δ m hδ
  obtain ⟨c, hc⟩ := unionBound w hw
  exact ⟨k, c, hc, hk⟩

/-- **THE TOTAL WEIGHT OF THE UNIFORM DISTRIBUTION IS THE NUMBER OF COLOURINGS.** -/
theorem sum_unif {n k : ℕ} : (∑ _c : Col n k, 1) = Fintype.card (Col n k) := by
  rw [Finset.sum_const, Finset.card_univ, Nat.nsmul_eq_mul]
  exact Nat.mul_one _

/-- **THE FIRST-MOMENT BARRIER.**  The uniform first moment cannot certify existence whenever
`k² ≤ C(n,4)`, i.e. for every palette size up to about `n²/√24`. -/
theorem uniform_firstMoment_fails {n k : ℕ} (hk : 2 ≤ k) (hC : k ^ 2 ≤ Nat.choose n 4) :
    (∑ c : Col n k, (badFours c).card) ≥ Fintype.card (Col n k) := by
  have hn : 4 ≤ n := by
    by_contra hcon
    have hz : Nat.choose n 4 = 0 := by
      interval_cases n <;> rfl
    rw [hz] at hC
    have hk0 : k = 0 := by
      have hpos : 0 < k ^ 2 := Nat.pow_pos (by omega)
      omega
    omega
  obtain ⟨a, b, c', d, hd⟩ := exists_four_distinct hn
  have hE := card_Sym2_ge_six a b c' d hd
  have h1 : (∑ c : Col n k, (badFours c).card)
      ≥ Nat.choose n 4 * k ^ (Fintype.card (Sym2 (Verts n)) - 2) := firstMoment_ge hE
  have h5 : k ^ 2 * k ^ (Fintype.card (Sym2 (Verts n)) - 2)
      ≤ Nat.choose n 4 * k ^ (Fintype.card (Sym2 (Verts n)) - 2) :=
    Nat.mul_le_mul_right (k ^ (Fintype.card (Sym2 (Verts n)) - 2)) hC
  have h2 : k ^ 2 * k ^ (Fintype.card (Sym2 (Verts n)) - 2)
      = k ^ Fintype.card (Sym2 (Verts n)) := by
    rw [Nat.mul_comm, ← Nat.pow_add, Nat.sub_add_cancel (by omega)]
  calc (∑ c : Col n k, (badFours c).card)
      ≥ Nat.choose n 4 * k ^ (Fintype.card (Sym2 (Verts n)) - 2) := h1
    _ ≥ k ^ 2 * k ^ (Fintype.card (Sym2 (Verts n)) - 2) := h5
    _ = k ^ Fintype.card (Sym2 (Verts n)) := h2
    _ = Fintype.card (Col n k) := by rw [card_col]

/-! ### §5  How large a palette the first moment would need -/

/-- **`C(n,4) = n(n-1)(n-2)(n-3)/24`.** -/
theorem choose_four_eq (n : ℕ) : Nat.choose n 4 * 24 = n * (n - 1) * (n - 2) * (n - 3) := by
  have h1 : Nat.choose n 1 * 1 = Nat.choose n 0 * (n - 0) := Nat.choose_succ_right_eq n 0
  have h2 : Nat.choose n 2 * 2 = Nat.choose n 1 * (n - 1) := Nat.choose_succ_right_eq n 1
  have h3 : Nat.choose n 3 * 3 = Nat.choose n 2 * (n - 2) := Nat.choose_succ_right_eq n 2
  have h4 : Nat.choose n 4 * 4 = Nat.choose n 3 * (n - 3) := Nat.choose_succ_right_eq n 3
  have e1 : Nat.choose n 1 = n := by simpa using h1
  have e2 : Nat.choose n 2 * 2 = n * (n - 1) := by simpa [e1] using h2
  have e3 : Nat.choose n 4 * 24 = Nat.choose n 3 * (n - 3) * 6 := by
    rw [show Nat.choose n 4 * 24 = Nat.choose n 4 * 4 * 6 by ring, h4]
  have e4 : Nat.choose n 3 * 6 = Nat.choose n 2 * (n - 2) * 2 := by
    rw [show Nat.choose n 3 * 6 = Nat.choose n 3 * 3 * 2 by ring, h3]
  calc Nat.choose n 4 * 24 = Nat.choose n 3 * (n - 3) * 6 := e3
    _ = Nat.choose n 2 * (n - 2) * 2 * (n - 3) := by
        rw [show Nat.choose n 3 * (n - 3) * 6 = (Nat.choose n 3 * 6) * (n - 3) by ring, e4]
    _ = (n * (n - 1)) * (n - 2) * (n - 3) := by
        rw [show Nat.choose n 2 * (n - 2) * 2 * (n - 3)
            = (Nat.choose n 2 * 2) * (n - 2) * (n - 3) by ring, e2]
/-- **`C(n,4) ≥ n²` for `n ≥ 8`.**  For `n ≥ 14` the analytic bound `(n-1)(n-2)(n-3) ≥ n³/8
≥ 24n` applies (`choose_four_eq` turns it into `n² ≤ C(n,4)`); the six orders `8 ≤ n < 14` are
finite instances. -/
theorem choose_four_ge_sq {n : ℕ} (hn : 8 ≤ n) : n ^ 2 ≤ Nat.choose n 4 := by
  by_cases h14 : 14 ≤ n
  · have h1 : 2 * (n - 1) ≥ n := by omega
    have h2 : 2 * (n - 2) ≥ n := by omega
    have h3 : 2 * (n - 3) ≥ n := by omega
    have key2 : n * n * n ≤ 8 * ((n - 1) * (n - 2) * (n - 3)) := by
      have key := Nat.mul_le_mul h2 (Nat.mul_le_mul h3 h1)
      calc n * n * n ≤ (2 * (n - 1)) * ((2 * (n - 2)) * (2 * (n - 3))) := by convert key using 1 <;> ring
        _ = 8 * ((n - 1) * (n - 2) * (n - 3)) := by ring
    have hA : 192 * n ≤ n * n * n := by
      have hq : 196 ≤ n * n := by
        have h14' := Nat.mul_le_mul h14 h14
        norm_num at h14' ⊢
        exact h14'
      have h5 := Nat.mul_le_mul_right n hq
      norm_num at h5
      omega
    have hC : 192 * n ≤ 8 * ((n - 1) * (n - 2) * (n - 3)) := by omega
    have hD : 24 * n ≤ (n - 1) * (n - 2) * (n - 3) := by
      have hC' : 8 * (24 * n) ≤ 8 * ((n - 1) * (n - 2) * (n - 3)) := by
        convert hC using 1 <;> ring
      exact Nat.le_of_mul_le_mul_left hC' (by norm_num : 0 < 8)
    have hF : 24 * (n * n) ≤ n * ((n - 1) * (n - 2) * (n - 3)) := by
      have := Nat.mul_le_mul_right n hD
      convert this using 1 <;> ring
    have hG : 24 * (n * n) ≤ 24 * Nat.choose n 4 := by
      rw [show 24 * Nat.choose n 4 = Nat.choose n 4 * 24 from Nat.mul_comm _ _, choose_four_eq]
      have := hF
      convert this using 1 <;> ring
    have hI := Nat.le_of_mul_le_mul_left hG (by norm_num : 0 < 24)
    rw [show n ^ 2 = n * n by ring]
    exact hI
  · interval_cases n <;> decide

/-- **`C(n,4) = Ω(n⁴)`: for `n ≥ 8`, `n⁴ ≤ 192·C(n,4)`. -/
theorem choose_four_ge {n : ℕ} (hn : 8 ≤ n) : n ^ 4 ≤ 192 * Nat.choose n 4 := by
  have h1 : 2 * (n - 1) ≥ n := by omega
  have h2 : 2 * (n - 2) ≥ n := by omega
  have h3 : 2 * (n - 3) ≥ n := by omega
  have key := Nat.mul_le_mul h2 (Nat.mul_le_mul h3 h1)
  have key2 : n ^ 3 ≤ 8 * ((n - 1) * (n - 2) * (n - 3)) := by
    calc n ^ 3 = n * (n * n) := by ring
      _ ≤ (2 * (n - 1)) * ((2 * (n - 2)) * (2 * (n - 3))) := by
          convert key using 1 <;> ring
      _ = 8 * ((n - 1) * (n - 2) * (n - 3)) := by ring
  calc n ^ 4 = n * n ^ 3 := by ring
    _ ≤ n * (8 * ((n - 1) * (n - 2) * (n - 3))) := Nat.mul_le_mul_left n key2
    _ = 8 * (n * (n - 1) * (n - 2) * (n - 3)) := by ring
    _ = 8 * (Nat.choose n 4 * 24) := by rw [choose_four_eq]
    _ = 192 * Nat.choose n 4 := by ring

/-- **THE UNION BOUND CERTIFIES NOTHING AT ANY PALETTE SIZE THE TRIVIAL COLOURING ACHIEVES.**  For
`n ≥ 8` and `2 ≤ k ≤ n+1` the uniform first moment is `≥ 1`, i.e. the mean number of failing
four-sets is at least one — while `Construction.EG_le_succ : EG n ≤ n + 1` (and
`Construction.EG_le_sumCol : EG n ≤ n` for odd `n`) is an explicit admissible colouring with at
most `n` colours.  **The uniform first-moment argument is never better than the trivial
construction.** -/
theorem no_certificate_below_trivial {n k : ℕ} (hn : 8 ≤ n) (hk : 2 ≤ k) (hk' : k ≤ n) :
    ¬ ((∑ c : Col n k, (badFours c).card) < Fintype.card (Col n k)) := by
  have h1 := choose_four_ge_sq hn
  have h2 : k ^ 2 ≤ n ^ 2 := by
    have : k * k ≤ n * n := Nat.mul_le_mul hk' hk'
    simpa only [Nat.pow_two] using this
  have h3 : k ^ 2 ≤ Nat.choose n 4 := by omega
  exact Nat.not_lt.mpr (uniform_firstMoment_fails hk h3)

/-- **THE UNION BOUND, AT ANY PALETTE, NEEDS `k > n`.** -/
theorem certificate_needs_more_than_n {n k : ℕ} (hn : 8 ≤ n) (hk : 2 ≤ k)
    (hc : (∑ c : Col n k, (badFours c).card) < Fintype.card (Col n k)) : n < k := by
  by_contra hcon
  have hk' : k ≤ n := Nat.le_of_not_gt hcon
  have h1a := choose_four_ge_sq hn
  have h2 : k ^ 2 ≤ n ^ 2 := by
    have : k * k ≤ n * n := Nat.mul_le_mul hk' hk'
    simpa only [Nat.pow_two] using this
  have h3 : k ^ 2 ≤ Nat.choose n 4 := by omega
  exact (Nat.not_lt.mpr (uniform_firstMoment_fails hk h3)) hc

/-- **THE PRICE OF THE FIRST MOMENT: A PALETTE OF ORDER `n²`.**  A palette certified by the uniform
first moment satisfies `n⁴ ≤ 192 k²`, i.e. `k ≥ n²/14` — a factor `Θ(n)` worse than the `n+1`
colours of `Construction.EG_le_succ`. -/
theorem firstMoment_needs_quadratic {n k : ℕ} (hn : 8 ≤ n) (hk : 2 ≤ k)
    (hc : (∑ c : Col n k, (badFours c).card) < Fintype.card (Col n k)) : n ^ 4 ≤ 192 * k ^ 2 := by
  have h7 : ¬ (k ^ 2 ≤ Nat.choose n 4) := by
    intro h
    exact (Nat.not_lt.mpr (uniform_firstMoment_fails hk h)) hc
  have h4 := choose_four_ge hn
  have h3 : Nat.choose n 4 < k ^ 2 := by omega
  have h5 : 192 * Nat.choose n 4 < 192 * k ^ 2 := by
    have := (Nat.mul_lt_mul_right (by norm_num : 0 < 192)).mpr h3
    convert this using 1 <;> ring
  exact le_trans h4 (Nat.le_of_lt h5)

/-- **THE FIRST MOMENT IS VACUOUS FOR EVERY PALETTE, LARGE OR SMALL, UP TO `√C(n,4)`.** -/
theorem firstMoment_vacuous_below {n k : ℕ} (hk : 2 ≤ k) (hC : k ^ 2 ≤ Nat.choose n 4) :
    (∑ c : Col n k, (badFours c).card) ≥ Fintype.card (Col n k) :=
  uniform_firstMoment_fails hk hC

/-- **THE PRICE OF CORRELATION: WHAT A CERTIFICATE MUST IMPROVE.**  The uniform distribution fails
a four-set with probability `1/k²` (`Barrier.firstMoment_ge`), so a distribution meeting the union
bound of `Barrier.unionBound` at order `n` must fail each four-set with probability
`< 1/C(n,4) ≤ 24/n⁴`: a gain of order `n²` over the uniform distribution.  This is the price of
the triangle-structure / nibble route of arXiv:2207.02920 §4, expressed as a `ℕ` inequality. -/
theorem gain_needed {n k : ℕ} (hn : 4 ≤ n) (hk : 2 ≤ k)
    (hw : (∑ c : Col n k, 1 * (badFours c).card) < ∑ c : Col n k, 1) :
    Nat.choose n 4 * (k ^ 2 * ∑ c : Col n k, 1) > ∑ c : Col n k, 1 * (badFours c).card := by
  have h1 : ∑ c : Col n k, 1 * (badFours c).card = ∑ c : Col n k, (badFours c).card := by
    refine Finset.sum_congr rfl fun c _ => ?_
    ring
  rw [h1] at hw ⊢
  have h5a : 1 ≤ k ^ 2 := by
    have h1k : 1 ≤ k := by omega
    have h1k' := Nat.mul_le_mul h1k h1k
    simpa only [Nat.pow_two] using h1k'
  have h5 : 1 * (∑ c : Col n k, 1) ≤ k ^ 2 * (∑ c : Col n k, 1) :=
    Nat.mul_le_mul h5a (Nat.le_refl _)
  have hC : 1 ≤ Nat.choose n 4 := by
    rw [← card_fourSets]
    obtain ⟨a, b, c', d, hd⟩ := exists_four_distinct hn
    exact Finset.card_pos.mpr ⟨fourSet a b c' d, mem_fourSets.mpr (card_fourSet hd)⟩
  have h6 : ∑ c : Col n k, 1 ≤ Nat.choose n 4 * (k ^ 2 * ∑ c : Col n k, 1) := by
    have h6' := Nat.mul_le_mul hC h5
    simpa using h6'
  omega

end