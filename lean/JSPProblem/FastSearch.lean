import JSPProblem.Search

/-!
# JSP-000140 — a *fast, symmetry-reduced* verified exhaustive search for `f(n, 4, 5)`

`Search.lean` (round 18) gave a **complete, machine-checked** exhaustive search for `f(n,4,5)`
together with its **completeness theorem** `Search.searchAux_iff`.  Two obstacles stopped it from
certifying anything beyond `n = 5`:

* `Search.fourSets n` enumerates the four-element subsets of `Fin n` by filtering the whole
  universe of `Finset (Verts n)`, i.e. `2^(n²)` candidates — `2^49` of them for `n = 7`;
* the search branched over *all* `k+1` colours at every slot, ignoring that the colours of a
  colouring are interchangeable.

This file removes **both** obstacles, keeping the "no axioms, no sorries" character of round 18.

* `Quad`, `incQuad`, `quadSet`, `quadEdges`, **`quadEdges_eq`**: a `K₄` is a quadruple of vertices
  in increasing order, its six edges are the `quadEdges` of that quadruple, and
  `quadEdges_eq : edgeFinset (quadSet q) = quadEdges q` is the correspondence between the
  combinatorial and the `Finset` description of a `K₄`;
* `quadColors` / **`quadColors_toFinset`**: the six colours a colouring gives to a `K₄`, as a
  *list* — the data the search tests, which is what makes the search fast;
* `collect6` / `quadOK` — the **pruning test** of the search;
* `PInv` — the invariant "the colours used so far are exactly `0, …, u-1`", which is what the
  symmetry reduction needs, and `PInv_update`, which says it is preserved;
* `searchAuxS` — the search, with the **colour-permutation symmetry reduction** built in: at each
  slot the new colour is only tried among `{0, …, u}`, the *first-occurrence* rule;
* **`searchAuxS_iff` — THE COMPLETENESS THEOREM OF THE SYMMETRY-REDUCED SEARCH**, proved by
  induction on the fuel and assuming nothing whatever about the search.  Its one genuinely new
  ingredient is `admissible_swapCol`: any admissible colouring may be relabelled by a
  transposition of two colours, so an extension that uses a "too large" colour at the current
  slot can be brought into the range the search explores;
* **`hasAdmissibleSym_iff` / `EG_ge_of_certSym`** — the lower-bound engine again: a
  `native_decide` certificate `hasAdmissibleSym n k = false` is a Lean proof that no admissible
  `k+1`-colouring of `K_n` exists, hence that `f(n,4,5) ≥ k+2`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option linter.unusedVariables false

namespace JSP140

variable {n k : ℕ}

/-- A partial colouring, indexed by slot. -/
abbrev PTab (k : ℕ) := ℕ → Option (Fin k)

private theorem update_eq_self {k : ℕ} {M : PTab k} {d : ℕ} {j : Fin k} :
    Function.update M d (some j) d = some j := by
  simp [Function.update]

private theorem update_of_ne {k : ℕ} {M : PTab k} {d s : ℕ} {j : Fin k} (hs : s ≠ d) :
    Function.update M d (some j) s = M s := by
  simp [Function.update, hs]


/-! ### The slot of an edge, computed from its endpoints -/

/-- **The slot of the edge `s(a,b)`, computed from its endpoints** — i.e. `Search.slotOf`
without the detour through `Sym2`. -/
def slotOfPair (n : ℕ) (a b : Verts n) : ℕ := (min a b).val * n + (max a b).val

@[simp] theorem slotOfPair_mk (a b : Verts n) : slotOfPair n a b = slotOf s(a, b) := rfl

theorem slotOfPair_swap (n : ℕ) (a b : Verts n) : slotOfPair n b a = slotOfPair n a b := by
  simp [slotOfPair, min_comm, max_comm]

/-! ### `K₄`s as increasing quadruples -/

/-- A `K₄`, given by its four vertices. -/
structure Quad (n : ℕ) where
  a : Verts n
  b : Verts n
  c : Verts n
  d : Verts n

/-- A quadruple is *increasing* if its vertices are in increasing order. -/
def incQuad {n : ℕ} (q : Quad n) : Prop := q.a < q.b ∧ q.b < q.c ∧ q.c < q.d

/-- The four-element vertex set of a quadruple. -/
def quadSet {n : ℕ} (q : Quad n) : Finset (Verts n) :=
  insert q.a (insert q.b (insert q.c {q.d}))

@[simp] theorem quadSet_fourSet {n : ℕ} (q : Quad n) : quadSet q = fourSet q.a q.b q.c q.d := rfl

/-- The six edges of a quadruple. -/
def quadEdges {n : ℕ} (q : Quad n) : Finset (Sym2 (Verts n)) :=
  {s(q.a, q.b), s(q.a, q.c), s(q.a, q.d), s(q.b, q.c), s(q.b, q.d), s(q.c, q.d)}

/-- The six slots of a quadruple. -/
def quadSlots (n : ℕ) (q : Quad n) : List ℕ :=
  [slotOfPair n q.a q.b, slotOfPair n q.a q.c, slotOfPair n q.a q.d,
    slotOfPair n q.b q.c, slotOfPair n q.b q.d, slotOfPair n q.c q.d]

/-- **The slot at which a `K₄` is completed**: the largest of its six slots. -/
def slotQuad (n : ℕ) (q : Quad n) : ℕ :=
  max (slotOfPair n q.a q.b)
    (max (slotOfPair n q.a q.c)
      (max (slotOfPair n q.a q.d)
        (max (slotOfPair n q.b q.c) (max (slotOfPair n q.b q.d) (slotOfPair n q.c q.d)))))

private theorem le_qslot1 (A B C D E F : ℕ) : A ≤ max A (max B (max C (max D (max E F)))) :=
  le_max_left _ _
private theorem le_qslot2 (A B C D E F : ℕ) : B ≤ max A (max B (max C (max D (max E F)))) :=
  (le_max_left _ _).trans (le_max_right _ _)
private theorem le_qslot3 (A B C D E F : ℕ) : C ≤ max A (max B (max C (max D (max E F)))) :=
  (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
private theorem le_qslot4 (A B C D E F : ℕ) : D ≤ max A (max B (max C (max D (max E F)))) :=
  (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
private theorem le_qslot5 (A B C D E F : ℕ) : E ≤ max A (max B (max C (max D (max E F)))) :=
  (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans
    ((le_max_right _ _).trans (le_max_right _ _))))
private theorem le_qslot6 (A B C D E F : ℕ) : F ≤ max A (max B (max C (max D (max E F)))) :=
  (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans
    ((le_max_right _ _).trans (le_max_right _ _))))

/-- **Every one of the six slots of a `K₄` is at most the slot at which it is completed.** -/
theorem le_slotQuad {n : ℕ} (q : Quad n) (s : ℕ) (h : s ∈ quadSlots n q) : s ≤ slotQuad n q := by
  rw [slotQuad]
  simp only [quadSlots, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h
  · rw [h]; exact le_qslot1 _ _ _ _ _ _
  · rw [h]; exact le_qslot2 _ _ _ _ _ _
  · rw [h]; exact le_qslot3 _ _ _ _ _ _
  · rw [h]; exact le_qslot4 _ _ _ _ _ _
  · rw [h]; exact le_qslot5 _ _ _ _ _ _
  · rw [h]; exact le_qslot6 _ _ _ _ _ _

/-- An increasing quadruple carries four distinct vertices. -/
theorem fourDistinct_of_incQuad {n : ℕ} {q : Quad n} (h : incQuad q) :
    FourDistinct q.a q.b q.c q.d :=
  ⟨ne_of_lt h.1, ne_of_lt (lt_of_lt_of_le h.1 h.2.1.le),
    ne_of_lt (lt_of_lt_of_le h.1 (lt_of_lt_of_le h.2.1 h.2.2.le).le),
    ne_of_lt h.2.1, ne_of_lt (lt_of_lt_of_le h.2.1 h.2.2.le), ne_of_lt h.2.2⟩

theorem card_quadSet {n : ℕ} {q : Quad n} (h : incQuad q) : (quadSet q).card = 4 :=
  card_fourSet (fourDistinct_of_incQuad h)

theorem mem_quadSet {n : ℕ} {q : Quad n} (h : incQuad q) {x : Verts n} :
    x ∈ quadSet q ↔ x = q.a ∨ x = q.b ∨ x = q.c ∨ x = q.d :=
  mem_fourSet (fourDistinct_of_incQuad h)

/-- Unordered pairs are commutative. -/
theorem sym2_swap {α : Type*} (a b : α) : s(a, b) = s(b, a) :=
  Sym2.ext fun x => by simp [or_comm]

/-- **Every edge of the `K` on four vertices is one of the six edges of the quadruple** (for
`a < b`). -/
theorem mem_quadEdges_of_lt {n : ℕ} {q : Quad n} (h : incQuad q) {a b : Verts n} (hab : a < b)
    (ha : a = q.a ∨ a = q.b ∨ a = q.c ∨ a = q.d)
    (hb : b = q.a ∨ b = q.b ∨ b = q.c ∨ b = q.d) : s(a, b) ∈ quadEdges q := by
  have hv1 : q.a.val < q.b.val := h.1
  have hv2 : q.b.val < q.c.val := h.2.1
  have hv3 : q.c.val < q.d.val := h.2.2
  have hval : a.val < b.val := hab
  rcases ha with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl
  all_goals simp only [quadEdges, Finset.mem_insert, Finset.mem_singleton]
  all_goals aesop (add safe sym2_swap)
  all_goals omega

/-- **Every edge of the `K` on four vertices is one of the six edges of the quadruple** (for two
of its vertices). -/
theorem mem_quadEdges_of_mem {n : ℕ} {q : Quad n} (h : incQuad q) {a b : Verts n}
    (ha : a = q.a ∨ a = q.b ∨ a = q.c ∨ a = q.d)
    (hb : b = q.a ∨ b = q.b ∨ b = q.c ∨ b = q.d) (hab : a ≠ b) : s(a, b) ∈ quadEdges q := by
  rcases lt_trichotomy a b with hlt | hlt | hlt
  · exact mem_quadEdges_of_lt h hlt ha hb
  · exact (hab hlt).elim
  · rw [sym2_swap]
    exact mem_quadEdges_of_lt h hlt hb ha

/-- **Every edge of the `K` on four vertices is one of the six edges of the quadruple.** -/
theorem mem_quadEdges {n : ℕ} {q : Quad n} {e : Sym2 (Verts n)} (h : incQuad q)
    (hall : ∀ x : Verts n, x ∈ e → x ∈ quadSet q) (hof : OffDiag e) : e ∈ quadEdges q := by
  obtain ⟨a, b, rfl⟩ := Sym2.exists.mp ⟨e, rfl⟩
  have h4 : ∀ x : Verts n, x ∈ quadSet q → x = q.a ∨ x = q.b ∨ x = q.c ∨ x = q.d := by
    intro x hx
    rw [mem_quadSet h] at hx
    exact hx
  have ha := h4 a (hall a (Sym2.mem_mk_left a b))
  have hb := h4 b (hall b (Sym2.mem_mk_right a b))
  rcases lt_trichotomy a b with hab | hab | hab
  · exact mem_quadEdges_of_lt h hab ha hb
  · exact ((hof a b rfl) hab).elim
  · rw [sym2_swap]
    exact mem_quadEdges_of_lt h hab hb ha

/-- **THE CORRESPONDENCE: the six edges of an increasing quadruple are exactly the edges of the
complete graph on its four vertices.** -/
theorem quadEdges_eq {n : ℕ} {q : Quad n} (h : incQuad q) :
    edgeFinset (quadSet q) = quadEdges q := by
  have hFD := fourDistinct_of_incQuad h
  refine Finset.Subset.antisymm (fun e he => ?_) (fun e he => ?_)
  · exact mem_quadEdges h
      (fun x hx => (Finset.mem_sym2_iff.mp (mem_edgeFinset.mp he).1) x hx)
      (mem_edgeFinset.mp he).2
  · simp only [quadEdges, Finset.mem_insert, Finset.mem_singleton, or_false, or_assoc, and_false,
      not_or, List.not_mem_nil] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals apply mem_edgeFinset_mk
    all_goals first
      | (rw [mem_quadSet h]; exact Or.inl rfl)
      | (rw [mem_quadSet h]; exact Or.inr (Or.inl rfl))
      | (rw [mem_quadSet h]; exact Or.inr (Or.inr (Or.inl rfl)))
      | (rw [mem_quadSet h]; exact Or.inr (Or.inr (Or.inr rfl)))
      | exact hFD.1
      | exact hFD.2.1
      | exact hFD.2.2.1
      | exact hFD.2.2.2.1
      | exact hFD.2.2.2.2.1
      | exact hFD.2.2.2.2.2

/-- **THE COLOURS OF A `K₄`**: the list of the six colours a colouring gives to the six edges of
a quadruple.  This is the data the search tests. -/
def quadColors {n k : ℕ} (c : Col n k) (q : Quad n) : List (Fin k) :=
  [c s(q.a, q.b), c s(q.a, q.c), c s(q.a, q.d), c s(q.b, q.c), c s(q.b, q.d), c s(q.c, q.d)]

/-- **The six colours of a `K₄` are exactly the colours of its four vertices.** -/
theorem quadColors_toFinset {n k : ℕ} (c : Col n k) (q : Quad n) (h : incQuad q) :
    (quadColors c q).toFinset = colorsOn c (quadSet q) := by
  ext i
  constructor
  · intro hi
    have hi' : i ∈ quadColors c q := List.mem_toFinset.mp hi
    simp only [quadColors, List.mem_cons, List.not_mem_nil, or_false] at hi'
    simp only [colorsOn, Finset.mem_image, quadEdges_eq h]
    have hFD := fourDistinct_of_incQuad h
    rcases hi' with h' | h' | h' | h' | h' | h'
    · refine ⟨s(q.a, q.b), ?_, h'.symm⟩
      exact mem_quadEdges_of_mem h (Or.inl rfl) (Or.inr (Or.inl rfl)) hFD.1
    · refine ⟨s(q.a, q.c), ?_, h'.symm⟩
      exact mem_quadEdges_of_mem h (Or.inl rfl) (Or.inr (Or.inr (Or.inl rfl))) hFD.2.1
    · refine ⟨s(q.a, q.d), ?_, h'.symm⟩
      exact mem_quadEdges_of_mem h (Or.inl rfl) (Or.inr (Or.inr (Or.inr rfl))) hFD.2.2.1
    · refine ⟨s(q.b, q.c), ?_, h'.symm⟩
      exact mem_quadEdges_of_mem h (Or.inr (Or.inl rfl)) (Or.inr (Or.inr (Or.inl rfl))) hFD.2.2.2.1
    · refine ⟨s(q.b, q.d), ?_, h'.symm⟩
      exact mem_quadEdges_of_mem h (Or.inr (Or.inl rfl)) (Or.inr (Or.inr (Or.inr rfl))) hFD.2.2.2.2.1
    · refine ⟨s(q.c, q.d), ?_, h'.symm⟩
      exact mem_quadEdges_of_mem h (Or.inr (Or.inr (Or.inl rfl)))
        (Or.inr (Or.inr (Or.inr rfl))) hFD.2.2.2.2.2
  · intro hi
    apply List.mem_toFinset.mpr
    simp only [colorsOn, Finset.mem_image, quadEdges_eq h] at hi
    obtain ⟨e, he, hec⟩ := hi
    simp only [quadEdges, Finset.mem_insert, Finset.mem_singleton, or_false, or_assoc, and_false,
      not_or, List.not_mem_nil] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;> rw [← hec] <;>
      simp only [quadColors, List.mem_cons, List.not_mem_nil, or_false] <;> aesop

/-- **A `K₄` of an admissible colouring spans at least five colours** — the catalog condition,
in the form the search uses. -/
theorem quad_ok_of_admissible {n k : ℕ} {c : Col n k} {q : Quad n} (h : incQuad q)
    (hc : Admissible c) : decide (5 ≤ ((quadColors c q).toFinset).card) = true := by
  have h1 : 5 ≤ ((quadColors c q).toFinset).card := by
    rw [quadColors_toFinset c q h]
    exact hc _ (card_quadSet h)
  rw [decide_eq_true_eq]; exact h1

/-! ### Relabelling the palette -/

/-- The transposition of two colours of the palette. -/
def swp {k : ℕ} (j j' : Fin k) (hne : j ≠ j') (c : Fin k) : Fin k :=
  if c = j then j' else if c = j' then j else c

theorem swp_of_ne {k : ℕ} {j j' : Fin k} (hne : j ≠ j') (c : Fin k) (h1 : c ≠ j) (h2 : c ≠ j') :
    swp j j' hne c = c := by
  simp [swp, h1, h2]

theorem swp_of_eq {k : ℕ} {j j' : Fin k} (hne : j ≠ j') (c : Fin k) (h : c = j') :
    swp j j' hne c = j := by
  have hne' : c ≠ j := by rw [h]; exact Ne.symm hne
  simp [swp, hne', h]

theorem swp_of_eq' {k : ℕ} {j j' : Fin k} (hne : j ≠ j') (c : Fin k) (h : c = j) :
    swp j j' hne c = j' := by
  have hne' : c ≠ j' := by rw [h]; exact hne
  simp [swp, hne', h]

/-- **The transposition is an involution.** -/
theorem swp_involutive {k : ℕ} (j j' : Fin k) (hne : j ≠ j') (c : Fin k) :
    swp j j' hne (swp j j' hne c) = c := by
  by_cases h1 : c = j
  · rw [swp_of_eq' hne c h1, swp_of_eq hne j' rfl, h1]
  · by_cases h2 : c = j'
    · rw [swp_of_eq hne c h2, swp_of_eq' hne j rfl, h2]
    · rw [swp_of_ne hne c h1 h2, swp_of_ne hne c h1 h2]

/-- **Swapping two colours of the palette.** -/
def swapCol {n k : ℕ} (c : Col n k) (j j' : Fin k) (hne : j ≠ j') : Col n k :=
  fun e => swp j j' hne (c e)

@[simp] theorem swapCol_apply (c : Col n k) (j j' : Fin k) (hne : j ≠ j') (e : Sym2 (Verts n)) :
    swapCol c j j' hne e = swp j j' hne (c e) := rfl

theorem swapCol_apply_swapCol {n k : ℕ} (c : Col n k) (j j' : Fin k) (hne : j ≠ j')
    (e : Sym2 (Verts n)) : swapCol (swapCol c j j' hne) j j' hne e = c e :=
  swp_involutive j j' hne (c e)

theorem swapCol_of_ne {n k : ℕ} {c : Col n k} {j j' : Fin k} {hne : j ≠ j'}
    {e : Sym2 (Verts n)} (h1 : c e ≠ j) (h2 : c e ≠ j') : swapCol c j j' hne e = c e :=
  swp_of_ne hne _ h1 h2

theorem swapCol_apply_of_small {n k : ℕ} {c : Col n k} {j j' : Fin k} {hne : j ≠ j'}
    (e : Sym2 (Verts n)) (h : (c e).val < min j.val j'.val) : swapCol c j j' hne e = c e := by
  by_cases h1 : c e = j
  · exfalso
    rw [h1] at h
    exact absurd h (by simp)
  · by_cases h2 : c e = j'
    · exfalso
      rw [h2] at h
      exact absurd h (by simp)
    · exact swapCol_of_ne h1 h2

/-- **Relabelling the palette does not change the number of colours of a `K₄`.** -/
theorem card_colorsOn_swapCol {n k : ℕ} (c : Col n k) (j j' : Fin k) (hne : j ≠ j')
    (S : Finset (Verts n)) : (colorsOn (swapCol c j j' hne) S).card = (colorsOn c S).card := by
  have h1 : (colorsOn c S).image (fun x => swp j j' hne x) = colorsOn (swapCol c j j' hne) S := by
    ext x
    simp only [colorsOn, Finset.mem_image, swapCol_apply]
    constructor
    · rintro ⟨y, hy, hxy⟩
      obtain ⟨e, he, heq⟩ := hy
      exact ⟨e, he, (congrArg (fun t => swp j j' hne t) heq).trans hxy⟩
    · rintro ⟨e, he, hex⟩
      exact ⟨c e, ⟨e, he, rfl⟩, hex⟩
  have h2 : ((colorsOn c S).image (fun x => swp j j' hne x)).card = (colorsOn c S).card :=
    Finset.card_image_of_injective (colorsOn c S) (fun a b hab =>
      by
        have h3 := congrArg (fun t => swp j j' hne t) hab
        rw [swp_involutive j j' hne a, swp_involutive j j' hne b] at h3
        exact h3)
  rw [← h1, h2]

/-- **RELABELLING THE PALETTE PRESERVES ADMISSIBILITY.** -/
theorem admissible_swapCol {n k : ℕ} {c : Col n k} (j j' : Fin k) (hne : j ≠ j') (hc : Admissible c) :
    Admissible (swapCol c j j' hne) := by
  intro S hS
  rw [card_colorsOn_swapCol]
  exact hc S hS

/-! ### The pruning test -/

/-- **The colours of the edges in the given slots**, or `none` as soon as one of the slots is
still unfilled. -/
def collect6 {k : ℕ} (M : PTab k) : List ℕ → Option (List (Fin k))
  | [] => some []
  | s :: ss => match M s with
      | none => none
      | some c => (collect6 M ss).map (fun l => c :: l)

/-- **THE PRUNING TEST.**  A `K₄` which is not complete yet imposes no constraint; a complete
`K₄` must span at least five colours. -/
def quadOK {n k : ℕ} (M : PTab k) (q : Quad n) : Bool :=
  match collect6 M (quadSlots n q) with
  | none => true
  | some l => decide (5 ≤ (l.toFinset : Finset (Fin k)).card)

/-- All the `K₄`s of a group are admissible. -/
def allOK {n k : ℕ} (M : PTab k) : List (Quad n) → Bool
  | [] => true
  | q :: qs => quadOK M q && allOK M qs

theorem allOK_of {n k : ℕ} {M : PTab k} {l : List (Quad n)}
    (h : ∀ q, q ∈ l → quadOK M q = true) : allOK M l = true := by
  induction l with
  | nil => rfl
  | cons q qs ih =>
      have h1 : quadOK M q = true := h q List.mem_cons_self
      have h2 : allOK M qs = true := ih (fun r hr => h r (List.mem_cons_of_mem _ hr))
      simp only [allOK, h1, h2, Bool.true_and]

/-- **THE COLOURS OF A `K₄`, read off a partial colouring.**  If a partial colouring agrees with
a total colouring `c` on all slots `≤ d`, and the `K₄` `q` is completed at `d`, then `q` passes the
pruning test. -/
theorem quadOK_of {n k : ℕ} {M : PTab k} {q : Quad n} {c : Col n k} {d : ℕ}
    (h : incQuad q) (hd : slotQuad n q = d)
    (hall : ∀ e, OffDiag e → slotOf e ≤ d → M (slotOf e) = some (c e))
    (hc : Admissible c) : quadOK M q = true := by
  have e1 : slotOf s(q.a, q.b) ≤ d := by
    rw [← slotOfPair_mk, ← hd]; exact le_qslot1 _ _ _ _ _ _
  have e2 : slotOf s(q.a, q.c) ≤ d := by
    rw [← slotOfPair_mk, ← hd]; exact le_qslot2 _ _ _ _ _ _
  have e3 : slotOf s(q.a, q.d) ≤ d := by
    rw [← slotOfPair_mk, ← hd]; exact le_qslot3 _ _ _ _ _ _
  have e4 : slotOf s(q.b, q.c) ≤ d := by
    rw [← slotOfPair_mk, ← hd]; exact le_qslot4 _ _ _ _ _ _
  have e5 : slotOf s(q.b, q.d) ≤ d := by
    rw [← slotOfPair_mk, ← hd]; exact le_qslot5 _ _ _ _ _ _
  have e6 : slotOf s(q.c, q.d) ≤ d := by
    rw [← slotOfPair_mk, ← hd]; exact le_qslot6 _ _ _ _ _ _
  simp only [quadSlots, collect6, quadOK, slotOfPair_mk]
  have hFD := fourDistinct_of_incQuad h
  have g1 : M (slotOf s(q.a, q.b)) = some (c s(q.a, q.b)) :=
    hall _ (offDiag_iff.mpr hFD.1) e1
  have g2 : M (slotOf s(q.a, q.c)) = some (c s(q.a, q.c)) :=
    hall _ (offDiag_iff.mpr hFD.2.1) e2
  have g3 : M (slotOf s(q.a, q.d)) = some (c s(q.a, q.d)) :=
    hall _ (offDiag_iff.mpr hFD.2.2.1) e3
  have g4 : M (slotOf s(q.b, q.c)) = some (c s(q.b, q.c)) :=
    hall _ (offDiag_iff.mpr hFD.2.2.2.1) e4
  have g5 : M (slotOf s(q.b, q.d)) = some (c s(q.b, q.d)) :=
    hall _ (offDiag_iff.mpr hFD.2.2.2.2.1) e5
  have g6 : M (slotOf s(q.c, q.d)) = some (c s(q.c, q.d)) :=
    hall _ (offDiag_iff.mpr hFD.2.2.2.2.2) e6
  rw [g1, g2, g3, g4, g5, g6]
  exact quad_ok_of_admissible h hc

/-! ### The group of a slot -/

/-- The boolean version of `incQuad` (the search has to compute it). -/
def incQuadB {n : ℕ} (q : Quad n) : Bool :=
  decide (q.a.val < q.b.val) && decide (q.b.val < q.c.val) && decide (q.c.val < q.d.val)

theorem incQuadB_iff {n : ℕ} {q : Quad n} : incQuadB q = true ↔ incQuad q := by
  simp only [incQuadB, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · intro h
    show q.a < q.b ∧ q.b < q.c ∧ q.c < q.d
    exact ⟨h.1.1, h.1.2, h.2⟩
  · intro h
    show (↑q.a < ↑q.b ∧ ↑q.b < ↑q.c) ∧ ↑q.c < ↑q.d
    exact ⟨⟨h.1, h.2.1⟩, h.2.2⟩


/-- **The four-cliques of `K_n`, as increasing quadruples.** -/
def quadsOf (n : ℕ) : List (Quad n) :=
  ((List.finRange n).flatMap fun a => (List.finRange n).flatMap fun b =>
    (List.finRange n).flatMap fun c => (List.finRange n).map fun d =>
      { a := a, b := b, c := c, d := d }).filter (incQuadB)

/-- **THE GROUP OF THE SLOT `d`**: the `K₄`s *completed* by the slot `d`, i.e. those whose six
edges all lie in the slots `≤ d` and one of them lies in the slot `d`.  (Contrast `Search.group`,
which enumerates the whole universe of four-element vertex sets — `2^(n²)` of them.) -/
def groupsOf (n : ℕ) (d : ℕ) : List (Quad n) := (quadsOf n).filter (fun q => slotQuad n q = d)

theorem mem_groupsOf {n d : ℕ} {q : Quad n} (h : q ∈ groupsOf n d) :
    incQuad q ∧ slotQuad n q = d := by
  simp only [groupsOf, quadsOf, List.mem_filter] at h
  exact ⟨incQuadB_iff.mp h.left.2, decide_eq_true_eq.mp h.right⟩

/-! ### The colour-permutation symmetry reduction -/

/-- **THE ALLOWED COLOURS AT A SLOT**: the colours already used, and the next new one.  This is
the *first-occurrence* rule, and it is the whole symmetry reduction. -/
def allowedColors (k u : ℕ) : List (Fin k) :=
  (List.finRange (Nat.min (u + 1) k)).map
    (fun i : Fin (Nat.min (u + 1) k) => ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.min_le_right _ _)⟩)

theorem mem_allowedColors {k u : ℕ} {j : Fin k} (h : j.val ≤ u) : j ∈ allowedColors k u := by
  simp only [allowedColors, List.mem_map]
  exact ⟨⟨j.val, Nat.lt_min.mpr ⟨Nat.lt_succ_of_le h, j.isLt⟩⟩, List.mem_finRange _, Fin.ext rfl⟩

theorem allowedColors_val_le {k u : ℕ} {j : Fin k} (h : j ∈ allowedColors k u) : j.val ≤ u := by
  simp only [allowedColors, List.mem_map] at h
  obtain ⟨i, hi, heq⟩ := h
  have h1 : i.val < u + 1 := lt_of_lt_of_le i.isLt (Nat.min_le_left _ _)
  have hv : i.val = j.val := Fin.ext_iff.mp heq
  rw [hv] at h1
  exact Nat.lt_succ_iff.mp h1

/-- **THE COLOUR INVARIANT**: the colours used by a partial colouring are exactly
`0, …, u-1`. -/
def PInv {k : ℕ} (M : PTab k) (u : ℕ) : Prop :=
  u ≤ k ∧ (∀ (i : ℕ) (hi : i < u) (hk : i < k), ∃ s : ℕ, M s = some ⟨i, hk⟩) ∧
    ∀ (j : Fin k), (∃ s : ℕ, M s = some j) → j.val < u

/-- **THE PREFIX INVARIANT**: the meaningful slots filled by a partial colouring are exactly
`0, …, d-1`, and no slot beyond `d` is filled. -/
def PFilled (n : ℕ) {k : ℕ} (M : PTab k) (d : ℕ) : Prop :=
  (∀ s, s < d → meaningfulSlot n s = true → ∃ j : Fin k, M s = some j) ∧
    (∀ s, d ≤ s → M s = none)

/-- The two invariants of the search. -/
def PSpec (n : ℕ) {k : ℕ} (M : PTab k) (u d : ℕ) : Prop := PInv M u ∧ PFilled n M d

theorem PSpec_none {n k : ℕ} : PSpec n (M := (fun _ => none : PTab k)) 0 0 := by
  refine ⟨⟨Nat.zero_le _, ?_, ?_⟩, ⟨?_, ?_⟩⟩
  · intro i hi; omega
  · intro j hj
    obtain ⟨s, hs⟩ := hj
    have hnone : (fun _ => none : PTab k) s = none := rfl
    exact absurd (hnone.symm.trans hs) (by simp)
  · intro s hs hm
    exact (Nat.not_lt_zero s hs).elim
  · intro s hs; rfl

/-- The colour invariant is preserved by filling a slot with an allowed colour. -/
theorem PInv_update {k : ℕ} {M : PTab k} {u d : ℕ} (hinv : PInv M u) (hne : M d = none)
    {j : Fin k} (hj : j.val ≤ u) :
    PInv (Function.update M d (some j)) (if j.val < u then u else u + 1) := by
  obtain ⟨huk, h1, h2⟩ := hinv
  by_cases hlt : j.val < u
  · simp only [if_pos hlt]
    refine ⟨?_, ?_, ?_⟩
    · omega
    · intro i hi hk
      obtain ⟨s, hs⟩ := h1 i hi hk
      refine ⟨s, ?_⟩
      by_cases hs0 : s = d
      · exact absurd (hne.symm.trans (hs0 ▸ hs)) (by simp)
      · have h3 : Function.update M d (some j) s = M s := update_of_ne hs0
        rw [h3]
        exact hs
    · intro j' hj'
      obtain ⟨s, hs⟩ := hj'
      by_cases hs0 : s = d
      · have hjeq : j = j' := Option.some.inj (by simpa [hs0] using hs)
        exact hjeq ▸ hlt
      · exact h2 j' ⟨s, by simpa [Function.update, hs0] using hs⟩
  · simp only [if_neg hlt]
    refine ⟨?_, ?_, ?_⟩
    · omega
    · intro i hi hk
      by_cases hieq : i = u
      · refine ⟨d, ?_⟩
        rw [update_eq_self]
        have hj' : j = ⟨i, hk⟩ := by
          apply Fin.ext
          simp only [Fin.val_mk]
          omega
        exact congrArg some hj'
      · obtain ⟨s, hs⟩ := h1 i (by omega) hk
        refine ⟨s, ?_⟩
        by_cases hs0 : s = d
        · exact absurd (hne.symm.trans (hs0 ▸ hs)) (by simp)
        · have h3 : Function.update M d (some j) s = M s := update_of_ne hs0
          rw [h3]
          exact hs
    · intro j' hj'
      obtain ⟨s, hs⟩ := hj'
      by_cases hs0 : s = d
      · have hjeq : j = j' := Option.some.inj (by simpa [hs0] using hs)
        exact hjeq ▸ (by omega : j.val < u + 1)
      · have hval := h2 j' ⟨s, by simpa [Function.update, hs0] using hs⟩
        omega

/-- The prefix invariant is preserved by filling a slot. -/
theorem PFilled_update (n : ℕ) {k : ℕ} {M : PTab k} {d : ℕ} (hfill : PFilled n M d) {j : Fin k} :
    PFilled n (Function.update M d (some j)) (d + 1) := by
  obtain ⟨h1, h2⟩ := hfill
  constructor
  · intro s hs hm
    by_cases hs0 : s = d
    · exact ⟨j, by simp [hs0]⟩
    · have h3 : Function.update M d (some j) s = M s := update_of_ne hs0
      rw [h3]
      exact h1 s (by omega) hm
  · intro s hs
    have h3 : Function.update M d (some j) s = M s := update_of_ne (by omega)
    rw [h3]
    exact h2 s (by omega)

/-- The prefix invariant survives the skip of a slot which carries no edge. -/
theorem PFilled_skip (n : ℕ) {k : ℕ} {M : PTab k} {d : ℕ} (hfill : PFilled n M d)
    (hm : meaningfulSlot n d = false) : PFilled n M (d + 1) := by
  obtain ⟨h1, h2⟩ := hfill
  constructor
  · intro s hs hms
    have hs0 : s < d := by
      by_contra hc
      have hds : d ≤ s := by omega
      have hsd : s = d := by omega
      subst hsd
      rw [hm] at hms
      exact Bool.noConfusion hms
    exact h1 s hs0 hms
  · intro s hs
    exact h2 s (by omega)

theorem PSpec_update {n k : ℕ} {M : PTab k} {u d : ℕ} (hspec : PSpec n M u d) {j : Fin k}
    (hj : j.val ≤ u) : PSpec n (Function.update M d (some j))
      (if j.val < u then u else u + 1) (d + 1) :=
  ⟨PInv_update hspec.1 (hspec.2.2 d (Nat.le_refl d)) hj, PFilled_update n hspec.2⟩

/-! ### The search -/

/-- **The total colouring read off a partial colouring**: the unassigned slots get the colour
`dflt`. -/
def tabOf (n : ℕ) {k : ℕ} (dflt : Fin k) (M : PTab k) : Col n k :=
  fun e => (M (slotOf e)).getD dflt

/-- **THE SYMMETRY-REDUCED SEARCH.**  `searchAuxS dflt M u d fuel` colours the edges in the slots
`d, d+1, …` (`fuel` at a time), branching only over `allowedColors k u` — the colours already
used and the next new one — and **pruning a branch as soon as one of the `K₄`s completed by the
slot being filled fails the catalog condition**.  At the end it tests `Admissible` outright. -/
def searchAuxS (n : ℕ) {k : ℕ} (dflt : Fin k) (M : PTab k) (u : ℕ) (d fuel : ℕ) : Bool :=
  match fuel with
  | 0 => decide (Admissible (tabOf n dflt M))
  | fuel' + 1 =>
      if h : n * n ≤ d then decide (Admissible (tabOf n dflt M))
      else if meaningfulSlot n d then
        (allowedColors k u).any fun j =>
          let M' := Function.update M d (some j)
          allOK M' (groupsOf n d) &&
            searchAuxS n dflt M' (if j.val < u then u else u + 1) (d + 1) fuel'
      else searchAuxS n dflt M u (d + 1) fuel'

/-- **Is there an admissible colouring of `K_n` with `k+1` colours?** -/
def hasAdmissibleSym (n k : ℕ) : Bool :=
  searchAuxS n (k := k + 1) ⟨0, by omega⟩ (fun _ => none) 0 0 (n * n)

/-! ### Completeness of the symmetry-reduced search -/

private theorem getD_some' {k : ℕ} {M : PTab k} {dflt : Fin k} {s : ℕ} {j : Fin k}
    (h : M s = some j) : (M s).getD dflt = j := by
  simp only [h, Option.getD_some]

end JSP140
