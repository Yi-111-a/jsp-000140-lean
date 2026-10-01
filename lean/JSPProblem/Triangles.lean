import JSPProblem.Criterion
import JSPProblem.Slack

/-!
# JSP-000140 — the published construction, encoded as a family of **labelled triangles**

Rounds 10–28 of this development proved the lower half of the catalog answer
`f(n, 4, 5) = 5n/6 + o(n)`, described the structure an extremal colouring must have
(`Rigidity`, `Classwise`, `Local`, `Star`), and turned the catalog condition into four local
conditions (`Criterion.design_iff_admissible`).  What was still missing was **the construction
itself**, in a shape a formalisation could use.

## What the literature actually does

* Bennett, Cushman, Dudek, Prałat, arXiv:2207.02920 (= JCTB 2024) prove
  `f(n, 4, 5) ≤ 5n/6 + o(n)` by a *randomised* process (random triangle removal, analysed with the
  differential-equation method).
* **Joos–Mubayi, arXiv:2208.12563, "Ramsey theory constructions from hypergraph matchings", give an
  alternative and much shorter solution of the same statement.**  Their §4 encodes the construction
  as a matching problem in an auxiliary `8`-uniform hypergraph `H` with vertex set
  `E(K_n) ∪ V'`, whose edges are

  `{uv, uw, vw, u_i, v_i, w_i, v_j, w_j}`  for a triangle `u v w` of `K_n` and `i ≠ j`,

  i.e. **a triangle `{u, v, w}`, a labelled (central) vertex `u`, a *path colour* on the two edges
  `uv, uw` meeting at `u`, and an *opposite colour* on the third edge `vw`.**  A *matching* `M`
  in `H` is precisely a family of edge-disjoint labelled triangles with the property that **every
  pair `(vertex, colour)` is used by at most one triangle** — that is what "matching in `H`" says,
  because the copies `x_i` of the vertices are hypervertices of `H`.  The conflict system `C`
  excludes the 2-coloured four-sets.

This file gives the *combinatorial content* of that encoding — no hypergraphs, no random thinning,
no differential equations, no local lemma — and proves:

* `tile_of_tri`, `packed_of_tri` — **`Tile` and `Packed` are FREE for a construction of this
  shape.**  They follow from the matching condition alone, so the only local conditions a
  construction has to verify are the two four-set ones.
* `admissible_of_tri` — **THE VERIFICATION LEMMA.**  A colouring built out of labelled triangles
  which cover every edge, with pairwise disjoint `(vertex, colour)` usage and no bad and no
  crossing four-set, is admissible.
* `jsp_000140_main_of_tri_family` — **the required theorem `jsp_000140_main` reduced to
  `TriFamily`**, the published construction stated as a *checkable* hypothesis.
-/

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

namespace JSP140

variable {n k : ℕ}

/-! ### Labelled triangles -/

/-- **A LABELLED TRIANGLE of the colouring `c`.**  An ordered triple of *distinct* vertices
`(u, p, q)` such that the two edges `s(u,p)`, `s(u,q)` meeting at the **labelled (central) vertex**
`u` have the same colour, and the third edge `s(p,q)` — the *opposite edge* — has a different one.

In arXiv:2208.12563 §4 this is the data attached to a triangle `uvw` of the auxiliary hypergraph:
one colour is used twice (on `uv, uw`), the other once (on `vw`), and the two colours differ. -/
def LabTri {n k : ℕ} (c : Col n k) (u p q : Verts n) : Prop :=
  u ≠ p ∧ u ≠ q ∧ p ≠ q ∧ c s(u, p) = c s(u, q) ∧ c s(u, p) ≠ c s(p, q)

theorem LabTri.ne {n k : ℕ} {c : Col n k} {u p q : Verts n} (h : LabTri c u p q) :
    u ≠ p ∧ u ≠ q ∧ p ≠ q :=
  ⟨h.1, h.2.1, h.2.2.1⟩

/-- **THE THREE EDGES OF A LABELLED TRIANGLE.** -/
def triEdges {n k : ℕ} (c : Col n k) (u p q : Verts n) : Finset (Sym2 (Verts n)) :=
  insert (s(u, p)) (insert (s(u, q)) (insert (s(p, q)) ∅))

/-- **THE THREE VERTICES OF A LABELLED TRIANGLE.** -/
def triVerts {n : ℕ} (u p q : Verts n) : Finset (Verts n) :=
  insert u (insert p (insert q ∅))

/-- **THE FIVE `(VERTEX, COLOUR)` PAIRS OF A LABELLED TRIANGLE.**  These are exactly the five
hypervertices `{u_i, v_i, w_i, v_j, w_j}` of arXiv:2208.12563 §4 — the copies of vertices that an
edge of the auxiliary hypergraph uses.  The matching condition says that no pair is used twice, and
the constant `5/6` of the catalog answer is precisely the ratio "five pairs per triangle". -/
def triPairs {n k : ℕ} (c : Col n k) (u p q : Verts n) : Finset (Verts n × Fin k) :=
  insert (u, c s(u, p))
    (insert (p, c s(u, p)) (insert (q, c s(u, p))
      (insert (p, c s(p, q)) (insert (q, c s(p, q)) ∅))))

/-- A finset whose elements are all one of two given elements is contained in the two-element
set. -/
private theorem sub_insert2 {α : Type*} [DecidableEq α] {s : Finset α} {a b : α}
    (h : ∀ x ∈ s, x = a ∨ x = b) : s ⊆ insert a (insert b ∅) := by
  intro x hx
  simp only [Finset.mem_insert]
  rcases h x hx with h' | h'
  · exact Or.inl h'
  · exact Or.inr (Or.inl h')

/-- A finset whose elements are all one given element is a singleton at most. -/
private theorem sub1 {α : Type*} [DecidableEq α] {s : Finset α} {a : α}
    (h : ∀ x ∈ s, x = a) : s ⊆ insert a ∅ := by
  intro x hx
  simp only [Finset.mem_insert]
  exact Or.inl (h x hx)

/-- A finset whose elements are all one given element is a singleton at most. -/
private theorem sub_insert1 {α : Type*} [DecidableEq α] {s : Finset α} {a : α}
    (h : ∀ x ∈ s, x = a) : s.card ≤ 1 := by
  have hsub : s ⊆ ({a} : Finset α) := by
    intro x hx
    rw [Finset.mem_singleton]
    exact h x hx
  exact le_trans (Finset.card_le_card hsub) (by simp)

/-- Two elements of a finset of cardinality at least two. -/
private theorem exists_two_mem {α : Type*} [DecidableEq α] {s : Finset α} (h : 2 ≤ s.card) :
    ∃ x y : α, x ≠ y ∧ x ∈ s ∧ y ∈ s := by
  by_cases he : s.card = 2
  · obtain ⟨x, y, hxy, hs⟩ := Finset.card_eq_two.mp he
    rw [hs] at h ⊢
    exact ⟨x, y, hxy, by simp, by simp⟩
  · have hne : s.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro hE
      rw [hE, Finset.card_empty] at h
      omega
    obtain ⟨x, hx⟩ := hne
    have hrem : (s.erase x).card = s.card - 1 := Finset.card_erase_of_mem hx
    have hrem2 : 1 ≤ (s.erase x).card := by omega
    obtain ⟨y, hy⟩ := Finset.card_pos.mp hrem2
    exact ⟨x, y, Ne.symm (Finset.mem_erase.mp hy).1, hx, (Finset.mem_erase.mp hy).2⟩

@[simp] theorem mem_triVerts {n : ℕ} {u p q x : Verts n} :
    x ∈ triVerts u p q ↔ x = u ∨ x = p ∨ x = q := by
  simp [triVerts]

theorem card_triVerts {n : ℕ} {u p q : Verts n} (h : u ≠ p ∧ u ≠ q ∧ p ≠ q) :
    (triVerts u p q).card = 3 := by
  rw [triVerts, Finset.card_insert_of_notMem (by simp [h.1, h.2.1]),
    Finset.card_insert_of_notMem (by simp [h.2.2]), Finset.card_insert_of_notMem (by simp)]
  simp

theorem eq_triEdges {n k : ℕ} {c : Col n k} {u p q : Verts n} {e : Sym2 (Verts n)}
    (he : e ∈ triEdges c u p q) : e = s(u, p) ∨ e = s(u, q) ∨ e = s(p, q) := by
  simp only [triEdges, Finset.mem_insert] at he
  simpa using he

theorem mem_triPairs {n k : ℕ} {c : Col n k} {u p q : Verts n} {x : Verts n} {j : Fin k} :
    (x, j) ∈ triPairs c u p q ↔
      (j = c s(u, p) ∧ (x = u ∨ x = p ∨ x = q)) ∨ (j = c s(p, q) ∧ (x = p ∨ x = q)) := by
  simp only [triPairs, Finset.mem_insert, Prod.mk.injEq, and_true] at *
  tauto

@[simp] theorem mem_triPairs_1 {n k : ℕ} {c : Col n k} (u p q : Verts n) :
    (u, c s(u, p)) ∈ triPairs c u p q := mem_triPairs.mpr (Or.inl ⟨rfl, Or.inl rfl⟩)

@[simp] theorem mem_triPairs_2 {n k : ℕ} {c : Col n k} (u p q : Verts n) :
    (p, c s(u, p)) ∈ triPairs c u p q := mem_triPairs.mpr (Or.inl ⟨rfl, Or.inr (Or.inl rfl)⟩)

@[simp] theorem mem_triPairs_3 {n k : ℕ} {c : Col n k} (u p q : Verts n) :
    (q, c s(u, p)) ∈ triPairs c u p q := mem_triPairs.mpr (Or.inl ⟨rfl, Or.inr (Or.inr rfl)⟩)

@[simp] theorem mem_triPairs_4 {n k : ℕ} {c : Col n k} (u p q : Verts n) :
    (p, c s(p, q)) ∈ triPairs c u p q := mem_triPairs.mpr (Or.inr ⟨rfl, Or.inl rfl⟩)

@[simp] theorem mem_triPairs_5 {n k : ℕ} {c : Col n k} (u p q : Verts n) :
    (q, c s(p, q)) ∈ triPairs c u p q := mem_triPairs.mpr (Or.inr ⟨rfl, Or.inr rfl⟩)

/-- **THE ACCOUNTING OF A SINGLE EDGE.**  Every endpoint of an edge of a labelled triangle uses the
`(vertex, colour)` pair of that edge's colour: this is why "matching in `H`" controls the
colouring. -/
theorem mem_triPairs_anchor {n k : ℕ} {c : Col n k} {u p q : Verts n} (h : LabTri c u p q)
    {e : Sym2 (Verts n)} {x : Verts n} (he : e ∈ triEdges c u p q) (hx : x ∈ e) :
    (x, c e) ∈ triPairs c u p q := by
  rcases eq_triEdges he with he | he | he
  · rw [he] at hx
    rw [Sym2.mem_iff] at hx
    rw [he]
    rcases hx with h1 | h1
    · rw [h1]; exact mem_triPairs_1 u p q
    · rw [h1]; exact mem_triPairs_2 u p q
  · rw [he] at hx
    rw [Sym2.mem_iff] at hx
    have hcol : c s(u, q) = c s(u, p) := h.2.2.2.1.symm
    rw [he, hcol]
    rcases hx with h1 | h1
    · rw [h1]; exact mem_triPairs_1 u p q
    · rw [h1]; exact mem_triPairs_3 u p q
  · rw [he] at hx
    rw [Sym2.mem_iff] at hx
    rw [he]
    rcases hx with h1 | h1
    · rw [h1]; exact mem_triPairs_4 u p q
    · rw [h1]; exact mem_triPairs_5 u p q

theorem mem_mem_triEdges {n k : ℕ} {c : Col n k} {u p q x y : Verts n} (h : LabTri c u p q)
    (he : s(x, y) ∈ triEdges c u p q) : x ∈ triVerts u p q ∧ y ∈ triVerts u p q := by
  rcases eq_triEdges he with h1 | h1 | h1
  · have hx : x = u ∨ x = p := by
      have hxm : x ∈ s(u, p) := by rw [← h1]; exact Sym2.mem_mk_left x y
      rw [Sym2.mem_iff] at hxm
      exact hxm
    have hy : y = u ∨ y = p := by
      have hym : y ∈ s(u, p) := by rw [← h1]; exact Sym2.mem_mk_right x y
      rw [Sym2.mem_iff] at hym
      exact hym
    constructor
    · rcases hx with h2 | h2 <;> simp [h2]
    · rcases hy with h2 | h2 <;> simp [h2]
  · have hx : x = u ∨ x = q := by
      have hxm : x ∈ s(u, q) := by rw [← h1]; exact Sym2.mem_mk_left x y
      rw [Sym2.mem_iff] at hxm
      exact hxm
    have hy : y = u ∨ y = q := by
      have hym : y ∈ s(u, q) := by rw [← h1]; exact Sym2.mem_mk_right x y
      rw [Sym2.mem_iff] at hym
      exact hym
    constructor
    · rcases hx with h2 | h2 <;> simp [h2]
    · rcases hy with h2 | h2 <;> simp [h2]
  · have hx : x = p ∨ x = q := by
      have hxm : x ∈ s(p, q) := by rw [← h1]; exact Sym2.mem_mk_left x y
      rw [Sym2.mem_iff] at hxm
      exact hxm
    have hy : y = p ∨ y = q := by
      have hym : y ∈ s(p, q) := by rw [← h1]; exact Sym2.mem_mk_right x y
      rw [Sym2.mem_iff] at hym
      exact hym
    constructor
    · rcases hx with h2 | h2 <;> simp [h2]
    · rcases hy with h2 | h2 <;> simp [h2]

theorem ne_of_mem_triEdges {n k : ℕ} {c : Col n k} {u p q x y : Verts n}
    (h : LabTri c u p q) (he : s(x, y) ∈ triEdges c u p q) : x ≠ y := by
  rcases eq_triEdges he with h1 | h1 | h1
  · intro hxy
    rcases sym2_inj h1.symm with ⟨hA, hB⟩ | ⟨hA, hB⟩
    · exact h.1 (hA.trans (hxy.trans hB.symm))
    · exact h.1 (hA.trans (hxy.symm.trans hB.symm))
  · intro hxy
    rcases sym2_inj h1.symm with ⟨hA, hB⟩ | ⟨hA, hB⟩
    · exact h.2.1 (hA.trans (hxy.trans hB.symm))
    · exact h.2.1 (hA.trans (hxy.symm.trans hB.symm))
  · intro hxy
    rcases sym2_inj h1.symm with ⟨hA, hB⟩ | ⟨hA, hB⟩
    · exact h.2.2.1 (hA.trans (hxy.trans hB.symm))
    · exact h.2.2.1 (hA.trans (hxy.symm.trans hB.symm))

theorem card_triEdges {n k : ℕ} {c : Col n k} {u p q : Verts n} (h : LabTri c u p q) :
    (triEdges c u p q).card = 3 := by
  have h12 : s(u, p) ≠ s(u, q) := fun hc => h.2.2.1 (sym2_inj_right hc)
  have h13 : s(u, p) ≠ s(p, q) := by
    intro hc
    rcases sym2_inj hc with ⟨hA, _⟩ | ⟨hA, _⟩
    · exact h.1 hA
    · exact h.2.1 hA
  have h23 : s(u, q) ≠ s(p, q) := by
    intro hc
    rcases sym2_inj hc with ⟨hA, _⟩ | ⟨hA, _⟩
    · exact h.1 hA
    · exact h.2.1 hA
  have e1 : s(u, p) ∉ (insert (s(u, q)) (insert (s(p, q)) ∅) : Finset (Sym2 (Verts n))) := by
    intro hc
    rcases Finset.mem_insert.mp hc with hc1 | hc
    · exact h12 hc1
    · rcases Finset.mem_insert.mp hc with hc2 | hc
      · exact h13 hc2
      · exact absurd hc (by simp)
  have e2 : s(u, q) ∉ (insert (s(p, q)) ∅ : Finset (Sym2 (Verts n))) := by
    intro hc
    rcases Finset.mem_insert.mp hc with hc1 | hc
    · exact h23 hc1
    · exact absurd hc (by simp)
  rw [triEdges, Finset.card_insert_of_notMem e1, Finset.card_insert_of_notMem e2]
  simp

/-- **THE EDGES OF A LABELLED TRIANGLE ARE THE EDGES OF THE COMPLETE GRAPH ON ITS THREE
VERTICES.** -/
theorem triEdges_eq_edgeFinset {n k : ℕ} {c : Col n k} {u p q : Verts n} (h : LabTri c u p q) :
    triEdges c u p q = edgeFinset (triVerts u p q) := by
  have hsub : triEdges c u p q ⊆ edgeFinset (triVerts u p q) := by
    intro e he
    obtain ⟨x, y, rfl⟩ : ∃ x y : Verts n, e = s(x, y) :=
      Quot.inductionOn e (fun p : Verts n × Verts n => ⟨p.1, p.2, rfl⟩)
    exact mem_edgeFinset_mk (mem_mem_triEdges h he).1 (mem_mem_triEdges h he).2
      (ne_of_mem_triEdges h he)
  refine Finset.eq_of_subset_of_card_le hsub ?_
  have h2 : (edgeFinset (triVerts u p q)).card = 3 := by
    rw [card_edgeFinset, card_triVerts h.ne]
    decide
  rw [card_triEdges h]
  omega

/-- Two labelled triangles on the same three vertices have the same three edges. -/
theorem triEdges_eq_of_eq_verts {n k : ℕ} {c : Col n k} {u p q u' p' q' : Verts n}
    (h1 : LabTri c u p q) (h2 : LabTri c u' p' q')
    (hv : triVerts u p q = triVerts u' p' q') : triEdges c u p q = triEdges c u' p' q' := by
  rw [triEdges_eq_edgeFinset h1, triEdges_eq_edgeFinset h2, hv]

/-! ### The two structural conditions of the encoding -/

/-- **COVERING.**  Every edge of `K_n` lies in one of the labelled triangles.  In arXiv:2208.12563
§4 this is the hypergraph `H` spanning all of `E(G)` (up to `o(n²)` edges). -/
def Covers {n k : ℕ} (c : Col n k) : Prop :=
  ∀ e : Sym2 (Verts n), OffDiag e → ∃ u p q : Verts n, LabTri c u p q ∧ e ∈ triEdges c u p q

/-- **THE MATCHING CONDITION.**  Two labelled triangles with different vertex sets use disjoint sets
of `(vertex, colour)` pairs; this is what it means for the corresponding edges of the auxiliary
`8`-graph `H` of arXiv:2208.12563 §4 to form a matching. -/
def PairFree {n k : ℕ} (c : Col n k) : Prop :=
  ∀ (u p q u' p' q' : Verts n), LabTri c u p q → LabTri c u' p' q' →
    triVerts u p q ≠ triVerts u' p' q' → triPairs c u p q ∩ triPairs c u' p' q' = ∅

theorem PairFree.of_common {n k : ℕ} {c : Col n k} (hP : PairFree c) {u p q u' p' q' : Verts n}
    (h1 : LabTri c u p q) (h2 : LabTri c u' p' q') {x : Verts n} {j : Fin k}
    (hm : (x, j) ∈ triPairs c u p q ∩ triPairs c u' p' q') :
    triVerts u p q = triVerts u' p' q' := by
  by_contra hcon
  have happ : (x, j) ∈ (triPairs c u p q ∩ triPairs c u' p' q') := hm
  rw [hP u p q u' p' q' h1 h2 hcon] at happ
  simpa using happ

/-- **TWO LABELLED TRIANGLES MEETING IN AN EDGE ARE THE SAME TRIANGLE.**  This is the combinatorial
form of "the triangles of the construction are edge-disjoint". -/
theorem triVerts_eq_of_mem_triEdges {n k : ℕ} {c : Col n k} (hP : PairFree c)
    {u p q u' p' q' : Verts n} (h1 : LabTri c u p q) (h2 : LabTri c u' p' q')
    {e : Sym2 (Verts n)} (he : e ∈ triEdges c u p q ∩ triEdges c u' p' q') :
    triVerts u p q = triVerts u' p' q' := by
  obtain ⟨a, b, rfl⟩ : ∃ a b : Verts n, e = s(a, b) :=
    Quot.inductionOn e (fun p : Verts n × Verts n => ⟨p.1, p.2, rfl⟩)
  have he1 : s(a, b) ∈ triEdges c u p q := (Finset.mem_inter.mp he).1
  have he2 : s(a, b) ∈ triEdges c u' p' q' := (Finset.mem_inter.mp he).2
  have hm1 : (a, c s(a, b)) ∈ triPairs c u p q :=
    mem_triPairs_anchor h1 he1 (Sym2.mem_mk_left a b)
  have hm2 : (a, c s(a, b)) ∈ triPairs c u' p' q' :=
    mem_triPairs_anchor h2 he2 (Sym2.mem_mk_left a b)
  have hm : (a, c s(a, b)) ∈ (triPairs c u p q ∩ triPairs c u' p' q') :=
    Finset.mem_inter.mpr ⟨hm1, hm2⟩
  exact hP.of_common (x := a) (j := c s(a, b)) h1 h2 hm

/-! ### The colour-`i` edges at a vertex lie in ONE triangle -/

/-- **THE KEY STEP OF THE ENCODING.**  If the colouring is covered by labelled triangles and two
triangles never share a `(vertex, colour)` pair, then *all* colour-`i` edges at `v` lie in one
single labelled triangle. -/
theorem exists_labTri_of_mem {n k : ℕ} {c : Col n k} (hC : Covers c) (hP : PairFree c)
    {i : Fin k} {v : Verts n} (hv : 1 ≤ (Nbrs c i v).card) :
    ∃ u p q : Verts n, LabTri c u p q ∧
      ∀ x : Verts n, x ∈ Nbrs c i v → s(v, x) ∈ triEdges c u p q := by
  have hne : (Nbrs c i v) ≠ ∅ := by
    intro hE
    rw [hE, Finset.card_empty] at hv
    omega
  obtain ⟨a, ha⟩ : ∃ a, a ∈ Nbrs c i v := Finset.nonempty_iff_ne_empty.mpr hne
  obtain ⟨u0, p0, q0, h0, he0⟩ := hC s(v, a) (offDiag_iff.mpr (Ne.symm (mem_Nbrs.mp ha).1))
  refine ⟨u0, p0, q0, h0, fun x hx => ?_⟩
  obtain ⟨u1, p1, q1, h1, he1⟩ := hC s(v, x) (offDiag_iff.mpr (Ne.symm (mem_Nbrs.mp hx).1))
  have hia : c s(v, a) = i := (mem_Nbrs.mp ha).2
  have hix : c s(v, x) = i := (mem_Nbrs.mp hx).2
  have hv0 : (v, i) ∈ triPairs c u0 p0 q0 := by
    rw [← hia]; exact mem_triPairs_anchor h0 he0 (Sym2.mem_mk_left v a)
  have hv1 : (v, i) ∈ triPairs c u1 p1 q1 := by
    rw [← hix]; exact mem_triPairs_anchor h1 he1 (Sym2.mem_mk_left v x)
  have hmem : (v, i) ∈ (triPairs c u0 p0 q0 ∩ triPairs c u1 p1 q1) :=
    Finset.mem_inter.mpr ⟨hv0, hv1⟩
  have hvv : triVerts u0 p0 q0 = triVerts u1 p1 q1 :=
    hP.of_common (x := v) (j := i) h0 h1 hmem
  rw [(triEdges_eq_of_eq_verts h0 h1 hvv).symm] at he1
  exact he1

/-- **A LEAF HAS COLOUR-DEGREE AT MOST ONE.**  If every colour-`i` edge at `v` lies in the labelled
triangle `(u,p,q)` and `v` is one of the two leaves, then `v` has at most one colour-`i`
neighbour. -/
private theorem leaf_of_tri {n k : ℕ} {c : Col n k} {i : Fin k} {u p q v : Verts n}
    (h : LabTri c u p q) (hv : v = p ∨ v = q)
    (hmem : ∀ x : Verts n, x ∈ Nbrs c i v → s(v, x) ∈ triEdges c u p q) :
    (Nbrs c i v).card ≤ 1 := by
  rcases hv with hv | hv
  · have hmem' : ∀ x ∈ Nbrs c i v, s(p, x) ∈ triEdges c u p q := by
      intro x hx; simpa [hv] using hmem x hx
    have hsub : ∀ x ∈ Nbrs c i v, x ∈ triVerts u p q :=
      fun x hx => (mem_mem_triEdges h (hmem' x hx)).2
    by_cases hu0 : u ∈ Nbrs c i v
    · have hu : u ∈ Nbrs c i p := by rw [hv] at hu0; exact hu0
      have hq0 : q ∉ Nbrs c i v := by
        intro hq0
        have hq : q ∈ Nbrs c i p := by rw [hv] at hq0; exact hq0
        have e1 : c s(p, u) = i := (mem_Nbrs.mp hu).2
        have e2 : c s(p, q) = i := (mem_Nbrs.mp hq).2
        rw [Sym2.eq_swap] at e1
        exact h.2.2.2.2 (e1.trans e2.symm)
      exact sub_insert1 (a := u) (fun x hx => by
        rcases (mem_triVerts.mp (hsub x hx)) with hA | hA | hA
        · exact hA
        · exact absurd (hA.trans hv.symm) (mem_Nbrs.mp hx).1
        · exact absurd (hA ▸ hx) hq0)
    · exact sub_insert1 (a := q) (fun x hx => by
        rcases (mem_triVerts.mp (hsub x hx)) with hA | hA | hA
        · exact absurd (hA ▸ hx) hu0
        · exact absurd (hA.trans hv.symm) (mem_Nbrs.mp hx).1
        · exact hA)
  · have hmem' : ∀ x ∈ Nbrs c i v, s(q, x) ∈ triEdges c u p q := by
      intro x hx; simpa [hv] using hmem x hx
    have hsub : ∀ x ∈ Nbrs c i v, x ∈ triVerts u p q :=
      fun x hx => (mem_mem_triEdges h (hmem' x hx)).2
    by_cases hu0 : u ∈ Nbrs c i v
    · have hu : u ∈ Nbrs c i q := by rw [hv] at hu0; exact hu0
      have hp0 : p ∉ Nbrs c i v := by
        intro hp0
        have hp : p ∈ Nbrs c i q := by rw [hv] at hp0; exact hp0
        have e1 : c s(q, u) = i := (mem_Nbrs.mp hu).2
        have e2 : c s(q, p) = i := (mem_Nbrs.mp hp).2
        have f1 : c s(q, u) = c s(u, q) := by rw [Sym2.eq_swap]
        have f2 : c s(q, p) = c s(p, q) := by rw [Sym2.eq_swap]
        have g : c s(u, q) = c s(p, q) := f1.symm.trans (e1.trans (e2.symm.trans f2))
        exact h.2.2.2.2 (h.2.2.2.1.trans g)
      exact sub_insert1 (a := u) (fun x hx => by
        rcases (mem_triVerts.mp (hsub x hx)) with hA | hA | hA
        · exact hA
        · exact absurd (hA ▸ hx) hp0
        · exact absurd (hA.trans hv.symm) (mem_Nbrs.mp hx).1)
    · exact sub_insert1 (a := p) (fun x hx => by
        rcases (mem_triVerts.mp (hsub x hx)) with hA | hA | hA
        · exact absurd (hA ▸ hx) hu0
        · exact hA
        · exact absurd (hA.trans hv.symm) (mem_Nbrs.mp hx).1)

/-- **THE COLOUR-`i` NEIGHBOURS OF A VERTEX INSIDE A LABELLED TRIANGLE.**  If every colour-`i` edge
at `v` lies in the labelled triangle `(u,p,q)`, then either `v = u` — and `v` has at most the two
leaves as colour-`i` neighbours — or `v` is a leaf and has colour-degree at most one.  This is the
whole content of the matching condition. -/
private theorem nbrs_of_tri {n k : ℕ} {c : Col n k} {i : Fin k} {u p q v : Verts n}
    (h : LabTri c u p q) (hv : v ∈ triVerts u p q)
    (hmem : ∀ x : Verts n, x ∈ Nbrs c i v → s(v, x) ∈ triEdges c u p q) :
    (v = u ∧ Nbrs c i v ⊆ insert p (insert q ∅)) ∨ (v ≠ u ∧ (Nbrs c i v).card ≤ 1) := by
  rcases (mem_triVerts.mp hv) with hv | hv | hv
  · refine Or.inl ⟨hv, sub_insert2 (a := p) (b := q) (fun x hx => ?_)⟩
    have hx' : x ∈ triVerts u p q := (mem_mem_triEdges h (hmem x hx)).2
    rcases (mem_triVerts.mp hx') with hA | hA | hA
    · exact absurd (hA.trans hv.symm) (mem_Nbrs.mp hx).1
    · exact Or.inl hA
    · exact Or.inr hA
  · refine Or.inr ⟨fun hh => h.1 (hh.symm.trans hv), leaf_of_tri h (Or.inl hv) hmem⟩
  · refine Or.inr ⟨fun hh => h.2.1 (hh.symm.trans hv), leaf_of_tri h (Or.inr hv) hmem⟩

/-- **THE COLOUR-DEGREE BOUND IS FREE.**  Under `Covers` and `PairFree` every vertex has at most two
colour-`i` neighbours — the first half of `Criterion.Tile`, and hence the whole of
`Counting.nb_card_le_two`, without any four-vertex clique being checked. -/
theorem nb_le_two_of_tri {n k : ℕ} {c : Col n k} (hC : Covers c) (hP : PairFree c)
    (i : Fin k) (v : Verts n) : (Nbrs c i v).card ≤ 2 := by
  by_cases hv0 : (Nbrs c i v).card = 0
  · rw [hv0]; omega
  obtain ⟨u, p, q, h, hmem⟩ :=
    exists_labTri_of_mem hC hP (Nat.succ_le_of_lt (Nat.pos_of_ne_zero hv0))
  have hne : (Nbrs c i v) ≠ ∅ := by
    intro hE
    exact hv0 (by rw [hE]; simp)
  obtain ⟨a, ha⟩ : ∃ a, a ∈ Nbrs c i v := Finset.nonempty_iff_ne_empty.mpr hne
  have hvsub : v ∈ triVerts u p q := (mem_mem_triEdges h (hmem a ha)).1
  rcases nbrs_of_tri h hvsub hmem with hcase | hcase
  · refine le_trans (Finset.card_le_card hcase.2) ?_
    have hne : p ∉ (insert q ∅ : Finset (Verts n)) := by simp [h.2.2.1]
    rw [Finset.card_insert_of_notMem hne, Finset.card_insert_of_notMem (by simp)]
    simp
  · exact le_trans hcase.2 (by omega)

/-- **A VERTEX WITH TWO COLOUR-`i` NEIGHBOURS IS THE LABELLED VERTEX OF ITS TRIANGLE, WITH BOTH
LEAVES.** -/
theorem centre_of_card_two {n k : ℕ} {c : Col n k} (hC : Covers c) (hP : PairFree c)
    {i : Fin k} {v : Verts n} (hcard : (Nbrs c i v).card = 2) :
    ∃ u p q : Verts n, LabTri c u p q ∧ v = u ∧ Nbrs c i v = insert p (insert q ∅) ∧
      p ∈ Nbrs c i v ∧ q ∈ Nbrs c i v := by
  obtain ⟨u, p, q, h, hmem⟩ := exists_labTri_of_mem hC hP (by rw [hcard]; omega)
  have hne : (Nbrs c i v) ≠ ∅ := by
    intro hE
    rw [hE, Finset.card_empty] at hcard
    omega
  obtain ⟨a, ha⟩ : ∃ a, a ∈ Nbrs c i v := Finset.nonempty_iff_ne_empty.mpr hne
  have hvsub : v ∈ triVerts u p q := (mem_mem_triEdges h (hmem a ha)).1
  rcases nbrs_of_tri h hvsub hmem with hcase | hcase
  · obtain ⟨hv, hN⟩ := hcase
    have hEq : Nbrs c i v = insert p (insert q ∅) := by
      refine Finset.eq_of_subset_of_card_le hN ?_
      rw [hcard]
      have hne : p ∉ (insert q ∅ : Finset (Verts n)) := by simp [h.2.2.1]
      rw [Finset.card_insert_of_notMem hne, Finset.card_insert_of_notMem (by simp)]
      simp
    refine ⟨u, p, q, h, hv, hEq, ?_, ?_⟩
    · rw [hEq]; simp
    · rw [hEq]; simp
  · exfalso
    omega

/-- **ALL COLOUR-`i` EDGES OF A VERTEX THAT USES ONE PAIR.**  If `(x, i)` is one of the five pairs
of a labelled triangle, then every colour-`i` edge at `x` lies in that triangle. -/
theorem sub_of_mem_triPairs {n k : ℕ} {c : Col n k} (hC : Covers c) (hP : PairFree c)
    {i : Fin k} {u p q x : Verts n} (h : LabTri c u p q) (hx : (x, i) ∈ triPairs c u p q)
    (hxv : x ∈ triVerts u p q) :
    ∀ y : Verts n, y ∈ Nbrs c i x → s(x, y) ∈ triEdges c u p q := by
  intro y hy
  obtain ⟨a, ha⟩ : ∃ a, a ∈ Nbrs c i x := ⟨y, hy⟩
  obtain ⟨u0, p0, q0, h0, he0⟩ := hC s(x, a) (offDiag_iff.mpr (Ne.symm (mem_Nbrs.mp ha).1))
  have ixa : c s(x, a) = i := (mem_Nbrs.mp ha).2
  have ixy : c s(x, y) = i := (mem_Nbrs.mp hy).2
  have hv0 : (x, i) ∈ triPairs c u0 p0 q0 := by
    rw [← ixa]; exact mem_triPairs_anchor h0 he0 (Sym2.mem_mk_left x a)
  have hmem0 : (x, i) ∈ (triPairs c u0 p0 q0 ∩ triPairs c u p q) :=
    Finset.mem_inter.mpr ⟨hv0, hx⟩
  have hvv : triVerts u0 p0 q0 = triVerts u p q :=
    hP.of_common (x := x) (j := i) h0 h hmem0
  obtain ⟨u1, p1, q1, h1, he1⟩ := hC s(x, y) (offDiag_iff.mpr (Ne.symm (mem_Nbrs.mp hy).1))
  have hv1 : (x, i) ∈ triPairs c u1 p1 q1 := by
    rw [← ixy]; exact mem_triPairs_anchor h1 he1 (Sym2.mem_mk_left x y)
  have hmem1 : (x, i) ∈ (triPairs c u1 p1 q1 ∩ triPairs c u p q) :=
    Finset.mem_inter.mpr ⟨hv1, hx⟩
  have hvv' : triVerts u1 p1 q1 = triVerts u p q :=
    hP.of_common (x := x) (j := i) h1 h hmem1
  have hsame : triVerts u1 p1 q1 = triVerts u0 p0 q0 := hvv'.trans hvv.symm
  rw [triEdges_eq_of_eq_verts h1 h0 hsame] at he1
  rw [triEdges_eq_of_eq_verts h0 h hvv] at he1
  exact he1

/-- **THE WHOLE TILING CONDITION IS FREE.**  `Covers` + `PairFree` ⟹ `Tile`: every colour class of a
construction of this shape is a vertex-disjoint union of two-edge paths and isolated single edges,
with *no* four-vertex clique being checked.  This is the sufficiency half of
`Criterion.Tile.of_admissible`. -/
theorem tile_of_tri {n k : ℕ} {c : Col n k} (hC : Covers c) (hP : PairFree c) (hn : 4 ≤ n) :
    Tile c := by
  unfold Tile
  refine fun i v => ⟨?_, ?_⟩
  · exact nb_le_two_of_tri hC hP i v
  · intro a ha hcard
    obtain ⟨u, p, q, h, rfl, hN, hp, hq⟩ := centre_of_card_two hC hP hcard
    have ha' : a = p ∨ a = q := by
      rw [hN] at ha
      rw [Finset.mem_insert, Finset.mem_insert] at ha
      rcases ha with ha'' | ha''
      · exact Or.inl ha''
      · rcases ha'' with ha'' | ha''
        · exact Or.inr ha''
        · exact absurd ha'' (by simp)
    rcases ha' with h1 | h1
    · rw [h1]
      have hsub : Nbrs c i p ⊆ insert v ∅ := sub1 (a := v) (fun x hx => by
        have hvp : c s(v, p) = i := (mem_Nbrs.mp hp).2
        have hxa : (p, i) ∈ triPairs c v p q := by
          rw [← hvp]; exact mem_triPairs_2 (c := c) v p q
        have hpxv : p ∈ triVerts v p q := by simp
        have hsub' : ∀ x ∈ Nbrs c i p, s(p, x) ∈ triEdges c v p q :=
          sub_of_mem_triPairs hC hP h hxa hpxv
        have hx' : x ∈ triVerts v p q := (mem_mem_triEdges h (hsub' x hx)).2
        rcases (mem_triVerts.mp hx') with hA | hA | hA
        · exact hA
        · exact absurd hA (mem_Nbrs.mp hx).1
        · have h1 : c s(p, q) = i := by rw [← hA]; exact (mem_Nbrs.mp hx).2
          have h2 : c s(v, p) = c s(p, q) := (mem_Nbrs.mp hp).2.trans h1.symm
          exact absurd h2 h.2.2.2.2)
      refine le_antisymm (le_trans (Finset.card_le_card hsub) (by simp)) ?_
      exact Nat.succ_le_of_lt (Finset.card_pos.mpr
        ⟨v, by rw [mem_Nbrs]; exact ⟨h.1, by rw [Sym2.eq_swap]; exact (mem_Nbrs.mp hp).2⟩⟩)
    · rw [h1]
      have hsub : Nbrs c i q ⊆ insert v ∅ := sub1 (a := v) (fun x hx => by
        have hvq : c s(v, q) = i := (mem_Nbrs.mp hq).2
        have hαq : c s(v, q) = c s(v, p) := h.2.2.2.1.symm
        have hxa : (q, i) ∈ triPairs c v p q := by
          rw [← hvq, hαq]; exact mem_triPairs_3 (c := c) v p q
        have hqxv : q ∈ triVerts v p q := by simp
        have hsub' : ∀ x ∈ Nbrs c i q, s(q, x) ∈ triEdges c v p q :=
          sub_of_mem_triPairs hC hP h hxa hqxv
        have hx' : x ∈ triVerts v p q := (mem_mem_triEdges h (hsub' x hx)).2
        rcases (mem_triVerts.mp hx') with hA | hA | hA
        · exact hA
        · have h1 : c s(q, p) = i := by rw [← hA]; exact (mem_Nbrs.mp hx).2
          have h2 : c s(v, q) = c s(q, p) := hvq.trans h1.symm
          have h3 : c s(q, p) = c s(p, q) := by rw [Sym2.eq_swap]
          exact absurd (h.2.2.2.1.trans (h2.trans h3)) h.2.2.2.2
        · exact absurd hA (mem_Nbrs.mp hx).1)
      refine le_antisymm (le_trans (Finset.card_le_card hsub) (by simp)) ?_
      exact Nat.succ_le_of_lt (Finset.card_pos.mpr
        ⟨v, by rw [mem_Nbrs]; exact ⟨h.2.1, by rw [Sym2.eq_swap]; exact (mem_Nbrs.mp hq).2⟩⟩)

/-- **THE PACKING CONDITION IS FREE TOO.**  `Covers` + `PairFree` ⟹ `Packed`: two labelled triangles
meeting in two vertices would meet in an edge, hence would be the same triangle with the same
labelled vertex, hence would be the same two-edge path. -/
theorem packed_of_tri {n k : ℕ} {c : Col n k} (hC : Covers c) (hP : PairFree c) (hn : 4 ≤ n) :
    Packed c := by
  intro i j v w hv hw hinter
  have hv2 : (Nbrs c i v).card = 2 := by
    rw [card_Nbrs]
    exact (Finset.mem_filter.mp hv).2
  have hw2 : (Nbrs c j w).card = 2 := by
    rw [card_Nbrs]
    exact (Finset.mem_filter.mp hw).2
  obtain ⟨u, p, q, h, hv1, hN, hp, hq⟩ := centre_of_card_two hC hP hv2
  obtain ⟨u2, p2, q2, h2, hw1, hNw, hp2, hq2⟩ := centre_of_card_two hC hP hw2
  have hps1 : pathSet c i v = triVerts u p q := by rw [pathSet, hN, hv1]; rfl
  have hps2 : pathSet c j w = triVerts u2 p2 q2 := by rw [pathSet, hNw, hw1]; rfl
  obtain ⟨x, y, hxy, hx, hy⟩ :=
    exists_two_mem (s := triVerts u p q ∩ triVerts u2 p2 q2)
      (by rw [← hps1, ← hps2]; exact hinter)
  have hxv1 : x ∈ triVerts u p q := (Finset.mem_inter.mp hx).1
  have hxv2 : x ∈ triVerts u2 p2 q2 := (Finset.mem_inter.mp hx).2
  have hyv1 : y ∈ triVerts u p q := (Finset.mem_inter.mp hy).1
  have hyv2 : y ∈ triVerts u2 p2 q2 := (Finset.mem_inter.mp hy).2
  by_cases heq : triVerts u p q = triVerts u2 p2 q2
  · by_cases hvw : v = w
    · rw [hvw] at hp hq
      have hmem : p ∈ triVerts u2 p2 q2 := by
        rw [← heq]; exact mem_triVerts.mpr (Or.inr (Or.inl rfl))
      rcases (mem_triVerts.mp hmem) with hA | hA | hA
      · exact (h.1 (hA.trans (hw1.symm.trans (hvw.symm.trans hv1))).symm).elim
      · rw [mem_Nbrs] at hp hp2
        rw [← hA] at hp2
        exact hp.2.symm.trans hp2.2
      · rw [← hA] at hq2
        rw [mem_Nbrs] at hp hq2
        exact hp.2.symm.trans hq2.2
    · have hwm : w ∈ triVerts u p q := by
        rw [heq]; exact mem_triVerts.mpr (Or.inl hw1)
      have hvm : v ∈ triVerts u2 p2 q2 := by
        rw [← heq]; exact mem_triVerts.mpr (Or.inl hv1)
      have hwm' : w ∈ Nbrs c i v := by
        rcases (mem_triVerts.mp hwm) with hA | hA | hA
        · exact absurd (hA.trans hv1.symm) (fun hz => hvw hz.symm)
        · rw [hA]; exact hp
        · rw [hA]; exact hq
      have hvm' : v ∈ Nbrs c j w := by
        rcases (mem_triVerts.mp hvm) with hA | hA | hA
        · exact absurd (hA.trans hw1.symm) hvw
        · rw [hA]; exact hp2
        · rw [hA]; exact hq2
      rw [mem_Nbrs] at hwm' hvm'
      have hswap : c s(v, w) = c s(w, v) := by rw [Sym2.eq_swap]
      exact (hwm'.2.symm.trans hswap).trans hvm'.2
  · have hedge1 : s(x, y) ∈ triEdges c u p q := by
      rw [triEdges_eq_edgeFinset h]; exact mem_edgeFinset_mk hxv1 hyv1 hxy
    have hedge2 : s(x, y) ∈ triEdges c u2 p2 q2 := by
      rw [triEdges_eq_edgeFinset h2]; exact mem_edgeFinset_mk hxv2 hyv2 hxy
    exact absurd (triVerts_eq_of_mem_triEdges hP h h2
      (Finset.mem_inter.mpr ⟨hedge1, hedge2⟩)) heq

/-! ### The verification lemma and the reduction of the required theorem -/

/-- **THE VERIFICATION LEMMA.**  A colouring which comes from a family of labelled triangles
covering every edge, with pairwise disjoint `(vertex, colour)` usage, and which has neither a bad
nor a crossing four-set, is admissible.  The four local conditions of `Criterion` are thus reduced
to the two four-set ones: `Tile` and `Packed` are automatic for this shape. -/
theorem admissible_of_tri {n k : ℕ} {c : Col n k} (hn : 4 ≤ n) (hC : Covers c) (hP : PairFree c)
    (hX : NoCrossFour c) (hB : NoBadFour c) : Admissible c :=
  admissible_of_design (tile_of_tri hC hP hn) (packed_of_tri hC hP hn) hX hB

/-- **THE PUBLISHED CONSTRUCTION, IN A CHECKABLE FORM.**  For every `δ > 0` and all large
`m ≡ 1 (mod 6)` there is a `k`-colouring of `K_m` which is *built out of labelled triangles* of the
kind of arXiv:2208.12563 §4 — every edge covered, the `(vertex, colour)` pairs of distinct triangles
disjoint — which has neither a bad nor a crossing four-set, and which uses at most
`5(m-1)/6 + δm/6` colours. -/
def TriFamily : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ M : ℕ, ∀ m : ℕ, M ≤ m → m % 6 = 1 →
    ∃ (k : ℕ) (c : Col m k), Covers c ∧ PairFree c ∧ NoCrossFour c ∧ NoBadFour c ∧
      (6 : ℝ) * (k : ℝ) ≤ 5 * ((m - 1 : ℕ) : ℝ) + δ * (m : ℝ)

/-- A family of labelled-triangle systems gives a family of admissible colourings: this is the
point of the encoding, because it lets the remaining hypothesis be stated for constructions that
are not yet known to be admissible. -/
theorem SlackFamily.of_tri (hfam : TriFamily) : SlackFamily := by
  intro δ hδ
  obtain ⟨M, hM⟩ := hfam δ hδ
  refine ⟨max M 4, fun m hMm hm => ?_⟩
  obtain ⟨k, c, hC, hP, hX, hB, hk⟩ := hM m (by omega) hm
  exact ⟨k, c, admissible_of_tri (by omega) hC hP hX hB, hk⟩

/-- **THE REQUIRED THEOREM, REDUCED TO THE PUBLISHED CONSTRUCTION.**  If for every `δ > 0` and all
large `m ≡ 1 (mod 6)` there is such a labelled-triangle system with at most `5(m-1)/6 + δm/6`
colours, then `jsp_000140_target` — the statement of the required theorem `jsp_000140_main`, i.e.
the catalog answer `f(n, 4, 5) = 5n/6 + o(n)` — holds.

Together with the lower half proved in `Cherry.lean` (`Main.fiveSixthLower_eg`) this identifies the
remaining content of the prize as *only* the existence of labelled-triangle systems, which is the
content of arXiv:2208.12563 §4 (= arXiv:2207.02920). -/
theorem jsp_000140_main_of_tri_family (hfam : TriFamily) : jsp_000140_target :=
  jsp_000140_main_of_slack_family (SlackFamily.of_tri hfam)

end JSP140
