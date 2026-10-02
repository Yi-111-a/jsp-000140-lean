import JSPProblem.First

/-!
# JSP-000140 — the first stage as a **matching in the auxiliary hypergraph**

Every hypothesis of this development up to `First.PartialStageFamily` is stated for a *colouring*
`c : Col n k`:

    `Covers c`, `PairFree c`, `Design c`, `SparseL (leftover c) D`, `CrossThin c₀ (leftover c₀) T`.

That is the wrong way round for an **existence** theorem.  What the constructions of
arXiv:2207.02920 (Phase 1) and arXiv:2208.12563 (§4, Thm 4.2) actually produce is a *matching in an
auxiliary `8`-uniform hypergraph* whose hypervertices are the `(vertex, colour)` **slots**
`V × [k]`; the colouring of `K_n` is a *consequence* of that matching.  So the hypothesis of the
prize must be expressible in terms of the matching alone: a set of configurations, each of which
uses five slots and three edges, no two of which share a slot and no two of which share an edge.

This file introduces that primitive object and proves:

* **`slots_countF`, `edgeCoverF`, `count_lowerF`** — the slot counting of round 36
  (`5|tris| ≤ nk`, `C(n,2) = 3|tris| + |leftover|`, `5(n-1) ≤ 6k + 5D`) **in the world of
  matchings**, where no colouring exists at all;
* **`colOf`** — the colouring *induced* by a family of configurations, with

  * **`labTri_of_mem`**, **`triPairs_eq_cfgSlots`**, **`covers_colOf`**, **`pairFree_colOf`**:
    a matching covering all of `E(K_n)` **is** an admissible-colouring construction, so all of
    `Tile`, `Packed` (rounds 29–30) and the four-vertex conditions can be *checked on the matching*;
  * **`mem_or_mem_swap_of_labTri`** — the converse: every labelled triangle of the induced colouring
    comes from a member of the family (up to the order of its two leaves).  This is what makes
    `PairFree (colOf F)` a genuine statement and not an accident;

* **`FamFamily`** and **`jsp_000140_main_of_fam_family`** — **the required theorem
  `jsp_000140_main`, reduced to the existence of a matching in the auxiliary hypergraph**, i.e. to
  the exact object the published probabilistic construction produces.  No colouring is quantified
  over in the hypothesis, so the hypothesis is *checkable*: it is a finite combinatorial condition on
  a finset of configurations.

## The centre balance (round 37)

A configuration uses its five slots **at three vertices**: one at its centre, two at each of its two
leaves.  Section 5 resolves this vertex by vertex.

* **`centF`, `leafF`, `throughF`** — the configurations centred at `v`, having `v` as a leaf, and
  passing through `v`;
* **`slotsAt`, `slotsAt_centre`, `slotsAt_leaf`, `slotsAt_leaf'`, `slotsAt_ne`** — the slots a
  single configuration uses at one vertex: `{(_, i)}` at the centre, `{(_, i), (_, j)}` at a leaf,
  `∅` elsewhere;
* **`card_slotsAt`** — "one slot at the centre, two at each leaf, none elsewhere";
* **`slotsF`, `slotsF_eq`, `card_slotsF`** — **THE CENTRE BALANCE OF A FAMILY**:
  `(slotsF F v).card = (centF F v).card + 2 · (leafF F v).card`, i.e. the `5 · |F|` slots of a
  matching split, at every vertex, into one slot per configuration centred there and two per
  configuration passing through it as a leaf;
* **`card_slotsF_le`** — a family uses at most `k` slots at any one vertex.

So the vertex-level slot budget of a first stage is fully determined: a vertex which centres `c`
configurations and is a leaf of `l` of them uses exactly `c + 2l` of its `k` slots, and `Σ_v (c_v +
2 l_v) = 5 · |F| ≤ n · k` is `count_lowerF` read vertexwise.  This is the quantity that must come out
*tight* (`Σ_v (c_v + 2 l_v) = n · k`) for the published construction to attain `5n/6 + o(n)`.
-/

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

namespace JSP140

attribute [local instance] Classical.propDecidable

variable {n k : ℕ}

/-! ### 1. Configurations: the edges of the auxiliary hypergraph -/

/-- **A CONFIGURATION.**  `(u, p, q, i, j)`: the centre `u` of a labelled triangle
(arXiv:2208.12563 §4), its two leaves `p, q`, the colour `i` given to the two edges at the centre
and the colour `j` given to the opposite edge `s(p, q)`.

A configuration is *data*, not a colouring: this is what makes the auxiliary hypergraph of
arXiv:2208.12563 §4 / arXiv:2207.02920 Phase 1 a first-class object of the development. -/
abbrev Cfg (n k : ℕ) := Verts n × Verts n × Verts n × Fin k × Fin k

/-- The centre of a configuration. -/
def cfgU {n k : ℕ} (g : Cfg n k) : Verts n := g.1

/-- The first leaf of a configuration. -/
def cfgP {n k : ℕ} (g : Cfg n k) : Verts n := g.2.1

/-- The second leaf of a configuration. -/
def cfgQ {n k : ℕ} (g : Cfg n k) : Verts n := g.2.2.1

/-- The colour of the two edges at the centre. -/
def cfgI {n k : ℕ} (g : Cfg n k) : Fin k := g.2.2.2.1

/-- The colour of the opposite edge. -/
def cfgJ {n k : ℕ} (g : Cfg n k) : Fin k := g.2.2.2.2

/-- **A CONFIGURATION IS WELL FORMED** if its three vertices are pairwise distinct and its two
colours differ — the whole content of `LabTri`, but now without a colouring. -/
def Ok {n k : ℕ} (g : Cfg n k) : Prop :=
  cfgU g ≠ cfgP g ∧ cfgU g ≠ cfgQ g ∧ cfgP g ≠ cfgQ g ∧ cfgI g ≠ cfgJ g

/-- **THE THREE VERTICES OF A CONFIGURATION.** -/
def cfgVerts {n k : ℕ} (g : Cfg n k) : Finset (Verts n) := triVerts (cfgU g) (cfgP g) (cfgQ g)

/-- **THE THREE EDGES OF A CONFIGURATION** — a hyperedge in `E(H_n)`. -/
def cfgEdges {n k : ℕ} (g : Cfg n k) : Finset (Sym2 (Verts n)) :=
  insert (s(cfgU g, cfgP g))
    (insert (s(cfgU g, cfgQ g)) (insert (s(cfgP g, cfgQ g)) ∅))

/-- **THE FIVE SLOTS OF A CONFIGURATION** — the five hypervertices `{u_i, p_i, q_i, p_j, q_j}` of
arXiv:2208.12563 §4. -/
def cfgSlots {n k : ℕ} (g : Cfg n k) : Finset (Verts n × Fin k) :=
  insert (cfgU g, cfgI g)
    (insert (cfgP g, cfgI g) (insert (cfgQ g, cfgI g)
      (insert (cfgP g, cfgJ g) (insert (cfgQ g, cfgJ g) ∅))))

/-- **THE COLOUR A CONFIGURATION GIVES TO AN EDGE.** -/
def edgeCol {n k : ℕ} (g : Cfg n k) (e : Sym2 (Verts n)) : Fin k :=
  if e = s(cfgP g, cfgQ g) then cfgJ g else cfgI g

/-- `Ok` on a configuration presented as a tuple is exactly its four defining inequalities. -/
theorem Ok_tuple {n k : ℕ} {u p q : Verts n} {i j : Fin k} :
    Ok (u, p, q, i, j) ↔ u ≠ p ∧ u ≠ q ∧ p ≠ q ∧ i ≠ j := by
  simp only [Ok, cfgU, cfgP, cfgQ, cfgI, cfgJ]

/-- The four inequalities defining a well-formed configuration. -/
theorem Ok_def {n k : ℕ} {g : Cfg n k} (h : Ok g) :
    cfgU g ≠ cfgP g ∧ cfgU g ≠ cfgQ g ∧ cfgP g ≠ cfgQ g ∧ cfgI g ≠ cfgJ g := h

@[simp] theorem mem_cfgEdges {n k : ℕ} (g : Cfg n k) {e : Sym2 (Verts n)} :
    e ∈ cfgEdges g ↔
      e = s(cfgU g, cfgP g) ∨ e = s(cfgU g, cfgQ g) ∨ e = s(cfgP g, cfgQ g) := by
  simp only [cfgEdges, Finset.mem_insert]
  tauto

@[simp] theorem mem_cfgSlots {n k : ℕ} (g : Cfg n k) {x : Verts n} {j : Fin k} :
    (x, j) ∈ cfgSlots g ↔
      (j = cfgI g ∧ (x = cfgU g ∨ x = cfgP g ∨ x = cfgQ g)) ∨
        (j = cfgJ g ∧ (x = cfgP g ∨ x = cfgQ g)) := by
  simp only [cfgSlots, Finset.mem_insert, Prod.mk.injEq, and_true]
  tauto

@[simp] theorem mem_cfgSlots_1 {n k : ℕ} (g : Cfg n k) : (cfgU g, cfgI g) ∈ cfgSlots g :=
  mem_cfgSlots g |>.mpr (Or.inl ⟨rfl, Or.inl rfl⟩)

@[simp] theorem mem_cfgSlots_2 {n k : ℕ} (g : Cfg n k) : (cfgP g, cfgI g) ∈ cfgSlots g :=
  mem_cfgSlots g |>.mpr (Or.inl ⟨rfl, Or.inr (Or.inl rfl)⟩)

@[simp] theorem mem_cfgSlots_3 {n k : ℕ} (g : Cfg n k) : (cfgQ g, cfgI g) ∈ cfgSlots g :=
  mem_cfgSlots g |>.mpr (Or.inl ⟨rfl, Or.inr (Or.inr rfl)⟩)

@[simp] theorem mem_cfgSlots_4 {n k : ℕ} (g : Cfg n k) : (cfgP g, cfgJ g) ∈ cfgSlots g :=
  mem_cfgSlots g |>.mpr (Or.inr ⟨rfl, Or.inl rfl⟩)

@[simp] theorem mem_cfgSlots_5 {n k : ℕ} (g : Cfg n k) : (cfgQ g, cfgJ g) ∈ cfgSlots g :=
  mem_cfgSlots g |>.mpr (Or.inr ⟨rfl, Or.inr rfl⟩)

/-- **THE THREE EDGES OF A WELL-FORMED CONFIGURATION ARE PAIRWISE DISTINCT.** -/
theorem ne_edges {n k : ℕ} {g : Cfg n k} (h : Ok g) :
    s(cfgU g, cfgP g) ≠ s(cfgU g, cfgQ g) ∧
      s(cfgU g, cfgP g) ≠ s(cfgP g, cfgQ g) ∧
      s(cfgU g, cfgQ g) ≠ s(cfgP g, cfgQ g) := by
  refine ⟨?_, ?_, ?_⟩
  · intro hc
    exact h.2.2.1 (sym2_inj_right hc)
  · intro hc
    rcases sym2_inj hc with hA | hA
    · exact h.1 hA.1
    · exact h.2.1 hA.1
  · intro hc
    rcases sym2_inj hc with hA | hA
    · exact h.1 hA.1
    · exact h.2.1 hA.1

/-- **THREE EDGES PER CONFIGURATION.** -/
theorem card_cfgEdges' {n k : ℕ} {u p q : Verts n} {i j : Fin k}
    (hne : u ≠ p ∧ u ≠ q ∧ p ≠ q) : (cfgEdges (u, p, q, i, j)).card = 3 := by
  have h12 : s(u, p) ≠ s(u, q) := by
    intro hc
    exact hne.2.2 (sym2_inj_right hc)
  have h13 : s(u, p) ≠ s(p, q) := by
    intro hc
    rcases sym2_inj hc with hA | hA
    · exact hne.1 hA.1
    · exact hne.2.1 hA.1
  have h23 : s(u, q) ≠ s(p, q) := by
    intro hc
    rcases sym2_inj hc with hA | hA
    · exact hne.1 hA.1
    · exact hne.2.1 hA.1
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
  have key : cfgEdges (u, p, q, i, j)
      = insert (s(u, p)) (insert (s(u, q)) (insert (s(p, q)) ∅)) := by
    simp only [cfgEdges, cfgU, cfgP, cfgQ]
  rw [key, Finset.card_insert_of_notMem e1, Finset.card_insert_of_notMem e2]
  simp

theorem card_cfgEdges {n k : ℕ} {g : Cfg n k} (h : Ok g) : (cfgEdges g).card = 3 :=
  card_cfgEdges' ⟨(Ok_def h).1, (Ok_def h).2.1, (Ok_def h).2.2.1⟩

/-- **FIVE SLOTS PER CONFIGURATION** — the ratio which produces the constant `5/6`. -/
theorem card_cfgSlots' {n k : ℕ} {u p q : Verts n} {i j : Fin k}
    (hne : u ≠ p ∧ u ≠ q ∧ p ≠ q) (hij : i ≠ j) : (cfgSlots (u, p, q, i, j)).card = 5 := by
  have key : cfgSlots (u, p, q, i, j)
      = insert (u, i) (insert (p, i) (insert (q, i)
        (insert (p, j) (insert (q, j) ∅)))) := by
    simp only [cfgSlots, cfgU, cfgP, cfgQ, cfgI, cfgJ]
  rw [key]
  simp [hne.1, hne.2.1, hne.2.2, hij]

theorem card_cfgSlots {n k : ℕ} {g : Cfg n k} (h : Ok g) : (cfgSlots g).card = 5 :=
  card_cfgSlots' ⟨(Ok_def h).1, (Ok_def h).2.1, (Ok_def h).2.2.1⟩ (Ok_def h).2.2.2

/-- Swapping the two leaves of a configuration changes neither its slots nor its edges. -/
theorem cfgSlots_swap {n k : ℕ} {u p q : Verts n} {i j : Fin k} :
    cfgSlots (u, p, q, i, j) = cfgSlots (u, q, p, i, j) := by
  ext x
  simp only [cfgSlots, cfgU, cfgP, cfgQ, cfgI, cfgJ, Finset.mem_insert]
  tauto

/-- **THE COLOUR OF THE OPPOSITE EDGE.** -/
theorem edgeCol_leaf {n k : ℕ} (g : Cfg n k) : edgeCol g (s(cfgP g, cfgQ g)) = cfgJ g :=
  by rw [edgeCol, if_pos rfl]

/-- **ANY OTHER EDGE GETS THE COLOUR AT THE CENTRE.** -/
theorem edgeCol_long {n k : ℕ} {g : Cfg n k} {e : Sym2 (Verts n)} (hne : e ≠ s(cfgP g, cfgQ g)) :
    edgeCol g e = cfgI g := by rw [edgeCol, if_neg hne]

/-- **THE ACCOUNTING OF A SINGLE CONFIGURATION.**  Every endpoint of an edge of a configuration
uses the `(vertex, colour)` slot of that edge's colour: this is why a *matching* in the auxiliary
hypergraph controls a *colouring*. -/
theorem mem_cfgSlots_end {n k : ℕ} {g : Cfg n k} (h : Ok g) {e : Sym2 (Verts n)} {x : Verts n}
    (he : e ∈ cfgEdges g) (hx : x ∈ e) : (x, edgeCol g e) ∈ cfgSlots g := by
  rcases mem_cfgEdges g |>.mp he with h1 | h1 | h1
  · rw [h1] at hx
    rw [h1, edgeCol_long (ne_edges h |>.2.1)]
    rcases Sym2.mem_iff.mp hx with hx' | hx'
    · rw [hx']; exact mem_cfgSlots_1 g
    · rw [hx']; exact mem_cfgSlots_2 g
  · rw [h1] at hx
    rw [h1, edgeCol_long (ne_edges h |>.2.2)]
    rcases Sym2.mem_iff.mp hx with hx' | hx'
    · rw [hx']; exact mem_cfgSlots_1 g
    · rw [hx']; exact mem_cfgSlots_3 g
  · rw [h1] at hx
    rw [h1, edgeCol_leaf g]
    rcases Sym2.mem_iff.mp hx with hx' | hx'
    · rw [hx']; exact mem_cfgSlots_4 g
    · rw [hx']; exact mem_cfgSlots_5 g

/-- **TWO EDGES OF A CONFIGURATION WITH THE SAME COLOUR ARE THE TWO EDGES AT ITS CENTRE.**  So a
configuration has exactly one pair of edges sharing a colour, and their common vertex is the
centre. -/
theorem eq_long_of_same {n k : ℕ} {g : Cfg n k} (h : Ok g) {e e' : Sym2 (Verts n)}
    (he : e ∈ cfgEdges g) (he' : e' ∈ cfgEdges g) (hne : e ≠ e')
    (hc : edgeCol g e = edgeCol g e') :
    (e = s(cfgU g, cfgP g) ∧ e' = s(cfgU g, cfgQ g)) ∨
      (e = s(cfgU g, cfgQ g) ∧ e' = s(cfgU g, cfgP g)) := by
  have hne13 : s(cfgU g, cfgP g) ≠ s(cfgP g, cfgQ g) := (ne_edges h).2.1
  have hne23 : s(cfgU g, cfgQ g) ≠ s(cfgP g, cfgQ g) := (ne_edges h).2.2
  rcases mem_cfgEdges g |>.mp he with h1 | h1 | h1
  · rcases mem_cfgEdges g |>.mp he' with h1' | h1' | h1'
    · exact absurd (h1'.trans h1.symm) hne.symm
    · exact Or.inl ⟨h1, h1'⟩
    · rw [h1, h1'] at hc
      rw [edgeCol_leaf g, edgeCol_long hne13] at hc
      exact absurd hc h.2.2.2
  · rcases mem_cfgEdges g |>.mp he' with h1' | h1' | h1'
    · exact Or.inr ⟨h1, h1'⟩
    · exact absurd (h1'.trans h1.symm) hne.symm
    · rw [h1, h1'] at hc
      rw [edgeCol_leaf g, edgeCol_long hne23] at hc
      exact absurd hc h.2.2.2
  · rcases mem_cfgEdges g |>.mp he' with h1' | h1' | h1'
    · rw [h1, h1'] at hc
      rw [edgeCol_leaf g, edgeCol_long hne13] at hc
      exact absurd hc h.2.2.2.symm
    · rw [h1, h1'] at hc
      rw [edgeCol_leaf g, edgeCol_long hne23] at hc
      exact absurd hc h.2.2.2.symm
    · exact absurd (h1'.trans h1.symm) hne.symm

/-! ### 2. Families: matchings in the auxiliary hypergraph -/

/-- **A FAMILY OF CONFIGURATIONS** — a finite set of hyperedges of the auxiliary hypergraph
`H ⊆ ⨆ (V × [k])` of arXiv:2208.12563 §4. -/
abbrev Fam (n k : ℕ) := Finset (Cfg n k)

/-- Every member of the family is well formed. -/
def OkF {n k : ℕ} (F : Fam n k) : Prop := ∀ (g : Cfg n k), g ∈ F → Ok g

/-- **THE MATCHING CONDITION ON EDGES:** two members never share an edge, i.e. the triangles of the
family form a *linear* system — the partial Steiner triple system of arXiv:2207.02920 Phase 1. -/
def LinF {n k : ℕ} (F : Fam n k) : Prop :=
  ∀ (g g' : Cfg n k), g ∈ F → g' ∈ F →
    ∀ e : Sym2 (Verts n), e ∈ cfgEdges g → e ∈ cfgEdges g' → g = g'

/-- **THE MATCHING CONDITION ON SLOTS:** two distinct members use disjoint sets of
`(vertex, colour)` pairs, i.e. the members of `F` form a matching in `H`.  This is `PairFree`,
but as a condition on *data*. -/
def SlotFree {n k : ℕ} (F : Fam n k) : Prop :=
  ∀ (g g' : Cfg n k), g ∈ F → g' ∈ F →
    ∀ vp : Verts n × Fin k, vp ∈ cfgSlots g → vp ∈ cfgSlots g' → g = g'

/-- **THE EDGES COVERED BY A FAMILY.** -/
noncomputable def coveredF {n k : ℕ} (F : Fam n k) : Finset (Sym2 (Verts n)) := F.biUnion cfgEdges

/-- **THE LEFTOVER OF A FAMILY**: the edges of `K_n` no member covers.  The second stage of
arXiv:2207.02920 colours these. -/
noncomputable def leftoverF {n k : ℕ} (F : Fam n k) : Finset (Sym2 (Verts n)) :=
  (edgeFinset (Finset.univ : Finset (Verts n))) \ coveredF F

@[simp] theorem mem_coveredF {n k : ℕ} {F : Fam n k} {e : Sym2 (Verts n)} :
    e ∈ coveredF F ↔ ∃ g ∈ F, e ∈ cfgEdges g := Finset.mem_biUnion

theorem mem_leftoverF {n k : ℕ} {F : Fam n k} {e : Sym2 (Verts n)} :
    e ∈ leftoverF F ↔ e ∈ edgeFinset (Finset.univ : Finset (Verts n)) ∧ e ∉ coveredF F :=
  Finset.mem_sdiff

/-- The covered edges are edges of `K_n`. -/
theorem coveredF_subset {n k : ℕ} {F : Fam n k} (hok : OkF F) :
    coveredF F ⊆ edgeFinset (Finset.univ : Finset (Verts n)) := by
  intro e he
  obtain ⟨g, hg, he'⟩ := mem_coveredF.mp he
  have hd := Ok_def (hok g hg)
  rcases mem_cfgEdges g |>.mp he' with h1 | h1 | h1
  · rw [h1]
    exact mem_edgeFinset_mk (Finset.mem_univ _) (Finset.mem_univ _) hd.1
  · rw [h1]
    exact mem_edgeFinset_mk (Finset.mem_univ _) (Finset.mem_univ _) hd.2.1
  · rw [h1]
    exact mem_edgeFinset_mk (Finset.mem_univ _) (Finset.mem_univ _) hd.2.2.1

theorem coveredF_eq_univ {n k : ℕ} {F : Fam n k} (hok : OkF F) (hc : (leftoverF F) = ∅) :
    coveredF F = edgeFinset (Finset.univ : Finset (Verts n)) := by
  refine Finset.Subset.antisymm (coveredF_subset hok) ?_
  intro e he
  by_contra hn
  have hne : e ∈ leftoverF F := mem_leftoverF.mpr ⟨he, hn⟩
  rw [hc] at hne
  exact absurd hne (by simp)

theorem mem_coveredF_of_leftover {n k : ℕ} {F : Fam n k} (hok : OkF F) (hc : (leftoverF F) = ∅)
    {e : Sym2 (Verts n)} (he : e ∈ edgeFinset (Finset.univ : Finset (Verts n))) :
    e ∈ coveredF F := by
  have h := coveredF_eq_univ hok hc
  rw [h]
  exact he

/-! ### 3. The slot counting, in the world of matchings -/

/-- The slots used by a family. -/
noncomputable def SlotsF {n k : ℕ} (F : Fam n k) : Finset (Verts n × Fin k) := F.biUnion cfgSlots

/-- **THE SLOTS OF A FAMILY ARE `5 · |F|` IN NUMBER.** -/
theorem card_SlotsF {n k : ℕ} {F : Fam n k} (hok : OkF F) (hS : SlotFree F) :
    (SlotsF F).card = 5 * F.card := by
  calc (SlotsF F).card = ∑ g ∈ F, (cfgSlots g).card := by
        rw [SlotsF, Finset.card_biUnion (fun a ha b hb hab => by
              refine Finset.disjoint_left.2 ?_
              intro x hxa hxb
              exact hab (hS a b ha hb x hxa hxb))]
    _ = ∑ _g ∈ F, 5 := Finset.sum_congr rfl (fun g hg => card_cfgSlots (hok g hg))
    _ = 5 * F.card := by rw [Finset.sum_const]; norm_num [Nat.mul_comm]

/-- **THE SLOT COUNTING — `5 · |F| ≤ n · k`, with no colouring anywhere.** -/
theorem slots_countF {n k : ℕ} {F : Fam n k} (hok : OkF F) (hS : SlotFree F) : 5 * F.card ≤ n * k := by
  have h1 := card_SlotsF hok hS
  have h2 : (SlotsF F).card ≤ (Finset.univ : Finset (Verts n × Fin k)).card :=
    Finset.card_le_card fun vp _ => Finset.mem_univ vp
  have h3 : ((Finset.univ : Finset (Verts n × Fin k)).card) = n * k := by
    rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
  omega

/-- **THE EDGES COVERED BY A FAMILY ARE `3 · |F|` IN NUMBER.** -/
theorem card_coveredF {n k : ℕ} {F : Fam n k} (hok : OkF F) (hL : LinF F) :
    (coveredF F).card = 3 * F.card := by
  calc (coveredF F).card = ∑ g ∈ F, (cfgEdges g).card := by
        rw [coveredF, Finset.card_biUnion (fun a ha b hb hab => by
              refine Finset.disjoint_left.2 ?_
              intro e hea heb
              exact hab (hL a b ha hb e hea heb))]
    _ = ∑ _g ∈ F, 3 := Finset.sum_congr rfl (fun g hg => card_cfgEdges (hok g hg))
    _ = 3 * F.card := by rw [Finset.sum_const]; norm_num [Nat.mul_comm]

/-- **THE EXACT ACCOUNTING OF A FIRST STAGE, `C(n,2) = 3·|F| + |leftoverF F|`.** -/
theorem edgeCoverF {n k : ℕ} {F : Fam n k} (hok : OkF F) (hL : LinF F) :
    (edgeFinset (Finset.univ : Finset (Verts n))).card = 3 * F.card + (leftoverF F).card := by
  have hcardF : (coveredF F).card = 3 * F.card := card_coveredF hok hL
  have hLsub : leftoverF F ⊆ edgeFinset (Finset.univ : Finset (Verts n)) :=
    fun e (he : e ∈ leftoverF F) => (mem_leftoverF (e := e)).mp he |>.1
  have hdisj : coveredF F ∩ leftoverF F = ∅ := by
    refine Finset.eq_empty_iff_forall_notMem.mpr fun e he => ?_
    obtain ⟨he1, he2⟩ := Finset.mem_inter.mp he
    exact (mem_leftoverF (e := e)).mp he2 |>.2 he1
  have hunion : (edgeFinset (Finset.univ : Finset (Verts n))) = coveredF F ∪ leftoverF F := by
    refine Finset.Subset.antisymm (fun e he => ?_) (fun e he => ?_)
    · refine Finset.mem_union.mpr ?_
      by_cases hd : e ∈ coveredF F
      · exact Or.inl hd
      · exact Or.inr (mem_leftoverF.mpr ⟨he, hd⟩)
    · rcases Finset.mem_union.mp he with he | he
      · exact coveredF_subset hok he
      · exact hLsub he
  have hcardE : (edgeFinset (Finset.univ : Finset (Verts n))).card
      = (coveredF F).card + (leftoverF F).card := by
    have h := Finset.card_union_add_card_inter (s := coveredF F) (t := leftoverF F)
    rw [hdisj, Finset.card_empty, ← hunion] at h
    exact h
  omega

/-- **THE HANDSHAKING LEMMA FOR THE LEFTOVER OF A FAMILY.** -/
theorem handshakeF {n k D : ℕ} {F : Fam n k} (hD : SparseL (leftoverF F) D) :
    2 * (leftoverF F).card ≤ n * D :=
  handshake_le (fun e he => ((mem_leftoverF (F := F)).mp he).1) hD

/-- **THE SLOT COUNTING OF ROUND 36, IN THE WORLD OF MATCHINGS: `5(n-1) ≤ 6k + 5D`.**  The three
ingredients — five slots per configuration, three edges per configuration, and the handshaking
lemma for the leftover — are now statements about a *matching in the auxiliary hypergraph*, with no
colouring and no four-vertex clique anywhere in sight. -/
theorem count_lowerF {n k D : ℕ} {F : Fam n k} (hok : OkF F) (hL : LinF F) (hS : SlotFree F)
    (hD : SparseL (leftoverF F) D) : FirstStageCounting n k D := by
  have h5 : 5 * F.card ≤ n * k := slots_countF hok hS
  have h3 := edgeCoverF hok hL
  have hHS : 2 * (leftoverF F).card ≤ n * D := handshakeF hD
  have key : 10 * (edgeFinset (Finset.univ : Finset (Verts n))).card
      ≤ 6 * (n * k) + 5 * (n * D) := by
    have h6 : 30 * F.card ≤ 6 * (n * k) := by
      have h := Nat.mul_le_mul_left 6 h5
      have h' : 6 * (5 * F.card) = 30 * F.card := by ring
      rw [h'] at h
      exact h
    have h7 : 10 * (leftoverF F).card ≤ 5 * (n * D) := by
      have h := Nat.mul_le_mul_left 5 hHS
      have h' : 5 * (2 * (leftoverF F).card) = 10 * (leftoverF F).card := by ring
      rw [h'] at h
      exact h
    have h8 : 10 * (edgeFinset (Finset.univ : Finset (Verts n))).card
        = 30 * F.card + 10 * (leftoverF F).card := by
      rw [h3]
      ring
    omega
  have h10 : 10 * (edgeFinset (Finset.univ : Finset (Verts n))).card
      = 5 * (n * (n - 1)) := by
    have h11 : 10 * (edgeFinset (Finset.univ : Finset (Verts n))).card
        = 5 * (2 * (edgeFinset (Finset.univ : Finset (Verts n))).card) := by ring
    rw [h11, edge_count_two_mul n]
  rw [h10] at key
  rw [show 5 * (n * (n - 1)) = n * (5 * (n - 1)) from by ring] at key
  rw [show 6 * (n * k) + 5 * (n * D) = n * (6 * k + 5 * D) from by ring] at key
  rcases Nat.eq_zero_or_pos n with h0 | hn
  · subst h0
    show 5 * (0 - 1) ≤ 6 * k + 5 * D
    omega
  · exact Nat.le_of_mul_le_mul_left key hn

/-- **THE THREE NUMBERS OF A FIRST STAGE, AS A MATCHING.** -/
theorem first_stage_numbersF {n k D : ℕ} {F : Fam n k} (hok : OkF F) (hL : LinF F)
    (hS : SlotFree F) (hD : SparseL (leftoverF F) D) :
    5 * F.card ≤ n * k ∧
      (edgeFinset (Finset.univ : Finset (Verts n))).card = 3 * F.card + (leftoverF F).card ∧
      2 * (leftoverF F).card ≤ n * D :=
  ⟨slots_countF hok hS, edgeCoverF hok hL, handshakeF hD⟩

/-- **THE COUNTING BOUND FOR A COMPLETE FIRST STAGE: `5(n-1) ≤ 6k`.** -/
theorem count_lowerF_tight {n k : ℕ} {F : Fam n k} (hok : OkF F) (hL : LinF F) (hS : SlotFree F)
    (hc : (leftoverF F) = ∅) : FirstStageCounting n k 0 := by
  refine count_lowerF hok hL hS ?_
  intro v
  rw [DegL, hc]
  simp

/-! ### 4. The colouring induced by a matching -/

/-- **THE COLOURING INDUCED BY A FAMILY.**  Uncovered edges get colour `0`; every other edge gets
the colour the (unique, by `LinF`) configuration covering it prescribes.  A construction of the
published kind produces `F` and gets `colOf F` for free. -/
noncomputable def colOf {n k : ℕ} (F : Fam n k) (d : Fin k) : Col n k :=
  fun e => if h : ∃ g ∈ F, e ∈ cfgEdges g then edgeCol h.choose e else d

/-- **THE COLOURING OF A FAMILY AGREES WITH THE CONFIGURATION COVERING AN EDGE.** -/
theorem colOf_of_mem {n k : ℕ} {F : Fam n k} (hL : LinF F) {g : Cfg n k} (hg : g ∈ F)
    {e : Sym2 (Verts n)} (he : e ∈ cfgEdges g) (d : Fin k) : colOf F d e = edgeCol g e := by
  have key : ∀ g' ∈ F, e ∈ cfgEdges g' → g' = g := by
    intro g' hg' he'
    exact (hL g g' hg hg' e he he').symm
  unfold colOf
  by_cases hex : ∃ g' ∈ F, e ∈ cfgEdges g'
  · rw [dif_pos hex]
    have hc' : hex.choose = g := by
      apply key
      · exact hex.choose_spec.1
      · exact hex.choose_spec.2
    rw [hc']
  · exact (hex ⟨g, hg, he⟩).elim

/-- **AN UNCOVERED EDGE GETS THE DEFAULT COLOUR.** -/
theorem colOf_of_not_covered {n k : ℕ} {F : Fam n k} {e : Sym2 (Verts n)} (d : Fin k)
    (he : e ∉ coveredF F) : colOf F d e = d := by
  unfold colOf
  by_cases hex : ∃ g ∈ F, e ∈ cfgEdges g
  · exfalso
    exact he (mem_coveredF.mpr hex)
  · rw [dif_neg hex]

/-- **A MEMBER OF THE FAMILY IS A LABELLED TRIANGLE OF THE INDUCED COLOURING.** -/
theorem labTri_of_mem {n k : ℕ} {F : Fam n k} (hL : LinF F) {u p q : Verts n} {i j : Fin k}
    (hg : (u, p, q, i, j) ∈ F) (hne : u ≠ p ∧ u ≠ q ∧ p ≠ q) (hij : i ≠ j) (d : Fin k) :
    LabTri (colOf F d) u p q := by
  have hok : Ok (u, p, q, i, j) := ⟨hne.1, hne.2.1, hne.2.2, hij⟩
  have hne12 : s(u, p) ≠ s(p, q) := (ne_edges hok).2.1
  have hne13 : s(u, q) ≠ s(p, q) := (ne_edges hok).2.2
  refine ⟨hne.1, hne.2.1, hne.2.2, ?_, ?_⟩
  · rw [colOf_of_mem hL hg (e := s(u, p)) (mem_cfgEdges _ |>.mpr (Or.inl rfl)) d,
      colOf_of_mem hL hg (e := s(u, q)) (mem_cfgEdges _ |>.mpr (Or.inr (Or.inl rfl))) d]
    calc edgeCol (u, p, q, i, j) s(u, p) = i := edgeCol_long (g := (u, p, q, i, j)) hne12
      _ = edgeCol (u, p, q, i, j) s(u, q) := (edgeCol_long (g := (u, p, q, i, j)) hne13).symm
  · rw [colOf_of_mem hL hg (e := s(p, q)) (mem_cfgEdges _ |>.mpr (Or.inr (Or.inr rfl))) d,
      colOf_of_mem hL hg (e := s(u, p)) (mem_cfgEdges _ |>.mpr (Or.inl rfl)) d]
    intro h
    have hh : j = i := by
      calc j = edgeCol (u, p, q, i, j) s(p, q) := (edgeCol_leaf (u, p, q, i, j)).symm
        _ = edgeCol (u, p, q, i, j) s(u, p) := h.symm
        _ = i := edgeCol_long hne12
    exact hij hh.symm

/-- **A MEMBER OF THE FAMILY, IN ACCESSOR FORM.** -/
theorem labTri_of_mem' {n k : ℕ} {F : Fam n k} (hL : LinF F) {g : Cfg n k} (hg : g ∈ F)
    (h : Ok g) (d : Fin k) : LabTri (colOf F d) (cfgU g) (cfgP g) (cfgQ g) := by
  obtain ⟨u, p, q, i, j⟩ := g
  simp only [cfgU, cfgP, cfgQ] at h ⊢
  obtain ⟨h1, h2, h3, h4⟩ := Ok_tuple.mp h
  exact labTri_of_mem hL hg ⟨h1, h2, h3⟩ h4 d

/-- **THE FIVE SLOTS OF A LABELLED TRIANGLE ARE THE SLOTS OF THE CONFIGURATION.** -/
theorem triPairs_eq_cfgSlots {n k : ℕ} {c : Col n k} {u p q : Verts n} {i j : Fin k}
    (hi : c s(u, p) = i) (hj : c s(p, q) = j) :
    triPairs c u p q = cfgSlots (u, p, q, i, j) := by
  simp only [triPairs, cfgSlots, cfgU, cfgP, cfgQ, cfgI, cfgJ]
  rw [hi, hj]

theorem triEdges_eq_cfgEdges {n k : ℕ} (g : Cfg n k) (c : Col n k) :
    triEdges c (cfgU g) (cfgP g) (cfgQ g) = cfgEdges g := by
  simp only [triEdges, cfgEdges, cfgU, cfgP, cfgQ]

/-- **A FAMILY COVERING ALL OF `E(K_n)` COVERS THE COLOURING.** -/
theorem covers_colOf {n k : ℕ} {F : Fam n k} (hok : OkF F) (hL : LinF F) (hc : (leftoverF F) = ∅)
    (d : Fin k) : Covers (colOf F d) := by
  intro e he
  obtain ⟨a, b, rfl⟩ := Sym2.exists.mp ⟨e, rfl⟩
  have hab : a ≠ b := offDiag_iff.mp he
  have heE : s(a, b) ∈ edgeFinset (Finset.univ : Finset (Verts n)) :=
    mem_edgeFinset_mk (Finset.mem_univ _) (Finset.mem_univ _) hab
  obtain ⟨g, hg, he'⟩ := mem_coveredF.mp (mem_coveredF_of_leftover hok hc heE)
  refine ⟨cfgU g, cfgP g, cfgQ g, ?_, ?_⟩
  · exact labTri_of_mem' hL hg (hok g hg) d
  · rw [triEdges_eq_cfgEdges]
    exact he'

/-- **TWO EDGES AT THE CENTRE DETERMINE THE CONFIGURATION.** -/
theorem eq_of_two_long {n : ℕ} {a b c : Verts n} {u p q : Verts n}
    (h : a ≠ b) (h' : a ≠ c) (h'' : b ≠ c) (hne : u ≠ p) (hne' : u ≠ q)
    (h1 : s(u, p) = s(a, b)) (h2 : s(u, q) = s(a, c)) : u = a ∧ p = b ∧ q = c := by
  have huA : u ∈ s(a, b) := by rw [← h1]; exact Sym2.mem_mk_left u p
  have huB : u ∈ s(a, c) := by rw [← h2]; exact Sym2.mem_mk_left u q
  have hpM : p ∈ s(a, b) := by rw [← h1]; exact Sym2.mem_mk_right u p
  have hqM : q ∈ s(a, c) := by rw [← h2]; exact Sym2.mem_mk_right u q
  rw [Sym2.mem_iff] at huA huB hpM hqM
  have hu : u = a := by
    rcases huA with huA | huA
    · exact huA
    · rcases huB with huB | huB
      · exact absurd (huA.symm.trans huB).symm h
      · exact absurd (huA.symm.trans huB) h''
  have hp : p = b := by
    rcases hpM with hpM | hpM
    · exact absurd (hu.trans hpM.symm) hne
    · exact hpM
  have hq : q = c := by
    rcases hqM with hqM | hqM
    · exact absurd (hu.trans hqM.symm) hne'
    · exact hqM
  exact ⟨hu, hp, hq⟩

/-- **EVERY LABELLED TRIANGLE OF THE INDUCED COLOURING IS A MEMBER OF THE FAMILY.**  This is the
converse of `labTri_of_mem`, and the reason `PairFree (colOf F)` is a theorem rather than an
accident. -/
theorem mem_or_mem_swap_of_labTri {n k : ℕ} {F : Fam n k} (hok : OkF F) (hL : LinF F)
    (hS : SlotFree F) (hc : (leftoverF F) = ∅) {u p q : Verts n} {d : Fin k}
    (h : LabTri (colOf F d) u p q) :
    (u, p, q, (colOf F d) s(u, p), (colOf F d) s(p, q)) ∈ F ∨
      (u, q, p, (colOf F d) s(u, p), (colOf F d) s(p, q)) ∈ F := by
  obtain ⟨huq, hineq⟩ : (colOf F d) s(u, q) = (colOf F d) s(u, p) ∧
      (colOf F d) s(u, p) ≠ (colOf F d) s(p, q) := ⟨h.2.2.2.1.symm, h.2.2.2.2⟩
  have hcov : ∀ e : Sym2 (Verts n), OffDiag e → ∃ g ∈ F, e ∈ cfgEdges g := by
    intro e he
    obtain ⟨a, b, rfl⟩ := Sym2.exists.mp ⟨e, rfl⟩
    obtain ⟨g, hg, he'⟩ := mem_coveredF.mp (mem_coveredF_of_leftover hok hc
      (mem_edgeFinset_mk (Finset.mem_univ _) (Finset.mem_univ _) (offDiag_iff.mp he)))
    exact ⟨g, hg, he'⟩
  obtain ⟨g₁, hg₁, he₁⟩ := hcov s(u, p) (offDiag_iff.mpr h.1)
  obtain ⟨g₂, hg₂, he₂⟩ := hcov s(u, q) (offDiag_iff.mpr h.2.1)
  have hslot₁ : (u, (colOf F d) s(u, p)) ∈ cfgSlots g₁ := by
    rw [colOf_of_mem hL hg₁ he₁ d]
    exact mem_cfgSlots_end (hok g₁ hg₁) he₁ (Sym2.mem_mk_left u p)
  have hslot₂ : (u, (colOf F d) s(u, q)) ∈ cfgSlots g₂ := by
    rw [colOf_of_mem hL hg₂ he₂ d]
    exact mem_cfgSlots_end (hok g₂ hg₂) he₂ (Sym2.mem_mk_left u q)
  rw [huq] at hslot₂
  have h12 : g₁ = g₂ := hS g₁ g₂ hg₁ hg₂ (u, (colOf F d) s(u, p)) hslot₁ hslot₂
  subst h12
  have hcol : edgeCol g₁ s(u, p) = edgeCol g₁ s(u, q) := by
    rw [← colOf_of_mem hL hg₁ he₁ d, ← colOf_of_mem hL hg₂ he₂ d, huq]
  have hne : s(u, p) ≠ s(u, q) := fun hx => h.2.2.1 (sym2_inj_right hx)
  rcases eq_long_of_same (hok g₁ hg₁) he₁ he₂ hne hcol with ⟨h1, h1'⟩ | ⟨h1, h1'⟩
  · obtain ⟨a, b, c, i₁, j₁⟩ := g₁
    simp only [cfgU, cfgP, cfgQ, cfgI, cfgJ] at he₁ h1 h1' hcol ⊢
    obtain ⟨hAb, hAc, hBc, hij⟩ := Ok_tuple.mp (hok (a, b, c, i₁, j₁) hg₁)
    have hne1 : s(a, b) ≠ s(b, c) := by
      intro hx
      have hxb : a ∈ s(b, c) := by
        have hxa : a ∈ s(a, b) := Sym2.mem_mk_left a b
        rw [hx] at hxa
        exact hxa
      rw [Sym2.mem_iff] at hxb
      rcases hxb with hxb | hxb
      · exact hAb hxb
      · exact hAc hxb
    have hne2 : s(a, c) ≠ s(b, c) := by
      intro hx
      have hxc : a ∈ s(b, c) := by
        have hxa : a ∈ s(a, c) := Sym2.mem_mk_left a c
        rw [hx] at hxa
        exact hxa
      rw [Sym2.mem_iff] at hxc
      rcases hxc with hxc | hxc
      · exact hAb hxc
      · exact hAc hxc
    obtain ⟨hu, hp, hq⟩ := eq_of_two_long hAb hAc hBc h.1 h.2.1 h1 h1'
    have hi : (colOf F d) s(a, b) = i₁ := by
      rw [colOf_of_mem hL hg₁ (e := s(a, b)) ((mem_cfgEdges (a, b, c, i₁, j₁)).mpr (Or.inl rfl)) d]
      simp [edgeCol, hne1, cfgI, cfgJ, cfgP, cfgQ, cfgU]
    have hj : (colOf F d) s(b, c) = j₁ := by
      rw [colOf_of_mem hL hg₁ (e := s(b, c)) ((mem_cfgEdges (a, b, c, i₁, j₁)).mpr (Or.inr (Or.inr rfl))) d]
      simp [edgeCol, Sym2.eq_swap, cfgJ, cfgP, cfgQ]
    rw [hu, hp, hq, hi, hj]
    exact Or.inl hg₁
  · obtain ⟨a, b, c, i₁, j₁⟩ := g₁
    simp only [cfgU, cfgP, cfgQ, cfgI, cfgJ] at he₁ h1 h1' hcol ⊢
    obtain ⟨hAb, hAc, hBc, hij⟩ := Ok_tuple.mp (hok (a, b, c, i₁, j₁) hg₁)
    have hne1 : s(a, b) ≠ s(b, c) := by
      intro hx
      have hxb : a ∈ s(b, c) := by
        have hxa : a ∈ s(a, b) := Sym2.mem_mk_left a b
        rw [hx] at hxa
        exact hxa
      rw [Sym2.mem_iff] at hxb
      rcases hxb with hxb | hxb
      · exact hAb hxb
      · exact hAc hxb
    have hne2 : s(a, c) ≠ s(b, c) := by
      intro hx
      have hxc : a ∈ s(b, c) := by
        have hxa : a ∈ s(a, c) := Sym2.mem_mk_left a c
        rw [hx] at hxa
        exact hxa
      rw [Sym2.mem_iff] at hxc
      rcases hxc with hxc | hxc
      · exact hAb hxc
      · exact hAc hxc
    obtain ⟨hu, hp, hq⟩ := eq_of_two_long hAb hAc hBc h.2.1 h.1 h1' h1
    have hi : (colOf F d) s(a, c) = i₁ := by
      rw [colOf_of_mem hL hg₁ (e := s(a, c)) ((mem_cfgEdges (a, b, c, i₁, j₁)).mpr (Or.inr (Or.inl rfl))) d]
      simp [edgeCol, hne2, cfgI, cfgJ, cfgP, cfgQ, cfgU]
    have hj : (colOf F d) s(c, b) = j₁ := by
      rw [colOf_of_mem hL hg₁ (e := s(c, b))
        ((mem_cfgEdges (a, b, c, i₁, j₁)).mpr
          (Or.inr (Or.inr (by simp [Sym2.eq_swap, cfgP, cfgQ])))) d]
      simp [edgeCol, Sym2.eq_swap, cfgJ, cfgP, cfgQ]
    rw [hu, hq, hp, hi, hj]
    exact Or.inr hg₁

/-- The vertex set of a configuration is the vertex set of its centre and its two leaves. -/
theorem cfgVerts_eq_triVerts {n k : ℕ} (g : Cfg n k) :
    cfgVerts g = triVerts (cfgU g) (cfgP g) (cfgQ g) := by simp only [cfgVerts, triVerts]

/-- Swapping the leaves does not change the vertex set of a triangle. -/
theorem triVerts_swap {n : ℕ} {u p q : Verts n} : triVerts u p q = triVerts u q p := by
  ext x
  simp only [mem_triVerts]
  tauto

/-- **THE SLOTS AND THE VERTEX SET OF A LABELLED TRIANGLE COME FROM ONE MEMBER OF THE FAMILY.** -/
theorem mem_or_mem_swap_of_labTri' {n k : ℕ} {F : Fam n k} (hok : OkF F) (hL : LinF F)
    (hS : SlotFree F) (hc : (leftoverF F) = ∅) {u p q : Verts n} {d : Fin k}
    (h : LabTri (colOf F d) u p q) :
    ∃ g ∈ F, triVerts u p q = cfgVerts g ∧ triPairs (colOf F d) u p q = cfgSlots g := by
  obtain (hgE | hgE) := mem_or_mem_swap_of_labTri hok hL hS hc h
  · refine ⟨(u, p, q, (colOf F d) s(u, p), (colOf F d) s(p, q)), hgE, ?_, ?_⟩
    · exact (cfgVerts_eq_triVerts
        (u, p, q, (colOf F d) s(u, p), (colOf F d) s(p, q))).symm
    · exact triPairs_eq_cfgSlots rfl rfl
  · refine ⟨(u, q, p, (colOf F d) s(u, p), (colOf F d) s(p, q)), hgE, ?_, ?_⟩
    · ext x
      simp only [mem_triVerts, cfgVerts, cfgU, cfgP, cfgQ]
      tauto
    · rw [triPairs_eq_cfgSlots rfl rfl, cfgSlots_swap]


/-- **A MATCHING IS PAIR-FREE AS A COLOURING.**  Together with `covers_colOf` this is the whole
content of the encoding: a set of configurations covering `E(K_n)` and using disjoint slots *is* a
labelled-triangle system in the sense of `Triangles.lean`. -/
theorem pairFree_colOf {n k : ℕ} {F : Fam n k} (hok : OkF F) (hL : LinF F) (hS : SlotFree F)
    (hc : (leftoverF F) = ∅) (d : Fin k) : PairFree (colOf F d) := by
  intro u p q u' p' q' h1 h2 hvv
  obtain ⟨g, hg, hV1, hT1⟩ := mem_or_mem_swap_of_labTri' hok hL hS hc h1
  obtain ⟨g', hg', hV2, hT2⟩ := mem_or_mem_swap_of_labTri' hok hL hS hc h2
  rw [hT1, hT2]
  refine Finset.eq_empty_iff_forall_notMem.mpr ?_
  intro x hx
  obtain ⟨hx1, hx2⟩ := Finset.mem_inter.mp hx
  by_cases he : g = g'
  · exfalso
    exact hvv (calc triVerts u p q = cfgVerts g := hV1
      _ = cfgVerts g' := by rw [he]
      _ = triVerts u' p' q' := hV2.symm)
  · exact absurd (hS g g' hg hg' x hx1 hx2) he

/-- **THE PUBLISHED CONSTRUCTION, IN THE FORM A CONSTRUCTION PRODUCES IT.**  For every `δ > 0` and
all large `m ≡ 1 (mod 6)` there is a *matching* `F` in the auxiliary hypergraph of arXiv:2208.12563
§4 — configurations on `k` colours, pairwise edge-disjoint and slot-disjoint, covering all of
`E(K_m)` — whose induced colouring has neither a bad nor a crossing four-set and which uses at most
`5(m-1)/6 + δm/6` colours.  **No colouring is quantified over**: `F` is a finset of configurations,
i.e. a finite combinatorial object, so the hypothesis is checkable. -/
def FamFamily : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ M : ℕ, ∀ m : ℕ, M ≤ m → m % 6 = 1 →
    ∃ (k : ℕ) (d : Fin k) (F : Fam m k),
      OkF F ∧ LinF F ∧ SlotFree F ∧ (leftoverF F) = ∅ ∧
        NoCrossFour (colOf F d) ∧ NoBadFour (colOf F d) ∧
        (6 : ℝ) * (k : ℝ) ≤ 5 * ((m - 1 : ℕ) : ℝ) + δ * (m : ℝ)

/-- **A MATCHING IN THE AUXILIARY HYPERGRAPH IS A LABELLED-TRIANGLE SYSTEM.** -/
theorem FamFamily.tri (h : FamFamily) : TriFamily := by
  intro δ hδ
  obtain ⟨M, hM⟩ := h δ hδ
  refine ⟨M, fun m hMm hm => ?_⟩
  obtain ⟨k, d, F, hok, hL, hS, h0, hX, hB, hk⟩ := hM m hMm hm
  exact ⟨k, colOf F d, covers_colOf hok hL h0 d, pairFree_colOf hok hL hS h0 d, hX, hB, hk⟩

/-- **THE REQUIRED THEOREM `jsp_000140_main`, REDUCED TO THE EXISTENCE OF A MATCHING IN THE
AUXILIARY HYPERGRAPH.**  No colouring occurs in the hypothesis: what is left of the catalog problem
is the existence, for every `δ > 0` and all large `m ≡ 1 (mod 6)`, of a matching in the auxiliary
hypergraph `H ⊆ ⨆ (V × [k])` of arXiv:2208.12563 §4 / arXiv:2207.02920 Phase 1 with

* every edge of `K_m` covered,
* the five slots of two configurations disjoint, the three edges of two configurations disjoint,
* no bad and no crossing four-set in the induced colouring,
* at most `5(m-1)/6 + δm/6` colours. -/
theorem jsp_000140_main_of_fam_family (h : FamFamily) : jsp_000140_target :=
  jsp_000140_main_of_tri_family h.tri


/-! ### 5. The centre balance of a family -/

/-- **THE CENTRES OF A FAMILY**: the members centred at `v`. -/
noncomputable def centF {n k : ℕ} (F : Fam n k) (v : Verts n) : Finset (Cfg n k) :=
  F.filter (fun g => cfgU g = v)

/-- **THE LEAVES OF A FAMILY**: the members having `v` as one of their two leaves. -/
noncomputable def leafF {n k : ℕ} (F : Fam n k) (v : Verts n) : Finset (Cfg n k) :=
  F.filter (fun g => cfgP g = v ∨ cfgQ g = v)

/-- **THE CONFIGURATIONS PASSING THROUGH A VERTEX.** -/
noncomputable def throughF {n k : ℕ} (F : Fam n k) (v : Verts n) : Finset (Cfg n k) :=
  F.filter (fun g => v ∈ cfgVerts g)

@[simp] theorem mem_centF {n k : ℕ} {F : Fam n k} {v : Verts n} {g : Cfg n k} :
    g ∈ centF F v ↔ g ∈ F ∧ cfgU g = v := Finset.mem_filter

@[simp] theorem mem_leafF {n k : ℕ} {F : Fam n k} {v : Verts n} {g : Cfg n k} :
    g ∈ leafF F v ↔ g ∈ F ∧ (cfgP g = v ∨ cfgQ g = v) := Finset.mem_filter

@[simp] theorem mem_throughF {n k : ℕ} {F : Fam n k} {v : Verts n} {g : Cfg n k} :
    g ∈ throughF F v ↔ g ∈ F ∧ v ∈ cfgVerts g := Finset.mem_filter

@[simp] theorem mem_cfgVerts {n k : ℕ} (g : Cfg n k) {v : Verts n} :
    v ∈ cfgVerts g ↔ v = cfgU g ∨ v = cfgP g ∨ v = cfgQ g := by
  simp only [cfgVerts, mem_triVerts]

/-- A pair is the pair of its components. -/
theorem prod_eta {α β : Type*} (x : α × β) : x = (x.1, x.2) := by
  cases x
  rfl

/-- Membership in `cfgSlots` may be tested on the two components. -/
theorem mem_cfgSlots_prod {n k : ℕ} (g : Cfg n k) {x : Verts n × Fin k} :
    x ∈ cfgSlots g ↔ (x.1, x.2) ∈ cfgSlots g := by
  have key : x = (x.1, x.2) := by
    cases x
    rfl
  constructor
  · intro hx
    rw [key] at hx
    exact hx
  · intro hx
    rw [← key] at hx
    exact hx

/-- **THE FIVE SLOTS OF A CONFIGURATION, AS FIVE WHOLE ELEMENTS.** -/
theorem mem_cfgSlots_cases' {n k : ℕ} (g : Cfg n k) {a : Verts n} {j : Fin k}
    (hx : (a, j) ∈ cfgSlots g) :
    (a, j) = (cfgU g, cfgI g) ∨ (a, j) = (cfgP g, cfgI g) ∨ (a, j) = (cfgQ g, cfgI g) ∨
      (a, j) = (cfgP g, cfgJ g) ∨ (a, j) = (cfgQ g, cfgJ g) := by
  rcases (mem_cfgSlots g).mp hx with ⟨hj, ha | ha | ha⟩ | ⟨hj, ha | ha⟩
  · exact Or.inl (Prod.ext ha hj)
  · exact Or.inr (Or.inl (Prod.ext ha hj))
  · exact Or.inr (Or.inr (Or.inl (Prod.ext ha hj)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (Prod.ext ha hj))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Prod.ext ha hj))))

/-- **THE SLOTS A CONFIGURATION USES AT ONE VERTEX.** -/
noncomputable def slotsAt {n k : ℕ} (g : Cfg n k) (v : Verts n) : Finset (Verts n × Fin k) :=
  (cfgSlots g).filter (fun vp => vp.1 = v)

/-- At the centre a configuration uses exactly ONE slot. -/
theorem slotsAt_centre {n k : ℕ} {g : Cfg n k} {v : Verts n} (h : Ok g) (hv : v = cfgU g) :
    slotsAt g v = {(cfgU g, cfgI g)} := by
  ext x
  simp only [slotsAt, Finset.mem_filter, Finset.mem_singleton]
  constructor
  · rintro ⟨hx, hx1⟩
    rcases mem_cfgSlots_cases' g ((mem_cfgSlots_prod g).mp hx) with hE | hE | hE | hE | hE
    · exact (prod_eta x).symm.trans hE
    · have hB : v = cfgP g := hx1.symm.trans (congrArg Prod.fst hE)
      exact absurd hB (fun hq => h.1 (hq.symm.trans hv).symm)
    · have hB : v = cfgQ g := hx1.symm.trans (congrArg Prod.fst hE)
      exact absurd hB (fun hq => h.2.1 (hq.symm.trans hv).symm)
    · have hB : v = cfgP g := hx1.symm.trans (congrArg Prod.fst hE)
      exact absurd hB (fun hq => h.1 (hq.symm.trans hv).symm)
    · have hB : v = cfgQ g := hx1.symm.trans (congrArg Prod.fst hE)
      exact absurd hB (fun hq => h.2.1 (hq.symm.trans hv).symm)
  · intro hx
    exact ⟨hx ▸ mem_cfgSlots_1 g, (congrArg Prod.fst hx).trans hv.symm⟩

/-- At a leaf a configuration uses exactly TWO slots: `(v, i)` and `(v, j)`. -/
theorem slotsAt_leaf {n k : ℕ} {g : Cfg n k} {v : Verts n} (h : Ok g) (hv : v = cfgP g) :
    slotsAt g v = {(cfgP g, cfgI g), (cfgP g, cfgJ g)} := by
  ext x
  simp only [slotsAt, Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hx, hx1⟩
    rcases mem_cfgSlots_cases' g ((mem_cfgSlots_prod g).mp hx) with hE | hE | hE | hE | hE
    · have hA : v = cfgU g := hx1.symm.trans (congrArg Prod.fst hE)
      exact absurd hA (fun hq => h.1 (hq.symm.trans hv))
    · exact Or.inl ((prod_eta x).symm.trans hE)
    · have hB : v = cfgQ g := hx1.symm.trans (congrArg Prod.fst hE)
      exact absurd hB (fun hq => h.2.2.1 (hq.symm.trans hv).symm)
    · exact Or.inr ((prod_eta x).symm.trans hE)
    · have hB : v = cfgQ g := hx1.symm.trans (congrArg Prod.fst hE)
      exact absurd hB (fun hq => h.2.2.1 (hq.symm.trans hv).symm)
  · intro hx
    rcases hx with hx | hx
    · exact ⟨hx ▸ mem_cfgSlots_2 g, (congrArg Prod.fst hx).trans hv.symm⟩
    · exact ⟨hx ▸ mem_cfgSlots_4 g, (congrArg Prod.fst hx).trans hv.symm⟩

/-- The same for the second leaf. -/
theorem slotsAt_leaf' {n k : ℕ} {g : Cfg n k} {v : Verts n} (h : Ok g) (hv : v = cfgQ g) :
    slotsAt g v = {(cfgQ g, cfgI g), (cfgQ g, cfgJ g)} := by
  ext x
  simp only [slotsAt, Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hx, hx1⟩
    rcases mem_cfgSlots_cases' g ((mem_cfgSlots_prod g).mp hx) with hE | hE | hE | hE | hE
    · have hA : v = cfgU g := hx1.symm.trans (congrArg Prod.fst hE)
      exact absurd hA (fun hq => h.2.1 (hq.symm.trans hv))
    · have hB : v = cfgP g := hx1.symm.trans (congrArg Prod.fst hE)
      exact absurd hB (fun hq => h.2.2.1 (hq.symm.trans hv))
    · exact Or.inl ((prod_eta x).symm.trans hE)
    · have hB : v = cfgP g := hx1.symm.trans (congrArg Prod.fst hE)
      exact absurd hB (fun hq => h.2.2.1 (hq.symm.trans hv))
    · exact Or.inr ((prod_eta x).symm.trans hE)
  · intro hx
    rcases hx with hx | hx
    · exact ⟨hx ▸ mem_cfgSlots_3 g, (congrArg Prod.fst hx).trans hv.symm⟩
    · exact ⟨hx ▸ mem_cfgSlots_5 g, (congrArg Prod.fst hx).trans hv.symm⟩

/-- At every other vertex a configuration uses NO slot. -/
theorem slotsAt_ne {n k : ℕ} {g : Cfg n k} {v : Verts n} (h : Ok g)
    (h1 : v ≠ cfgU g) (h2 : v ≠ cfgP g) (h3 : v ≠ cfgQ g) : slotsAt g v = ∅ := by
  refine Finset.eq_empty_iff_forall_notMem.mpr fun x hx => ?_
  obtain ⟨hx1, hx2⟩ := Finset.mem_filter.mp hx
  rcases mem_cfgSlots_cases' g ((mem_cfgSlots_prod g).mp hx1) with hE | hE | hE | hE | hE
  · exact h1 (hx2.symm.trans (congrArg Prod.fst hE))
  · exact h2 (hx2.symm.trans (congrArg Prod.fst hE))
  · exact h3 (hx2.symm.trans (congrArg Prod.fst hE))
  · exact h2 (hx2.symm.trans (congrArg Prod.fst hE))
  · exact h3 (hx2.symm.trans (congrArg Prod.fst hE))

/-- **ONE SLOT AT THE CENTRE, TWO AT EACH LEAF, NONE ELSEWHERE.** -/
theorem card_slotsAt {n k : ℕ} {g : Cfg n k} (h : Ok g) (v : Verts n) :
    (slotsAt g v).card = if v = cfgU g then 1 else if v = cfgP g ∨ v = cfgQ g then 2 else 0 := by
  by_cases h1 : v = cfgU g
  · rw [slotsAt_centre h h1, Finset.card_singleton, if_pos h1]
  · by_cases h2 : v = cfgP g
    · rw [slotsAt_leaf h h2, if_neg h1, if_pos (Or.inl h2)]
      simp [h.2.2.2]
    · by_cases h3 : v = cfgQ g
      · rw [slotsAt_leaf' h h3, if_neg h1, if_pos (Or.inr h3)]
        simp [h.2.2.2]
      · rw [slotsAt_ne h h1 h2 h3, Finset.card_empty, if_neg h1, if_neg (fun hh => hh.elim h2 h3)]

/-- **THE SLOTS A FAMILY USES AT ONE VERTEX.** -/
noncomputable def slotsF {n k : ℕ} (F : Fam n k) (v : Verts n) : Finset (Verts n × Fin k) :=
  (SlotsF F).filter (fun vp => vp.1 = v)

theorem slotsF_eq {n k : ℕ} (F : Fam n k) (v : Verts n) :
    slotsF F v = F.biUnion (fun g => slotsAt g v) := by
  ext x
  constructor
  · intro hx
    have hx1 : x ∈ SlotsF F ∧ x.1 = v := Finset.mem_filter.mp hx
    obtain ⟨g, hg, hxg⟩ := Finset.mem_biUnion.mp hx1.1
    exact Finset.mem_biUnion.mpr ⟨g, hg, Finset.mem_filter.mpr ⟨hxg, hx1.2⟩⟩
  · intro hx
    obtain ⟨g, hg, hxg⟩ := Finset.mem_biUnion.mp hx
    have hxg' : x ∈ cfgSlots g ∧ x.1 = v := Finset.mem_filter.mp hxg
    exact Finset.mem_filter.mpr ⟨Finset.mem_biUnion.mpr ⟨g, hg, hxg'.1⟩, hxg'.2⟩

/-- **THE CENTRE BALANCE: the slots a family uses at `v` are one per configuration centred at `v`
and two per configuration having `v` as a leaf.**  Together with `card_SlotsF` (`5 · |F|` slots)
this is the whole slot budget of a first stage, resolved vertex by vertex. -/
theorem card_slotsF {n k : ℕ} {F : Fam n k} (hok : OkF F) (hS : SlotFree F) (v : Verts n) :
    (slotsF F v).card = (centF F v).card + 2 * (leafF F v).card := by
  have key : ∀ (g : Cfg n k) (hg : g ∈ F),
      (slotsAt g v).card = (if g ∈ centF F v then 1 else 0)
        + 2 * (if g ∈ leafF F v then 1 else 0) := by
    intro g hg
    by_cases h1 : v = cfgU g
    · have hA : g ∈ centF F v := mem_centF.mpr ⟨hg, h1.symm⟩
      have hB : g ∉ leafF F v := by
        intro hB'
        obtain ⟨-, hB'⟩ := mem_leafF.mp hB'
        rcases hB' with he | he
        · exact (hok g hg).1 (he.trans h1).symm
        · exact (hok g hg).2.1 (he.trans h1).symm
      rw [if_pos hA, if_neg hB, card_slotsAt (hok g hg) v, if_pos h1]
    · by_cases h2 : v = cfgP g ∨ v = cfgQ g
      · have hA : g ∉ centF F v := by
          intro hA'
          obtain ⟨-, he⟩ := mem_centF.mp hA'
          exact h1 he.symm
        have hB : g ∈ leafF F v := by
          rcases h2 with h2' | h2'
          · exact mem_leafF.mpr ⟨hg, Or.inl h2'.symm⟩
          · exact mem_leafF.mpr ⟨hg, Or.inr h2'.symm⟩
        rw [if_neg hA, if_pos hB, card_slotsAt (hok g hg) v, if_neg h1, if_pos h2]
      · have hA : g ∉ centF F v := by
          intro hA'
          obtain ⟨-, he⟩ := mem_centF.mp hA'
          exact h1 he.symm
        have hB : g ∉ leafF F v := by
          intro hB'
          obtain ⟨-, he⟩ := mem_leafF.mp hB'
          exact h2 (he.elim (fun x => Or.inl x.symm) (fun x => Or.inr x.symm))
        rw [if_neg hA, if_neg hB, card_slotsAt (hok g hg) v, if_neg h1, if_neg h2]
  rw [slotsF_eq F v, Finset.card_biUnion (fun a ha b hb hab => by
        refine Finset.disjoint_left.2 ?_
        intro x hxa hxb
        exact hab (hS a b ha hb x (Finset.mem_filter.mp hxa).1 (Finset.mem_filter.mp hxb).1)),
      Finset.sum_congr rfl key]
  have hffc : F.filter (fun g => g ∈ centF F v) = centF F v := by
    ext g
    simp only [Finset.mem_filter, mem_centF]
    tauto
  have hffl : F.filter (fun g => g ∈ leafF F v) = leafF F v := by
    ext g
    simp only [Finset.mem_filter, mem_leafF]
    tauto
  have hcen : ∑ g ∈ F, (if g ∈ centF F v then (1 : ℕ) else 0) = (centF F v).card := by
    have h3 : ∑ _g ∈ F.filter (fun g => g ∈ centF F v), (1 : ℕ)
        = ∑ g ∈ F, (if g ∈ centF F v then 1 else 0) :=
      Finset.sum_filter (fun g => g ∈ centF F v) (fun _ => (1 : ℕ))
    rw [← h3, ← Finset.card_eq_sum_ones, hffc]
  have hleaf : ∑ g ∈ F, 2 * (if g ∈ leafF F v then (1 : ℕ) else 0)
      = 2 * (leafF F v).card := by
    have h3 : ∑ _g ∈ F.filter (fun g => g ∈ leafF F v), (1 : ℕ)
        = ∑ g ∈ F, (if g ∈ leafF F v then 1 else 0) :=
      Finset.sum_filter (fun g => g ∈ leafF F v) (fun _ => (1 : ℕ))
    rw [← Finset.mul_sum, ← h3, ← Finset.card_eq_sum_ones, hffl]
  have hsplit : ∑ g ∈ F,
        ((if g ∈ centF F v then (1 : ℕ) else 0) + 2 * (if g ∈ leafF F v then (1 : ℕ) else 0))
      = (∑ g ∈ F, (if g ∈ centF F v then (1 : ℕ) else 0))
        + ∑ g ∈ F, (2 * (if g ∈ leafF F v then (1 : ℕ) else 0)) := Finset.sum_add_distrib
  rw [hsplit, hcen, hleaf]

/-- **A FAMILY USES AT MOST `k` SLOTS AT ANY ONE VERTEX** (the slots at `v` are pairwise distinct
`(v, colour)` pairs, by the matching condition). -/
theorem card_slotsF_le {n k : ℕ} {F : Fam n k} (v : Verts n) : (slotsF F v).card ≤ k := by
  have hsub : slotsF F v
      ⊆ (Finset.image (fun j : Fin k => (v, j)) (Finset.univ : Finset (Fin k))) := by
    intro vp hvp
    have hvp' : vp ∈ SlotsF F ∧ vp.1 = v := Finset.mem_filter.mp hvp
    refine Finset.mem_image.mpr ⟨vp.2, Finset.mem_univ _, ?_⟩
    exact Prod.ext hvp'.2.symm rfl
  calc (slotsF F v).card
      ≤ ((Finset.image (fun j : Fin k => (v, j)) (Finset.univ : Finset (Fin k))).card) :=
        Finset.card_le_card hsub
    _ = k := by
      rw [Finset.card_image_of_injective _ (fun a b hab => (Prod.ext_iff.mp hab).2),
        Finset.card_univ, Fintype.card_fin]

end JSP140
