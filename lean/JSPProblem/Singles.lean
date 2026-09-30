import JSPProblem.Extremal

/-!
# JSP-000140 — the single-edge half of the extremal structure: the leaf-edge bijection

The counting lemma of `Cherry.lean` (`3 * Paths c ≤ |E(K_n)|`) uses one third of the edges: every
two-edge path `a - v - b` of colour `i` *forces* the edge `s(a, b)` to be an **isolated single
edge** of a different colour (`Cherry.Single_of_leaf`), and the triples of edges belonging to
different two-edge paths are disjoint (`Cherry.cherryEdges_disjoint`).  Round 13 showed that in the
extremal case the two-edge paths decompose `K_n` into triangles (a Steiner triple system), and round
14 that every colour class spans the vertex set.  This file completes the description by proving
that **the single edges are exactly the leaf edges of the two-edge paths, one for each**:

* `singleFinset` — the single edges of a colouring as a finset, `mem_singleFinset`;
* `twoA_oneB_or_zero` — every vertex has colour-degree `0`, `1` or `2` in each colour;
* `single_or_center`, `mem_classIn_single_or_path` — **EVERY EDGE OF A COLOUR CLASS IS A PATH EDGE OR
  AN ISOLATED SINGLE EDGE** (the components of a colour class are two-edge paths and isolated single
  edges);
* `card_single_in_classIn` — a colour class has exactly `|E_i| - 2|A_i|` single edges;
* **`card_singleFinset` — THE IDENTITY `|E(K_n)| = 2 * Paths c + (number of single edges)`.**
  Since the single edges contain the leaf edges of the paths,
  **`paths_le_singles` — `Paths c ≤ (number of single edges)`, i.e. at least one third of the edges
  of `K_n` lie in single-edge components**, with equality `⇔` the counting lemma is an equality;
* **`tight_card_singles` — IN THE EXTREMAL CASE THE SINGLE EDGES ARE EXACTLY AS MANY AS THE TWO-EDGE
  PATHS**, `n(n-1)/6` of them, one leaf edge for each block of the Steiner triple system;
* **`tight_single_is_leaf` — AND EVERY SINGLE EDGE IS THE LEAF EDGE OF EXACTLY ONE TWO-EDGE PATH**:
  the two halves of the extremal structure are in bijection.
-/

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

namespace JSP140

variable {n k : ℕ}

/-- `Single` is decidable (it is a property of two vertices and of two finite neighbourhoods). -/
def singleDecidable (c : Col n k) (e : Sym2 (Verts n)) : Decidable (Single c e) := by
  unfold Single
  infer_instance

instance singleDecidablePred (c : Col n k) : DecidablePred (Single c) := fun e => singleDecidable c e

/-- **The single edges of a colouring**: the edges which are the only edge of their colour class at
each of their two endpoints (`Cherry.Single`). -/
def singleFinset (c : Col n k) : Finset (Sym2 (Verts n)) :=
  (edgeFinset (Finset.univ : Finset (Verts n))).filter (Single c)

theorem mem_singleFinset {c : Col n k} {e : Sym2 (Verts n)} :
    e ∈ singleFinset c ↔ e ∈ edgeFinset (Finset.univ : Finset (Verts n)) ∧ Single c e := by
  rw [singleFinset, Finset.mem_filter]

/-- **Colour-degrees are `0`, `1` or `2`.**  A vertex is either the centre of a two-edge path of
colour `i`, or has exactly one colour-`i` neighbour, or none. -/
theorem twoA_oneB_or_zero {c : Col n k} (hc : Admissible c) (i : Fin k) (v : Verts n) :
    v ∈ twoA c i ∨ v ∈ oneB c i ∨ (nb c i v (Finset.univ : Finset (Verts n))).card = 0 := by
  by_cases h2 : (nb c i v (Finset.univ : Finset (Verts n))).card = 2
  · exact Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ v, h2⟩)
  by_cases h1 : (nb c i v (Finset.univ : Finset (Verts n))).card = 1
  · exact Or.inr (Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ v, h1⟩))
  have hle := nb_card_le_two hc i v (Finset.univ : Finset (Verts n))
  exact Or.inr (Or.inr (by omega))

/-- **The endpoints of an edge of a colour class are either a centre of a two-edge path, or the edge
is an isolated single edge.** -/
theorem single_or_center {c : Col n k} (hc : Admissible c) (i : Fin k) (a b : Verts n)
    (hab : a ≠ b) (hcol : c s(a, b) = i) :
    Single c s(a, b) ∨ a ∈ twoA c i ∨ b ∈ twoA c i := by
  have hba : b ∈ Nbrs c i a := mem_Nbrs.mpr ⟨hab.symm, hcol⟩
  have hab' : a ∈ Nbrs c i b := mem_Nbrs.mpr ⟨hab, by rw [Sym2.eq_swap]; exact hcol⟩
  have hposa : 0 < (Nbrs c i a).card := Finset.card_pos.mpr ⟨b, hba⟩
  have hposb : 0 < (Nbrs c i b).card := Finset.card_pos.mpr ⟨a, hab'⟩
  rcases twoA_oneB_or_zero hc i a with h2a | h1a | h0a
  · exact Or.inr (Or.inl h2a)
  · rcases twoA_oneB_or_zero hc i b with h2b | h1b | h0b
    · exact Or.inr (Or.inr h2b)
    · refine Or.inl ⟨a, b, rfl, hab, ?_, ?_⟩
      · have hx : (Nbrs c (c s(a, b)) a).card = (Nbrs c i a).card := by rw [hcol]
        rw [hx]
        exact (Finset.mem_filter.mp h1a).2
      · have hx : (Nbrs c (c s(a, b)) b).card = (Nbrs c i b).card := by rw [hcol]
        rw [hx]
        exact (Finset.mem_filter.mp h1b).2
    · exfalso
      have hz : (Nbrs c i b).card = 0 := h0b
      omega
  · exfalso
    have hz : (Nbrs c i a).card = 0 := h0a
    omega

/-- **EVERY EDGE OF A COLOUR CLASS IS EITHER AN EDGE OF A TWO-EDGE PATH OR AN ISOLATED SINGLE EDGE.**
This is the full description of the components of a colour class of an admissible colouring: they
are two-edge paths and isolated single edges (an edge alone in its colour class). -/
theorem mem_classIn_single_or_path {c : Col n k} (hc : Admissible c) {i : Fin k}
    {e : Sym2 (Verts n)} (he : e ∈ classIn c i (Finset.univ : Finset (Verts n))) :
    Single c e ∨ ∃ v ∈ twoA c i, e ∈ pathEdges c i v := by
  obtain ⟨a, b, hab⟩ := Sym2.exists.mp (show ∃ e' : Sym2 (Verts n), e = e' from ⟨e, rfl⟩)
  have he' := he
  rw [hab] at he'
  have hmem := mem_classIn.mp he'
  have hcol : c s(a, b) = i := hmem.2
  have habne : a ≠ b := (mem_edgeFinset.mp hmem.1).2 a b rfl
  rcases single_or_center hc i a b habne hcol with h | h2a | h2b
  · refine Or.inl ?_
    rw [hab]
    exact h
  · exact Or.inr ⟨a, h2a, (mem_pathEdges i).mpr
      ⟨b, mem_Nbrs.mpr ⟨habne.symm, hcol⟩, hab⟩⟩
  · exact Or.inr ⟨b, h2b, (mem_pathEdges i).mpr
      ⟨a, mem_Nbrs.mpr ⟨habne, by rw [Sym2.eq_swap]; exact hcol⟩, hab.trans Sym2.eq_swap.symm⟩⟩

/-- **A colour class has exactly `|E_i| - 2 * |A_i|` single edges**: the edges of the two-edge paths
of that colour, which are pairwise disjoint (`Extremal.two_mul_twoA_le_classIn`) and are never
single edges (`Cherry.not_Single_of_path_edge`), leave exactly the single edges. -/
theorem card_single_in_classIn {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n) (i : Fin k) :
    (singleFinset c ∩ classIn c i (Finset.univ : Finset (Verts n))).card
      = (classIn c i (Finset.univ : Finset (Verts n))).card - 2 * (twoA c i).card := by
  set U := (Finset.univ : Finset (Verts n)) with hU
  set P : Finset (Sym2 (Verts n)) := (twoA c i).biUnion (fun v => pathEdges c i v) with hP
  have hcardP : P.card = 2 * (twoA c i).card := by
    have hcard : ∀ v ∈ twoA c i, (pathEdges c i v).card = 2 := fun v hv => card_pathEdges i hv
    have hdisc : (↑(twoA c i) : Set (Verts n)).PairwiseDisjoint (fun v => pathEdges c i v) := by
      intro v hv w hw hvw
      exact pathEdges_disjoint hc hn i (Finset.mem_coe.mp hv) (Finset.mem_coe.mp hw) hvw
    have h1 : P.card = ∑ v ∈ twoA c i, (pathEdges c i v).card := Finset.card_biUnion hdisc
    calc P.card = ∑ v ∈ twoA c i, (pathEdges c i v).card := h1
      _ = ∑ v ∈ twoA c i, (2 : ℕ) := by
          refine Finset.sum_congr rfl fun v hv => hcard v (Finset.mem_coe.mp hv)
      _ = (twoA c i).card • (2 : ℕ) := Finset.sum_const _
      _ = 2 * (twoA c i).card := by rw [nsmul_eq_mul]; exact Nat.mul_comm _ _
  have hPsub : P ⊆ classIn c i U := by
    rw [hP]
    refine Finset.biUnion_subset.mpr fun v hv => ?_
    exact fun e he => pathEdges_subset_classIn i he
  have hPdisj : Disjoint P (singleFinset c) := by
    rw [hP]
    refine Finset.disjoint_left.mpr fun e heP heS => ?_
    obtain ⟨v, hv, he⟩ := Finset.mem_biUnion.mp heP
    obtain ⟨a, ha, he'⟩ := (mem_pathEdges i).mp he
    rw [he'] at heS
    exact (not_Single_of_path_edge i (Finset.mem_coe.mp hv) ha) (mem_singleFinset.mp heS).2

  have hsub : classIn c i U ⊆ P ∪ (singleFinset c ∩ classIn c i U) := by
    intro e he
    rcases mem_classIn_single_or_path hc he with h | ⟨v, hv, he'⟩
    · exact Finset.mem_union.mpr
        (Or.inr (Finset.mem_inter.mpr ⟨mem_singleFinset.mpr ⟨(mem_classIn.mp he).1, h⟩, he⟩))
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_biUnion.mpr ⟨v, Finset.mem_coe.mpr hv, he'⟩))
  have hsup : P ∪ (singleFinset c ∩ classIn c i U) ⊆ classIn c i U :=
    Finset.union_subset hPsub Finset.inter_subset_right
  have heqset : P ∪ (singleFinset c ∩ classIn c i U) = classIn c i U :=
    Finset.Subset.antisymm hsup hsub
  have hdisj : Disjoint P (singleFinset c ∩ classIn c i U) := by
    refine Finset.disjoint_left.mpr fun e heP heS => ?_
    rw [hP] at heP
    obtain ⟨v, hv, he⟩ := Finset.mem_biUnion.mp heP
    obtain ⟨a, ha, he'⟩ := (mem_pathEdges i).mp he
    rw [he'] at heS
    exact (not_Single_of_path_edge i (Finset.mem_coe.mp hv) ha)
      (mem_singleFinset.mp (Finset.mem_inter.mp heS).1).2
  have hEq : (singleFinset c ∩ classIn c i U).card
      = (classIn c i U).card - 2 * (twoA c i).card := by
    have h1 : (P ∪ (singleFinset c ∩ classIn c i U)).card
        = P.card + (singleFinset c ∩ classIn c i U).card := Finset.card_union_of_disjoint hdisj
    have h2 : P.card + (singleFinset c ∩ classIn c i U).card = (classIn c i U).card := by
      rw [← h1]
      exact congrArg Finset.card heqset
    omega
  exact hEq

/-- **THE SINGLE-EDGE IDENTITY.**  Every edge of `K_n` is either one of the two edges of a two-edge
path, or an isolated single edge, and the two kinds are counted by `2 * Paths c` and by
`(singleFinset c).card` respectively:

    |E(K_n)| = 2 * Paths c + (number of single edges). -/
theorem card_singleFinset {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n) :
    (singleFinset c).card
      = (edgeFinset (Finset.univ : Finset (Verts n))).card - 2 * Paths c := by
  have hdisc : (↑(Finset.univ : Finset (Fin k)) : Set (Fin k)).PairwiseDisjoint
      (fun i => singleFinset c ∩ classIn c i (Finset.univ : Finset (Verts n))) := by
    intro i _ j _ hij
    refine Finset.disjoint_left.mpr fun e h1 h2 => ?_
    have hc1 : c e = i := (mem_classIn.mp (Finset.mem_inter.mp h1).2).2
    have hc2 : c e = j := (mem_classIn.mp (Finset.mem_inter.mp h2).2).2
    exact hij (hc1.symm.trans hc2)
  have h1 : ((Finset.univ : Finset (Fin k)).biUnion
      (fun i => singleFinset c ∩ classIn c i (Finset.univ : Finset (Verts n)))).card
      = ∑ i : Fin k, (singleFinset c ∩ classIn c i (Finset.univ : Finset (Verts n))).card :=
    Finset.card_biUnion hdisc
  have h2 : (∑ i : Fin k, (singleFinset c ∩ classIn c i (Finset.univ : Finset (Verts n))).card)
      + (∑ i : Fin k, (2 * (twoA c i).card))
      = ∑ i : Fin k, (classIn c i (Finset.univ : Finset (Verts n))).card := by
    calc (∑ i : Fin k, (singleFinset c ∩ classIn c i (Finset.univ : Finset (Verts n))).card)
          + (∑ i : Fin k, (2 * (twoA c i).card))
        = ∑ i : Fin k, ((singleFinset c ∩ classIn c i (Finset.univ : Finset (Verts n))).card
            + 2 * (twoA c i).card) := (Finset.sum_add_distrib).symm
      _ = ∑ i : Fin k, (classIn c i (Finset.univ : Finset (Verts n))).card := by
          refine Finset.sum_congr rfl fun i _ => ?_
          have h := card_single_in_classIn hc hn i
          have hle := two_mul_twoA_le_classIn hc hn i
          rw [h, Nat.sub_add_cancel hle]
  have h3 : (∑ i : Fin k, (classIn c i (Finset.univ : Finset (Verts n))).card)
      = (edgeFinset (Finset.univ : Finset (Verts n))).card := sum_card_classIn c _
  have h4 : (∑ i : Fin k, (2 * (twoA c i).card)) = 2 * ∑ i : Fin k, (twoA c i).card := by
    rw [← Finset.mul_sum]
  have h5 : (∑ i : Fin k, (twoA c i).card) = Paths c := by rw [Paths]
  have hsub2 : ((Finset.univ : Finset (Fin k)).biUnion
      (fun i => singleFinset c ∩ classIn c i (Finset.univ : Finset (Verts n)))) = singleFinset c := by
    apply Finset.Subset.antisymm
    · intro e he
      obtain ⟨i, _, he'⟩ := Finset.mem_biUnion.mp he
      exact (Finset.mem_inter.mp he').1
    · intro e he
      rw [mem_singleFinset] at he
      refine Finset.mem_biUnion.mpr ⟨c e, Finset.mem_univ _, ?_⟩
      exact Finset.mem_inter.mpr ⟨mem_singleFinset.mpr he, mem_classIn.mpr ⟨he.1, rfl⟩⟩
  rw [hsub2] at h1
  omega

/-- **THE LEAF EDGE OF A TWO-EDGE PATH IS AN ISOLATED SINGLE EDGE** (`Cherry.Single_of_leaf`,
packaged for the finset `singleFinset`). -/
theorem leafEdge_subset_single {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n) {i : Fin k}
    {v : Verts n} (hv : v ∈ twoA c i) {e : Sym2 (Verts n)} (he : e ∈ leafEdge c i v) :
    e ∈ singleFinset c := by
  rw [leafEdge] at he
  obtain ⟨p, hp, he⟩ := Finset.mem_image.mp he
  obtain ⟨hp, hne⟩ := Finset.mem_filter.mp hp
  have hpp := Finset.mem_product.mp hp
  refine mem_singleFinset.mpr ⟨?_, ?_⟩
  · rw [← he]
    exact mem_edgeFinset_mk (Finset.mem_univ p.1) (Finset.mem_univ p.2) hne
  · rw [← he]
    exact Single_of_leaf hc hn i v p.1 p.2 hv hne hpp.1 hpp.2 (c s(p.1, p.2)) rfl

/-- The leaf edge is a single element of `E(K_n)`. -/
theorem card_leafEdge {c : Col n k} (i : Fin k) {v : Verts n} (hv : v ∈ twoA c i) :
    (leafEdge c i v).card = 1 := by
  have h2 := card_twoA i hv
  obtain ⟨a, b, hab, hN⟩ := Finset.card_eq_two.mp h2
  have hB : leafEdge c i v = {s(a, b)} := image_pairs_two (card_twoA i hv) hN hab
  rw [hB]
  simp

/-- **THE LEAF EDGES OF THE TWO-EDGE PATHS ARE PAIRWISE DISTINCT.**  Two two-edge paths cannot have a
common leaf edge, since the triples of edges of two different paths are disjoint
(`Cherry.cherryEdges_disjoint`). -/
theorem leafEdge_disjoint {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n) {i i' : Fin k}
    {v w : Verts n} (hvi : v ∈ twoA c i) (hvi' : w ∈ twoA c i')
    (hne : (i, v) ≠ (i', w)) : Disjoint (leafEdge c i v) (leafEdge c i' w) := by
  refine Finset.disjoint_left.mpr fun e he1 he2 => ?_
  have h1 : e ∈ cherryEdges c i v := Finset.mem_union.mpr (Or.inr he1)
  have h2 : e ∈ cherryEdges c i' w := Finset.mem_union.mpr (Or.inr he2)
  have hd := cherryEdges_disjoint hc hn hvi hvi' hne
  exact Finset.disjoint_left.mp hd h1 h2

/-- **AT LEAST ONE THIRD OF THE EDGES LIE IN SINGLE-EDGE COMPONENTS.**  The leaf edges of the
`Paths c` two-edge paths are pairwise distinct isolated single edges, so the number of single edges
is at least the number of two-edge paths.  Together with `Cherry.three_mul_paths_le_edges`
(`3 * Paths c ≤ |E(K_n)|`) this sandwiches

    Paths c ≤ (number of single edges) = |E(K_n)| - 2 * Paths c,

and in the extremal case the two inequalities coincide: *every* single edge is a leaf edge. -/
theorem paths_le_singles {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n) :
    Paths c ≤ (singleFinset c).card := by
  have hdisc : (↑(cherryFinset c) : Set (Fin k × Verts n)).PairwiseDisjoint
      (fun p => leafEdge c p.1 p.2) := by
    intro p hp q hq hpq
    exact leafEdge_disjoint hc hn (twoA_of_mem_cherryFinset (Finset.mem_coe.mp hp))
      (twoA_of_mem_cherryFinset (Finset.mem_coe.mp hq)) hpq
  have h1 : ((cherryFinset c).biUnion (fun p => leafEdge c p.1 p.2)).card
      = ∑ p ∈ cherryFinset c, (leafEdge c p.1 p.2).card := Finset.card_biUnion hdisc
  have h2 : (∑ p ∈ cherryFinset c, (leafEdge c p.1 p.2).card) = (cherryFinset c).card := by
    calc (∑ p ∈ cherryFinset c, (leafEdge c p.1 p.2).card)
        = ∑ p ∈ cherryFinset c, (1 : ℕ) := by
          refine Finset.sum_congr rfl fun p hp =>
            card_leafEdge p.1 (twoA_of_mem_cherryFinset (Finset.mem_coe.mp hp))
      _ = (cherryFinset c).card • (1 : ℕ) := Finset.sum_const _
      _ = (cherryFinset c).card := by rw [nsmul_eq_mul, Nat.mul_one, Nat.cast_id]
  have hcardBI : ((cherryFinset c).biUnion (fun p => leafEdge c p.1 p.2)).card
      = (cherryFinset c).card := h1.trans h2
  have hsub : ((cherryFinset c).biUnion (fun p => leafEdge c p.1 p.2)) ⊆ singleFinset c := by
    intro e he
    obtain ⟨p, hp, he'⟩ := Finset.mem_biUnion.mp he
    exact leafEdge_subset_single hc hn (twoA_of_mem_cherryFinset (Finset.mem_coe.mp hp)) he'
  have h3 : (cherryFinset c).card ≤ (singleFinset c).card := by
    rw [← hcardBI]
    exact Finset.card_le_card hsub
  rw [← card_cherryFinset]
  exact h3

/-- **IN THE EXTREMAL CASE THE SINGLE EDGES ARE EXACTLY THE LEAF EDGES OF THE TWO-EDGE PATHS.**
Both numbers are `n(n-1)/6`: the `n(n-1)/6` two-edge paths contribute `2 n(n-1)/6` edges and, in the
extremal case, the remaining `n(n-1)/6` edges of `K_n` are all isolated single edges.  Combined with
`Rigidity.tight_pathFinset_is_STS` this says: *in an extremal colouring the single edges are
canonically in bijection with the blocks of the Steiner triple system, one per block*, namely the
edge joining the two leaves of the two-edge path attached to that block. -/
theorem tight_card_singles {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n)
    (h3 : 3 * Paths c = (edgeFinset (Finset.univ : Finset (Verts n))).card)
    (hk : 6 * k = 5 * (n - 1)) :
    (singleFinset c).card = n * (n - 1) / 6 := by
  have hcard := card_singleFinset hc hn
  have hpaths := tight_paths hc hn h3
  have hle := paths_le_singles hc hn
  have hEq : (singleFinset c).card = Paths c := by omega
  rw [hEq, hpaths]

/-- **AND EVERY SINGLE EDGE IS THE LEAF EDGE OF EXACTLY ONE TWO-EDGE PATH.**  In the extremal case
the single edges and the leaf edges have the same cardinality and the leaf edges are pairwise
distinct (`leafEdge_disjoint`), so the two families of edges are equal: the map

        two-edge path  ↦  the edge joining its two leaves

is a **bijection** from the two-edge paths onto the single edges of the colouring.  With
`Rigidity.tight_pathFinset_is_STS` this completes the description of the extremal case:

* the two-edge paths decompose `K_n` into the blocks of a Steiner triple system;
* each block carries a centre, and its leaf edge is a single edge;
* every single edge of the colouring is the leaf edge of exactly one block. -/
theorem tight_single_is_leaf {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n)
    (h3 : 3 * Paths c = (edgeFinset (Finset.univ : Finset (Verts n))).card)
    (hk : 6 * k = 5 * (n - 1)) {e : Sym2 (Verts n)} (he : e ∈ singleFinset c) :
    ∃! p : Fin k × Verts n, p ∈ cherryFinset c ∧ e ∈ leafEdge c p.1 p.2 := by
  have hdisc : (↑(cherryFinset c) : Set (Fin k × Verts n)).PairwiseDisjoint
      (fun p => leafEdge c p.1 p.2) := by
    intro p hp q hq hpq
    exact leafEdge_disjoint hc hn (twoA_of_mem_cherryFinset (Finset.mem_coe.mp hp))
      (twoA_of_mem_cherryFinset (Finset.mem_coe.mp hq)) hpq
  have h1 : ((cherryFinset c).biUnion (fun p => leafEdge c p.1 p.2)).card
      = ∑ p ∈ cherryFinset c, (leafEdge c p.1 p.2).card := Finset.card_biUnion hdisc
  have hsub : ((cherryFinset c).biUnion (fun p => leafEdge c p.1 p.2)) ⊆ singleFinset c := by
    intro x hx
    obtain ⟨p, hp, hx'⟩ := Finset.mem_biUnion.mp hx
    exact leafEdge_subset_single hc hn (twoA_of_mem_cherryFinset (Finset.mem_coe.mp hp)) hx'
  have hcard := card_singleFinset hc hn
  have hcards : (singleFinset c).card = (cherryFinset c).card := by
    rw [card_cherryFinset]
    omega
  have hcardBI : ((cherryFinset c).biUnion (fun p => leafEdge c p.1 p.2)).card
      = (cherryFinset c).card := by
    have h1 : ((cherryFinset c).biUnion (fun p => leafEdge c p.1 p.2)).card
        = ∑ p ∈ cherryFinset c, (leafEdge c p.1 p.2).card := Finset.card_biUnion hdisc
    have h2 : (∑ p ∈ cherryFinset c, (leafEdge c p.1 p.2).card) = (cherryFinset c).card := by
      calc (∑ p ∈ cherryFinset c, (leafEdge c p.1 p.2).card)
          = ∑ p ∈ cherryFinset c, (1 : ℕ) := by
            refine Finset.sum_congr rfl fun p hp =>
              card_leafEdge p.1 (twoA_of_mem_cherryFinset (Finset.mem_coe.mp hp))
        _ = (cherryFinset c).card • (1 : ℕ) := Finset.sum_const _
        _ = (cherryFinset c).card := by rw [nsmul_eq_mul, Nat.mul_one, Nat.cast_id]
    exact h1.trans h2
  have heq : ((cherryFinset c).biUnion (fun p => leafEdge c p.1 p.2)) = singleFinset c :=
    Finset.eq_of_subset_of_card_le hsub (by rw [hcards, ← hcardBI])
  have hex : e ∈ (cherryFinset c).biUnion (fun p => leafEdge c p.1 p.2) := heq ▸ he
  obtain ⟨p, hp, hp'⟩ := Finset.mem_biUnion.mp hex
  have hmem : p ∈ cherryFinset c ∧ e ∈ leafEdge c p.1 p.2 := ⟨Finset.mem_coe.mpr hp, hp'⟩
  refine ⟨p, hmem, ?_⟩
  intro q hq
  by_cases hqp : (q.1, q.2) = (p.1, p.2)
  · have hpq : (p.1, p.2) = (q.1, q.2) := hqp.symm
    exact Prod.ext_iff.mpr ⟨(congrArg Prod.fst hpq).symm, (congrArg Prod.snd hpq).symm⟩
  · have hd := leafEdge_disjoint hc hn (twoA_of_mem_cherryFinset hq.1)
      (twoA_of_mem_cherryFinset hmem.1) hqp
    exact False.elim (Finset.disjoint_left.mp hd hq.2 hp')

end JSP140
