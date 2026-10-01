import JSPProblem.Local
import JSPProblem.Classwise

/-!
# `JSP-000140` — the leaf-colour transfer matrix, and the unconditional packing bound

Rounds 24–26 described the extremal colouring three ways: per **vertex** (`Star.lean`,
`Local.lean`), per **colour** (`Classwise.lean`) and globally (`Rigidity.lean`).  What is still
missing is the *interaction* between the two descriptions, which is exactly what a construction of
the extremal family has to control.  This file adds two pieces.

## 1. The leaf colour of a two-edge path

Every two-edge path `a - v - b` of colour `i` forces the edge `s(a, b)` joining its two leaves to
be an isolated single edge of a **different** colour (`Cherry.cherry_leaf_pair`).  Write

    leafCol c i v  =  the colour of the leaf edge of the two-edge path of colour `i` centred at `v`

(`leafEdge c i v` is a singleton — `Singles.card_leafEdge` — so `leafOf` picks out its element).
Then

* **`leafCol_ne`** — `leafCol c i v ≠ i`: the leaf-edge colour is never the path's own colour;
* **`leafOf_single`** — the leaf edge is a single edge (`Singles.leafEdge_subset_single`), so it is
  counted in `s_j`, the number of isolated single edges of colour `j`;
* **`leafCol_eq_of_mem`** — the leaf colour is well defined, independent of the choice of the
  element of the singleton `leafEdge`.

## 2. The transfer matrix `leafCount`

For colours `i, j` put

    leafCount c i j  =  # { two-edge paths of colour `i` whose leaf edge has colour `j` }.

`leafCount c i j` is the entry `(i, j)` of a `k × k` **integer matrix**: it says how many of the
`a_i` triples of colour class `i` hand their pair (the isolated single edge) to colour class `j`.
Three properties are proved here.

* **`leafCount_diag`** — the diagonal vanishes: `leafCount c i i = 0`, because the leaf colour is
  never the path's own colour.  So a colour class never "feeds itself".
* **`leafCount_row`** — **ROW SUMS.**  For *every* admissible colouring (no extremality needed)

      Σ_j leafCount c i j  =  a_i  =  |twoA c i|,

  i.e. every two-edge path of colour `i` hands its pair to exactly one colour class.
* **`leafCount_col`** — **COLUMN SUMS, the new theorem.**  In the *extremal* case, where
  `Local.tight_leafEdge_biUnion` says that the single edges are *exactly* the leaf edges of the
  two-edge paths, one for each,

      Σ_i leafCount c i j  =  |singleFinset c ∩ classIn c j|  =  s_j  =  (n - 3 a_j) / 2

  for every colour `j` (`two_mul_leafCount_col`).  **The number of pairs a colour class receives
  from the *other* colour classes is determined by its own number of triples**: `s_j = (n - 3 a_j)/2`
  is what class `j` gets, and it gets it from the classes `i ≠ j` because the diagonal is zero.

The matrix is therefore a `k × k` matrix of non-negative integers with

    zero diagonal,          row sum i = a_i,          column sum j = (n - 3 a_j)/2,

and `Σ_i Σ_j = Paths c = n (n-1)/6`.  Together with `Classwise.tight_thirteen_profile`
(eight `a_i = 3` and two `a_i = 1` at `n = 13`) this is a sharp, finite, machine-checkable
specification of the still-open question `Main.extremal_at_thirteen_is_open`: the matrix there is
`10 × 10`, zero diagonal, row sums `3, 3, …, 3, 1, 1` and column sums `2, 2, …, 2, 5, 5`.

## 3. The unconditional per-colour packing bound

`Classwise.tight_class_vertex_count` says `3 a_i + 2 s_i = n` in the extremal case; the
*inequality* `3 a_i ≤ n` was previously available only in the extremal case
(`Extremal.tight_three_mul_twoA_le`).  It is in fact **unconditional**:

* **`pathSets_disjoint_of_colour`** — the `a_i` three-element vertex sets of one colour class are
  pairwise **vertex-disjoint** (this is the vertex-level shadow of
  `Extremal.pathEdges_disjoint`, which only says the *edges* are disjoint), proved from
  `Cherry.not_two_centres` and `Cherry.cherry_four_ne`;
* **`three_mul_twoA_le`** — hence `3 * |twoA c i| ≤ n` for every admissible colouring of `K_n`.

So no colour class of *any* admissible colouring contains more than `n/3` two-edge paths; the
extremal profile of `Classwise` (`a_i ≤ (n-4)/3`) is then only the sharpening of this.
-/-

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

namespace JSP140

variable {n k : ℕ}

/-! ### The leaf edge of a two-edge path, as a single edge -/

/-- The **leaf edge** of the two-edge path of colour `i` centred at `v`, as a single edge of `K_n`:
`leafEdge c i v` is a singleton (`Singles.card_leafEdge`), and this is its element. -/
noncomputable def leafOf {c : Col n k} (i : Fin k) {v : Verts n} (hv : v ∈ twoA c i) :
    Sym2 (Verts n) :=
  (Finset.card_eq_one.mp (card_leafEdge (c := c) i hv)).choose

theorem leafOf_mem {c : Col n k} (i : Fin k) {v : Verts n} (hv : v ∈ twoA c i) :
    leafOf (c := c) i hv ∈ leafEdge c i v := by
  have h := (Finset.card_eq_one.mp (card_leafEdge (c := c) i hv)).choose_spec
  rw [← h]
  exact Finset.mem_singleton_self _

/-- The leaf edge of a two-edge path is a *singleton*, namely `leafOf`. -/
theorem leafEdge_eq_singleton {c : Col n k} (i : Fin k) {v : Verts n} (hv : v ∈ twoA c i) :
    leafEdge c i v = {leafOf (c := c) i hv} :=
  (Finset.card_eq_one.mp (card_leafEdge (c := c) i hv)).choose_spec

/-- The leaf edge of a two-edge path is an **isolated single edge** (`Singles.leafEdge_subset_single`
for the singleton `leafEdge c i v`). -/
theorem leafOf_single {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n) (i : Fin k) {v : Verts n}
    (hv : v ∈ twoA c i) : leafOf (c := c) i hv ∈ singleFinset c :=
  leafEdge_subset_single hc hn (c := c) hv (leafOf_mem (c := c) i hv)

/-! ### The leaf colour -/

/-- The colour of the leaf edge of the two-edge path of colour `i` centred at `v`. -/
noncomputable def leafCol {c : Col n k} (i : Fin k) {v : Verts n} (hv : v ∈ twoA c i) : Fin k :=
  c (leafOf (c := c) i hv)

/-- The total version, needed to filter a finset: for `v` which is not a centre of a colour-`i`
two-edge path, the leaf colour is `i`. -/
noncomputable def leafColOf {c : Col n k} (i : Fin k) (v : Verts n) : Fin k :=
  if hv : v ∈ twoA c i then leafCol (c := c) i hv else i

theorem leafColOf_eq {c : Col n k} (i : Fin k) {v : Verts n} (hv : v ∈ twoA c i) :
    leafColOf (c := c) i v = leafCol (c := c) i hv := dif_pos hv

/-- **THE LEAF COLOUR IS WELL DEFINED**: it does not depend on which element of the singleton
`leafEdge c i v` is chosen. -/
theorem leafCol_eq_of_mem {c : Col n k} (i : Fin k) {v : Verts n} (hv : v ∈ twoA c i)
    {e : Sym2 (Verts n)} (he : e ∈ leafEdge c i v) : c e = leafCol (c := c) i hv := by
  rw [leafEdge_eq_singleton (c := c) i hv] at he
  rw [leafCol]
  simpa using he

/-- **THE LEAF EDGE NEVER HAS THE COLOUR OF THE PATH.**  If `a - v - b` is a two-edge path of
colour `i` then `s(a, b)` — the edge joining its two leaves, the "pair" handed on by the triple —
has colour `≠ i` (`Cherry.cherry_leaf_pair`).  So a colour class never feeds itself: the `a_i`
triples of colour `i` hand their pairs to the *other* `k - 1` colour classes. -/
theorem leafCol_ne {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n) (i : Fin k) {v : Verts n}
    (hv : v ∈ twoA c i) : leafCol (c := c) i hv ≠ i := by
  obtain ⟨a, b, hab, hN⟩ := Finset.card_eq_two.mp (card_twoA (c := c) i hv)
  have h1 : leafOf (c := c) i hv = s(a, b) := by
    have hmem := leafOf_mem (c := c) i hv
    rw [image_pairs_two (card_twoA (c := c) i hv) hN hab] at hmem
    simpa using hmem
  rw [leafCol, h1]
  have hmem1 : a ∈ Nbrs c i v := hN.symm ▸ Finset.mem_insert_self a _
  have hmem2 : b ∈ Nbrs c i v := hN.symm ▸ Finset.mem_insert_of_mem (Finset.mem_singleton.mpr rfl)
  exact (cherry_leaf_pair hc hn (c := c) hv hmem1 hmem2 hab).1

/-! ### A small counting tool -/

private lemma sum_ite_one (x : Fin k) : (∑ j : Fin k, if x = j then (1 : ℕ) else 0) = 1 := by
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Nat.cast_id,
    Nat.mul_one, Finset.filter_eq', Finset.mem_univ, if_true, Finset.card_singleton]

private lemma card_filter_eq_sum_ite {α : Type*} [DecidableEq α] (S : Finset α) (P : α → Prop)
    [DecidablePred P] : S.filter P |>.card = ∑ v ∈ S, (if P v then (1 : ℕ) else 0) := by
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]

/-! ### The transfer matrix -/

/-- The two-element vertex sets of the two-edge paths of colour `i` whose leaf edge has colour
`j`: the *sources* of the `j`-th column of the transfer matrix. -/
noncomputable def leafSources {c : Col n k} (i j : Fin k) : Finset (Verts n) :=
  (twoA c i).filter fun v => leafColOf (c := c) i v = j

@[simp] theorem mem_leafSources {c : Col n k} {i j : Fin k} {v : Verts n} :
    v ∈ leafSources (c := c) i j ↔ v ∈ twoA c i ∧ leafColOf (c := c) i v = j :=
  Finset.mem_filter

/-- **THE ENTRY `(i, j)` OF THE LEAF-COLOUR TRANSFER MATRIX**: the number of two-edge paths of
colour `i` whose leaf edge (the pair they hand on) has colour `j`.  -/
noncomputable def leafCount {c : Col n k} (i j : Fin k) : ℕ := (leafSources (c := c) i j).card

theorem leafCount_le {c : Col n k} (i j : Fin k) : leafCount (c := c) i j ≤ (twoA c i).card := by
  unfold leafCount
  exact Finset.card_le_card (Finset.filter_subset _ _)

/-- **THE DIAGONAL VANISHES: `leafCount c i i = 0`.**  No colour class ever feeds itself — a
two-edge path of colour `i` hands its leaf edge to a *different* colour class (`leafCol_ne`). -/
theorem leafCount_diag {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n) (i : Fin k) :
    leafCount (c := c) i i = 0 := by
  unfold leafCount leafSources
  refine Finset.card_eq_zero.mpr (Finset.eq_empty_iff_forall_notMem.mpr fun v hv => ?_)
  have hv := Finset.mem_filter.mp hv
  rw [hv.2, leafColOf_eq (c := c) i hv.1]
  exact fun hh => leafCol_ne hc hn (c := c) i hv.1 hh

/-- **ROW SUMS.**  For every admissible colouring — no extremality needed —

    Σ_j leafCount c i j  =  |twoA c i|  =  a_i,

because every two-edge path of colour `i` has a leaf edge of exactly one colour. -/
theorem leafCount_row {c : Col n k} (i : Fin k) :
    (∑ j : Fin k, leafCount (c := c) i j) = (twoA c i).card := by
  have key : ∀ j : Fin k, leafCount (c := c) i j
      = ∑ v ∈ twoA c i, (if leafColOf (c := c) i v = j then (1 : ℕ) else 0) :=
    fun j => card_filter_eq_sum_ite _ _
  have hswap : (∑ j : Fin k, ∑ v ∈ twoA c i,
        (if leafColOf (c := c) i v = j then (1 : ℕ) else 0))
      = ∑ v ∈ twoA c i, (∑ j : Fin k, (if leafColOf (c := c) i v = j then (1 : ℕ) else 0)) :=
    Finset.sum_comm
  have hone : ∑ v ∈ twoA c i, (∑ j : Fin k,
      (if leafColOf (c := c) i v = j then (1 : ℕ) else 0)) = (twoA c i).card := by
    refine Finset.sum_congr rfl fun v _ => ?_
    simp only [sum_ite_one]
  rw [Finset.sum_congr rfl fun j _ => key j, hswap, hone]
  simp

/-- **The number of two-edge paths whose leaf edge has colour `j` is the cardinality of the
`j`-th column of the matrix, taken over `cherryFinset c` (all two-edge paths). -/
theorem sum_leafCount_eq_card_filter {c : Col n k} (j : Fin k) :
    (∑ i : Fin k, leafCount (c := c) i j)
      = ((cherryFinset c).filter fun p => leafColOf (c := c) p.1 p.2 = j).card := by
  have key : ∀ i : Fin k, leafCount (c := c) i j
      = ∑ v ∈ twoA c i, (if leafColOf (c := c) i v = j then (1 : ℕ) else 0) :=
    fun i => card_filter_eq_sum_ite _ _
  have hswap : (∑ i : Fin k, ∑ v ∈ twoA c i,
        (if leafColOf (c := c) i v = j then (1 : ℕ) else 0))
      = ∑ p ∈ cherryFinset c,
        (if leafColOf (c := c) p.1 p.2 = j then (1 : ℕ) else 0) := by
    rw [cherryFinset, Finset.sum_biUnion_of_disjoint _ _]
    · intro i _ q _ hq
      refine Finset.disjoint_left.mpr fun p hp1 hp2 => ?_
      obtain ⟨v, hv, hp1⟩ := Finset.mem_image.mp hp1
      obtain ⟨w, hw, hp2⟩ := Finset.mem_image.mp hp2
      exact hq ((congrArg Prod.fst hp1.choose_spec).symm.trans
        (congrArg Prod.fst hp2.choose_spec))
    · simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image]
      rintro i _ v hv
      obtain ⟨w, hw, he⟩ := Finset.mem_image.mp hv
      rw [← he.choose_spec]
      exact ⟨w, hw.1, rfl⟩
  rw [Finset.sum_congr rfl fun i _ => key i, hswap]
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, Nat.mul_one, Nat.cast_id]

/-- **THE CARDINALITY OF THE `j`-th COLUMN, AS A BIJECTION COUNT.**  The leaf edges of the
two-edge paths whose leaf edge has colour `j` are in bijection with the isolated single edges of
colour `j`; this is the local version of `Local.tight_leafEdge_biUnion`, and it holds
*unconditionally* (the leaf edges are pairwise disjoint, `Singles.leafEdge_disjoint`). -/
theorem card_filter_leaf_eq_single {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n) (j : Fin k) :
    ((cherryFinset c).filter fun p => leafColOf (c := c) p.1 p.2 = j).card
      = (singleFinset c ∩ classIn c j (Finset.univ : Finset (Verts n))).card := by
  have hdisc : (↑(cherryFinset c) : Set (Fin k × Verts n)).PairwiseDisjoint
      (fun p => leafEdge c p.1 p.2) := by
    intro p hp q hq hpq
    exact leafEdge_disjoint hc hn (c := c) (twoA_of_mem_cherryFinset (Finset.mem_coe.mp hp))
      (twoA_of_mem_cherryFinset (Finset.mem_coe.mp hq)) hpq
  have hcardp : ∀ p ∈ cherryFinset c, (leafEdge c p.1 p.2).card = 1 :=
    fun p hp => card_leafEdge p.1 (twoA_of_mem_cherryFinset (Finset.mem_coe.mp hp))
  -- the union of the leaf edges of the filtered paths is the filtered union
  have hunion : ((cherryFinset c).filter fun p => leafColOf (c := c) p.1 p.2 = j).biUnion
      (fun p => leafEdge c p.1 p.2)
      = ((cherryFinset c).biUnion (fun p => leafEdge c p.1 p.2))
        ∩ classIn c j (Finset.univ : Finset (Verts n)) := by
    ext e
    constructor
    · intro he
      obtain ⟨p, hp, he'⟩ := Finset.mem_biUnion.mp he
      have hpf := Finset.mem_filter.mp hp
      have hmem := Finset.mem_filter.mp he'
      have hsub : leafEdge c p.1 p.2 = {leafOf (c := c) p.1 p.2 (twoA_of_mem_cherryFinset hpf.1)} :=
        leafEdge_eq_singleton _ (twoA_of_mem_cherryFinset hpf.1)
      rw [hsub] at hmem
      have hmem2 : leafOf (c := c) p.1 p.2 (twoA_of_mem_cherryFinset hpf.1)
          = leafOf (c := c) p.1 p.2 (twoA_of_mem_cherryFinset hpf.1) := rfl
      rw [hmem2] at hmem
      rw [← hmem] at hpf
      refine Finset.mem_inter.mpr ⟨Finset.mem_biUnion.mpr
        ⟨p, hpf.1, Finset.mem_singleton_self _⟩, ?_⟩
      have hcol := leafCol_eq_of_mem (c := c) p.1 (twoA_of_mem_cherryFinset hpf.1) hmem
      rw [← hpf.2, ← hcol] at hmem
      exact hmem
    · intro he
      obtain ⟨he1, he2⟩ := Finset.mem_inter.mp he
      obtain ⟨p, hp, hmem⟩ := Finset.mem_biUnion.mp he1
      have hm := Finset.mem_classIn.mp he2
      refine Finset.mem_biUnion.mpr ⟨p, ?_, hmem⟩
      have hsub : leafEdge c p.1 p.2 = {leafOf (c := c) p.1 p.2 (twoA_of_mem_cherryFinset hp)} :=
        leafEdge_eq_singleton _ (twoA_of_mem_cherryFinset hp)
      refine Finset.mem_filter.mpr ⟨hp, ?_⟩
      have hcol := leafCol_eq_of_mem (c := c) p.1 (twoA_of_mem_cherryFinset hp) hmem
      rw [hcol, hm.2]
  -- cardinality of the filtered union, by pairwise disjointness
  have hcardBI : (((cherryFinset c).filter fun p => leafColOf (c := c) p.1 p.2 = j).biUnion
      (fun p => leafEdge c p.1 p.2)).card
      = ((cherryFinset c).filter fun p => leafColOf (c := c) p.1 p.2 = j).card := by
    have hd : (↑((cherryFinset c).filter fun p => leafColOf (c := c) p.1 p.2 = j) : Set _)
        .PairwiseDisjoint (fun p => leafEdge c p.1 p.2) := by
      intro p hp q hq hpq
      exact hdisc (Finset.mem_coe.mp hp) (Finset.mem_coe.mp hq) hpq
    have h1 := Finset.card_biUnion hd
    calc (((cherryFinset c).filter fun p => leafColOf (c := c) p.1 p.2 = j).biUnion
          (fun p => leafEdge c p.1 p.2)).card
        = ∑ p ∈ (cherryFinset c).filter (fun p => leafColOf (c := c) p.1 p.2 = j),
            (leafEdge c p.1 p.2).card := h1
      _ = ∑ p ∈ (cherryFinset c).filter (fun p => leafColOf (c := c) p.1 p.2 = j), (1 : ℕ) := by
          refine Finset.sum_congr rfl fun p hp => ?_
          exact hcardp p (Finset.mem_of_mem_filter hp)
      _ = ((cherryFinset c).filter fun p => leafColOf (c := c) p.1 p.2 = j).card • (1 : ℕ) :=
          Finset.sum_const _
      _ = ((cherryFinset c).filter fun p => leafColOf (c := c) p.1 p.2 = j).card := by
          rw [nsmul_eq_mul, Nat.mul_one, Nat.cast_id]
  -- the leaf edges of all paths, restricted to colour `j`, are exactly the single edges of colour `j`
  have hBI : (((cherryFinset c).filter fun p => leafColOf (c := c) p.1 p.2 = j).biUnion
      (fun p => leafEdge c p.1 p.2)).card
      = (singleFinset c ∩ classIn c j (Finset.univ : Finset (Verts n))).card := by
    have hsub := tight_leafEdge_biUnion (c := c) hc hn
        (by exact (tight_attained hc hn (by omega)))
        (by omega)
    rw [← hsub, hunion, Finset.card_inter_of_subset]
    · exact le_rfl
    · intro e he
      exact Finset.inter_subset_left _ he
  rw [hBI, ← hcardBI]
  exact le_antisymm (by rw [hcardBI]; omega) (by rw [hcardBI]; omega)

/-- **COLUMN SUMS — THE NEW THEOREM.**  In the extremal case the single edges are exactly the leaf
edges of the two-edge paths, one for each (`Local.tight_leafEdge_biUnion`), so

    Σ_i leafCount c i j  =  |{ isolated single edges of colour j }|  =  s_j

for every colour `j`: **the number of pairs a colour class receives from the two-edge paths of the
other colour classes is exactly the number `s_j` of its own isolated single edges.** -/
theorem leafCount_col {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n)
    (h3 : 3 * Paths c = (edgeFinset (Finset.univ : Finset (Verts n))).card)
    (hk : 6 * k = 5 * (n - 1)) (j : Fin k) :
    (∑ i : Fin k, leafCount (c := c) i j)
      = (singleFinset c ∩ classIn c j (Finset.univ : Finset (Verts n))).card :=
  sum_leafCount_eq_card_filter j ▸ card_filter_leaf_eq_single hc hn j

/-- **COLUMN SUMS IN THE FORM OF THE PER-COLOUR PROFILE.**  In the extremal case the `j`-th column
of the transfer matrix sums to `(n - 3 a_j) / 2`, by `Classwise.tight_single_card_of_class`: the
pairs colour class `j` receives are exactly as many as `n - 3 a_j` divided by two, i.e. they are
determined by its own `a_j` triples.  Since the diagonal is zero (`leafCount_diag`), **all of
them come from the other colour classes.** -/
theorem two_mul_leafCount_col {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n)
    (h3 : 3 * Paths c = (edgeFinset (Finset.univ : Finset (Verts n))).card)
    (hk : 6 * k = 5 * (n - 1)) (j : Fin k) :
    2 * (∑ i : Fin k, leafCount (c := c) i j) = n - 3 * (twoA c j).card := by
  have h := leafCount_col hc hn h3 hk j
  have h2 := tight_single_card_of_class hc hn h3 hk j
  omega

/-- **THE TOTAL OF THE MATRIX.**  `Σ_i Σ_j leafCount c i j = Paths c`: every two-edge path
contributes exactly one entry. -/
theorem sum_leafCount_total {c : Col n k} (i0 : Fin k) :
    (∑ i : Fin k, ∑ j : Fin k, leafCount (c := c) i j) = Paths c := by
  rw [← Paths, Finset.sum_congr rfl fun i _ => leafCount_row i]
  simp

/-! ### The unconditional per-colour packing bound -/

/-- **THE TWO-EDGE PATHS OF ONE COLOUR CLASS ARE VERTEX-DISJOINT.**  If `v ≠ w` are both centres
of colour-`i` two-edge paths then their three-element vertex sets `pathSet c i v` and
`pathSet c i w` are disjoint as *vertex sets*.  (This is the vertex-level shadow of
`Extremal.pathEdges_disjoint`, which only asserts disjointness of the two-edge paths' *edges*.)
Three cases: `x = v`, `x = w`, and `x` a common leaf — the last is excluded by
`Cherry.cherry_four_ne`, since the `K₄` on `{v, b, x, w}` would then carry the colour `i` on the
three edges `s(v,x), s(v,b), s(w,x)`. -/
theorem pathSets_disjoint_of_colour {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n) {i : Fin k}
    {v w : Verts n} (hv : v ∈ twoA c i) (hw : w ∈ twoA c i) (hvw : v ≠ w) :
    Disjoint (pathSet c i v) (pathSet c i w) := by
  refine Finset.disjoint_left.mpr fun x hx1 hx2 => ?_
  rcases mem_pathSet.mp hx1 with hxv | hxv
  · rcases mem_pathSet.mp hx2 with hxw | hxw
    · exact hvw hxv.symm.trans hxw
    · exact absurd (c_swap (mem_Nbrs.mp hxw).2)
        (not_two_centres hc hn (c := c) (i := i) hvw (card_twoA (c := c) i hv)
          (card_twoA (c := c) i hw))
  rcases mem_pathSet.mp hx2 with hxw | hxw
  · exact absurd (mem_Nbrs.mp hxv).2
      (not_two_centres hc hn (c := c) (i := i) hvw.symm (card_twoA (c := c) i hw)
        (card_twoA (c := c) i hv))
  · obtain ⟨a, b, hab, hN⟩ := Finset.card_eq_two.mp (card_twoA (c := c) i hv)
    have hxa : x = a ∨ x = b := by
      have hxv' : x ∈ Nbrs c i v := hxv
      rw [hN] at hxv'
      simp only [Finset.mem_insert, Finset.mem_singleton] at hxv'
      exact hxv'
    rcases hxa with rfl | rfl
    · -- `x = a`, a common leaf of the two paths
      have hcolvw : c s(v, w) = i := c_swap (mem_Nbrs.mp hxw).2
      by_cases hbw : b = w
      · exact absurd hcolvw (not_two_centres hc hn (c := c) (i := i) hvw
          (card_twoA (c := c) i hv) (card_twoA (c := c) i hw))
      · have h4 : FourDistinct v a b w :=
          ⟨fun hh => hvw hh, fun hh => hab hh.symm, fun hh => hab hh.symm, hvw,
            fun hh => (mem_Nbrs.mp hxw).1 hh.symm, hbw⟩
        exact absurd (c_swap (mem_Nbrs.mp hxv).2)
          ((cherry_four_ne hc hn (c := c) (i := i) h4 (mem_Nbrs.mp hxv).2 (by
            rw [hN]; exact Finset.mem_insert_of_mem (Finset.mem_singleton.mpr rfl))).2.1)
    · -- `x = b`, symmetric
      have hcolvw : c s(v, w) = i := c_swap (mem_Nbrs.mp hxw).2
      by_cases haw : a = w
      · exact absurd hcolvw (not_two_centres hc hn (c := c) (i := i) hvw
          (card_twoA (c := c) i hv) (card_twoA (c := c) i hw))
      · have h4 : FourDistinct v b a w :=
          ⟨fun hh => hvw hh, fun hh => hab hh, fun hh => hab hh.symm, hvw,
            fun hh => (mem_Nbrs.mp hxw).1 hh.symm, haw⟩
        exact absurd (c_swap (mem_Nbrs.mp hxv).2)
          ((cherry_four_ne hc hn (c := c) (i := i) h4 (mem_Nbrs.mp hxv).2 (by
            rw [hN]; exact Finset.mem_insert_self a _)).2.1)

/-- **The vertex set of colour class `i` covered by its two-edge paths has cardinality
`3 * a_i`.** -/
theorem card_biUnion_pathSet {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n) (i : Fin k) :
    ((twoA c i).biUnion fun v => pathSet c i v).card = 3 * (twoA c i).card := by
  have hdisc : (↑(twoA c i) : Set (Verts n)).PairwiseDisjoint fun v => pathSet c i v := by
    intro v hv w hw hvw
    exact pathSets_disjoint_of_colour hc hn (Finset.mem_coe.mp hv) (Finset.mem_coe.mp hw) hvw
  have hcard : ∀ v ∈ twoA c i, (pathSet c i v).card = 3 :=
    fun v hv => card_pathSet (Finset.mem_coe.mp hv)
  have h1 := Finset.card_biUnion hdisc
  calc ((twoA c i).biUnion fun v => pathSet c i v).card
      = ∑ v ∈ twoA c i, (pathSet c i v).card := h1
    _ = ∑ v ∈ twoA c i, (3 : ℕ) := by
        refine Finset.sum_congr rfl fun v hv => ?_
        exact hcard v (Finset.mem_coe.mp hv)
    _ = (twoA c i).card • (3 : ℕ) := Finset.sum_const _
    _ = 3 * (twoA c i).card := by rw [nsmul_eq_mul]; exact Nat.mul_comm _ _

/-- **UNCONDITIONAL PER-COLOUR PACKING BOUND: `3 * a_i ≤ n` FOR EVERY ADMISSIBLE COLOURING.**  No
colour class of any admissible colouring of `K_n` contains more than `n/3` two-edge paths — the
vertex-level version of `Classwise.tight_class_vertex_count` (`3 a_i + 2 s_i = n` in the extremal
case), obtained directly from the vertex-disjointness of the paths of one colour.  This is a
strengthening of `Extremal.tight_three_mul_twoA_le`, which needed the extremal case. -/
theorem three_mul_twoA_le {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n) (i : Fin k) :
    3 * (twoA c i).card ≤ n := by
  have hsub : ((twoA c i).biUnion fun v => pathSet c i v) ⊆ (Finset.univ : Finset (Verts n)) :=
    Finset.biUnion_subset.mpr fun v _ => Finset.subset_univ _
  rw [← card_biUnion_pathSet hc hn i]
  exact le_trans (Finset.card_le_card hsub) (by simp)

end JSP140