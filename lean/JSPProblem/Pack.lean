import Mathlib.Algebra.Order.BigOperators.Group.Finset
import JSPProblem.BlockCol
import JSPProblem.Alt
import JSPProblem.First

/-!
# JSP-000140 — the *first stage* of the published construction: a **partial** triangle packing

Rounds 49–56 wrote down the `(2,1)`-block colouring of a **triangle decomposition** of `K_n`
(`Block.lean`, `BlockCol.lean`): a Steiner triple system, a centre and two colours per block, the
exact price `n * k = 5 * m + Isolated c` and the recipe `6k = 5(n-1) + 6` at `Isolated = n`.

**But the papers do not build a decomposition.**  arXiv:2207.02920 §4 ("the first phase stops at
`i_max = (1/6) n²(1 - n^{-δ})`, so the hypergraph matching covers `1 - n^{-δ}` of the edges") and
arXiv:2208.12563 Thm 4.2 (IV) ("the graph `L = K_n - E(F)` has maximum degree at most `n^{1-δ}`")
build a **partial** triangle packing whose leftover graph `L` is *sparse but nonempty*, and
arXiv:2207.02920 Claim 4 measures it: "at the end of Phase 1 each vertex is incident with
`O(n^{1-δ})` uncolored edges".  Until now this development had no object for that: `TwoOne` was a
*decomposition* (`cover`), which cannot express a leftover graph at all.

This file closes that gap.  `TwoOne` no longer carries the unused hypothesis `cover`, so it *is* the
published first stage: a packing of edge-disjoint triangles with a centre and two colours each.
What is added here is

## §1 — the leftover graph of a packing

* `PackL C` — the edges of `K_n` in **no** block: the leftover graph of the hypergraph matching.
* `TwoOne.not_mem_PackL` — every block edge is covered, i.e. `PackL C` really is the complement of
  the packing; `PackL.offDiag`, `PackL.subset_univ`.

## §2 — the census of a partial packing

* `TwoOne.card_blEdge` — a block spans three edges; `Pack.blocks_card` — the packing spans `3 * m`
  edges.
* **`Pack.census` — `6 * m + |PackL C| = n * (n - 1)`**: the packing and its leftover partition
  `E(K_n)`.  (For a Steiner triple system, `TwoOne.decomposition_empty`: `PackL C = ∅`, recovering
  the shape of rounds 49–56.)
* `Pack.card_le` — `6 * m ≤ n * (n - 1)`.
* **`Pack.card_two_mul_le` — `SparseL (PackL C) D → 2 * |PackL C| ≤ n * D`** (the handshaking
  lemma `Slot.handshake_le`), and **`Pack.blocks_ge` — the packing covers all but `O(n * D)`
  edges**: with `D = n^{1-δ}` this is arXiv:2207.02920's `1 - n^{-δ}`.
* **`Pack.price` — `6 * k + 5 * D ≥ 5 * (n - 1)`**, i.e. `k ≥ 5(n-1)/6 - 5D/6`: the *partial*
  version of the price of `TwoOne.price` (`5 * m ≤ n * k`, five colour-slots per block of
  arXiv:2208.12563 §4).  For `D = 0` this is the sharp constant `5(n-1)/6 ≤ 6k` of rounds 49–56;
  for the published `D = n^{1-δ}` it reads `6k ≥ 5(n-1) - 5n^{1-δ}`, i.e. `k = 5n/6 - o(n)` —
  the catalog answer, with the rate the papers achieve.

## §3 — the second stage of a *partial* first stage

* **`FirstOk c₀ L` — THE FIRST-STAGE LOCAL CONDITION.**  On every four-set, the colours of the
  *covered* edges together with `⌈|L ∩ E(S)|/2⌉` reach five.  The `⌈·/2⌉` is exact: a proper fresh
  colouring gives `⌈t/2⌉` distinct colours on `t` leftover edges of a four-set, because a colour
  class is a matching.
* `Pack.fresh_colours` — that counting statement (`Proper c L` + `|S| = 4` ⟹
  `⌈|(edgeFinset S ∩ L)|/2⌉ ≤ |(edgeFinset S ∩ L).image c|`), proved by pigeonhole over the fibres,
  whose size is bounded by 2 by `Pack.disjoint_card_le_two` (three vertex-disjoint edges need six
  vertices).
* **`Pack.second_stage` — `FirstOk (C.col) (PackL C)` + `SparseL (PackL C) D` ⟹ an admissible
  `k + 2D + 1` colouring of `K_n`**, and `Pack.eg_le` — `EG n ≤ k + 2 * D + 1`.  Note that
  **`Admissible (C.col)` is *not* a hypothesis**: a partial packing has garbage colours on the
  leftover edges, and the correct local condition on the first stage is `FirstOk`.

## §4 — the prize hypothesis, in design language only

* **`PackFamily`**: for every `ε' > 0` there is `N` such that every `n ≥ N` carries a packing with
  a leftover of maximum degree `D` (constant in `n`), satisfying `FirstOk`, and priced by
  `6 * (k₁ + 2D + 1) ≤ 5 * (n -1) + ε' * n`.
* **`Pack.target_of_packFamily` — `PackFamily → jsp_000140_target`.**

  Compare with round 33's `CrossStageFamily`, whose hypothesis is a **colouring** `c₀` satisfying
  `Covers`, `PairFree`, `NoCrossFour`, `NoBadFour`, plus two density statements about `leftover c₀`.
  `PackFamily` asks for strictly less: a set of edge-disjoint triangles with a centre and two
  colours each, a local condition on the covered edges, and a price.  **No admissibility
  assumption of any kind.**  The two things the papers get by analysis — the hypergraph matching
  itself (Rödl nibble) and the bound `D = O(n^{1-δ})` on its output — are the whole content of
  `PackFamily`.
-/

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

namespace JSP140

attribute [local instance] Classical.propDecidable

variable {n k m : ℕ}

/-! ### §1 — the leftover graph of a packing -/

/-- **THE LEFTOVER GRAPH OF A PACKING.**  The edges of `K_n` which lie in no block of `C`: the edges
the hypergraph matching of arXiv:2208.12563 §4 does not cover, and the graph that the second stage
of arXiv:2207.02920 §12 has to colour with `o(n)` extra colours.  It is **nonempty** in general —
the published construction only covers `1 - n^{-δ}` of the edges — and it is `∅` exactly for a
Steiner triple system (`TwoOne.decomposition_empty`). -/
noncomputable def PackL {n k m : ℕ} (C : TwoOne n k m) : Finset (Sym2 (Verts n)) :=
  edgeFinset (Finset.univ : Finset (Verts n))
    \ (Finset.univ : Finset (Fin m)).biUnion fun i => edgeFinset (C.bl i)

@[simp] theorem mem_PackL {n k m : ℕ} (C : TwoOne n k m) (e : Sym2 (Verts n)) :
    e ∈ PackL C ↔ e ∈ edgeFinset (Finset.univ : Finset (Verts n)) ∧
      ∀ i : Fin m, e ∉ edgeFinset (C.bl i) := by
  rw [PackL, Finset.mem_sdiff, Finset.mem_biUnion]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun i hi => h2 ⟨i, Finset.mem_univ i, hi⟩⟩
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun h => ?_⟩
    obtain ⟨i, hi, hmem⟩ := h
    exact h2 i hmem

/-- **AN EDGE OF A BLOCK IS COVERED, NOT LEFTOVER.** -/
theorem TwoOne.not_mem_PackL {n k m : ℕ} (C : TwoOne n k m) {i : Fin m} {e : Sym2 (Verts n)}
    (he : e ∈ edgeFinset (C.bl i)) : e ∉ PackL C := by
  rw [mem_PackL]
  exact fun h => h.2 i he

/-- A leftover edge is an edge, i.e. has two distinct endpoints. -/
theorem PackL.offDiag {n k m : ℕ} (C : TwoOne n k m) {e : Sym2 (Verts n)} (he : e ∈ PackL C) :
    OffDiag e := (mem_edgeFinset.mp ((mem_PackL C e).mp he).1).2

theorem PackL.subset_univ {n k m : ℕ} (C : TwoOne n k m) :
    PackL C ⊆ edgeFinset (Finset.univ : Finset (Verts n)) :=
  fun _ he => ((mem_PackL C _).mp he).1

/-! ### §2 — the census of a partial packing -/

/-- A block spans three edges. -/
theorem TwoOne.card_blEdge {n k m : ℕ} (C : TwoOne n k m) (i : Fin m) :
    (edgeFinset (C.bl i)).card = 3 := by
  rw [card_edgeFinset, C.card_three i]
  decide

/-- The set of edges spanned by the blocks of `C`. -/
noncomputable def PackEdges {n k m : ℕ} (C : TwoOne n k m) : Finset (Sym2 (Verts n)) :=
  (Finset.univ : Finset (Fin m)).biUnion fun i => edgeFinset (C.bl i)

/-- The cardinality formula for a **disjoint** union of finsets. -/
private theorem card_biUnion_eq {n m : ℕ} (f : Fin n → Finset (Sym2 (Verts m)))
    (hpd : ∀ i j : Fin n, i ≠ j → ∀ e, e ∈ f i → e ∈ f j → False) :
    ∀ s : Finset (Fin n), (s.biUnion f).card = ∑ i ∈ s, (f i).card := by
  intro s
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      have hbi : (insert a s).biUnion f = f a ∪ s.biUnion f := by
        ext e
        rw [Finset.mem_biUnion, Finset.mem_union, Finset.mem_biUnion]
        constructor
        · rintro ⟨b, hb, he⟩
          rcases Finset.mem_insert.mp hb with rfl | hb
          · exact Or.inl he
          · exact Or.inr ⟨b, hb, he⟩
        · intro he
          rcases he with he | ⟨b, hb, he⟩
          · exact ⟨a, Finset.mem_insert_self a s, he⟩
          · exact ⟨b, Finset.mem_insert_of_mem hb, he⟩
      have hinter : f a ∩ s.biUnion f = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro e he
        rcases Finset.mem_inter.mp he with ⟨he1, he2⟩
        obtain ⟨b, hb, he3⟩ := Finset.mem_biUnion.mp he2
        exact hpd a b (fun h => ha (h ▸ hb)) e he1 he3
      have h1 := Finset.card_union_add_card_inter (f a) (s.biUnion f)
      rw [hinter, Finset.card_empty, add_zero] at h1
      rw [hbi, h1, Finset.sum_insert ha, ih]

/-- **THE BLOCKS OF `C` SPAN EXACTLY `3 * m` EDGES.**  They are edge-disjoint (`uniq`), so the
disjoint-union formula applies. -/
theorem Pack.blocks_card {n k m : ℕ} (C : TwoOne n k m) : (PackEdges C).card = 3 * m := by
  have hpd : ∀ i j : Fin m, i ≠ j → ∀ e, e ∈ edgeFinset (C.bl i) →
      e ∈ edgeFinset (C.bl j) → False :=
    fun i j hij e he1 he2 => hij (C.uniq e i j he1 he2)
  show ((Finset.univ : Finset (Fin m)).biUnion fun i => edgeFinset (C.bl i)).card = 3 * m
  calc ((Finset.univ : Finset (Fin m)).biUnion fun i => edgeFinset (C.bl i)).card
      = ∑ i ∈ (Finset.univ : Finset (Fin m)), (edgeFinset (C.bl i)).card :=
        card_biUnion_eq _ hpd _
    _ = ∑ _i ∈ (Finset.univ : Finset (Fin m)), ((3 : ℕ)) := by
        rw [Finset.sum_congr rfl (fun i _ => TwoOne.card_blEdge C i)]
    _ = 3 * m := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, Nat.nsmul_eq_mul]
        exact Nat.mul_comm m 3

/-- The spanned edges are edges of `K_n`. -/
theorem PackEdges.subset_univ {n k m : ℕ} (C : TwoOne n k m) :
    PackEdges C ⊆ edgeFinset (Finset.univ : Finset (Verts n)) := by
  intro e he
  obtain ⟨i, -, hei⟩ := Finset.mem_biUnion.mp he
  exact mem_edgeFinset.mpr ⟨Finset.mem_sym2_iff.mpr fun a _ => Finset.mem_univ a,
    (mem_edgeFinset.mp hei).2⟩

/-- **`PackL C` IS THE COMPLEMENT OF THE SPANNED EDGES.** -/
theorem packL_eq_sdiff {n k m : ℕ} (C : TwoOne n k m) :
    PackL C = edgeFinset (Finset.univ : Finset (Verts n)) \ PackEdges C := rfl

/-- **THE CENSUS OF A PACKING: `6 * m + 2 * |PackL C| = n * (n - 1)`.**  The blocks cover `3 * m`
edges and the leftover graph holds the rest of the `n * (n-1) / 2` edges of `K_n`.  For a Steiner
triple system (`6 * m = n * (n-1)`) the leftover graph is empty (`TwoOne.decomposition_empty`):
that is the shape rounds 49–56 worked with, and it is the shape of arXiv:2207.02920 §4 *only up
to `n^{-δ}`*. -/
theorem Pack.census {n k m : ℕ} (C : TwoOne n k m) :
    6 * m + 2 * (PackL C).card = n * (n - 1) := by
  have h1 := Finset.card_sdiff_add_card_eq_card (s := PackEdges C)
    (t := edgeFinset (Finset.univ : Finset (Verts n))) (PackEdges.subset_univ C)
  rw [← packL_eq_sdiff] at h1
  have h2 := card_edgeFinset_univ_two n
  have h3 := Pack.blocks_card C
  omega

/-- The packing cannot span more than `E(K_n)`. -/
theorem Pack.card_le {n k m : ℕ} (C : TwoOne n k m) : 6 * m ≤ n * (n - 1) := by
  have h := Pack.census C
  omega

/-- **A STEINER TRIPLE SYSTEM HAS NO LEFTOVER EDGES.**  `6 * m = n * (n - 1)` is the *decomposition*
case of `Pack.census`; the published construction of arXiv:2207.02920 §4 is the inequality
`Pack.blocks_ge` below, not this equality. -/
theorem TwoOne.decomposition_empty {n k m : ℕ} (C : TwoOne n k m)
    (hB : 6 * m = n * (n - 1)) : PackL C = ∅ := by
  have h := Pack.census C
  rw [hB] at h
  have hz : (PackL C).card = 0 := by omega
  exact Finset.card_eq_zero.mp hz

/-- **A SPARSE LEFTOVER GRAPH HAS AT MOST `n * D / 2` EDGES.**  The handshaking lemma applied to
`PackL C`: the leftover degrees sum to twice the number of leftover edges, and each of the `n`
vertices has degree at most `D`.  This is the `O(n^{2-δ})` leftover of arXiv:2207.02920 §4. -/
theorem Pack.card_two_mul_le {n k m : ℕ} (C : TwoOne n k m) {D : ℕ}
    (hD : SparseL (PackL C) D) : 2 * (PackL C).card ≤ n * D := by
  have h1 := sum_DegL_two_mul_card (L := PackL C) (PackL.subset_univ C)
  have h2 : (∑ v : Verts n, DegL (PackL C) v) ≤ n * D := by
    have h2' : (∑ v : Verts n, DegL (PackL C) v) ≤ ∑ _v : Verts n, D :=
      Finset.sum_le_sum fun v _ => hD v
    have h3 : (∑ _v : Verts n, D) = n * D := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      norm_num
    omega
  omega

/-- **THE PACKING COVERS ALL BUT `O(n * D)` EDGES.**  `n * (n-1) ≤ 6 * m + n * D`: with
`D = n^{1-δ}` the packing covers `1 - n^{-δ}` of `E(K_n)`, the coverage of arXiv:2207.02920 §4
and arXiv:2208.12563 §4. -/
theorem Pack.blocks_ge {n k m : ℕ} (C : TwoOne n k m) {D : ℕ}
    (hD : SparseL (PackL C) D) : n * (n - 1) ≤ 6 * m + n * D := by
  have h1 := Pack.census C
  have h2 := Pack.card_two_mul_le C hD
  omega

/-- **THE PRICE OF A PARTIAL PACKING: `6 * k + 5 * D ≥ 5 * (n - 1)`, i.e. `k ≥ 5(n-1)/6 - 5D/6`.**
The partial version of `TwoOne.price` (`5 * m ≤ n * k`: five colour-slots per block of
arXiv:2208.12563 §4).  For `D = 0` this is the sharp constant `5(n-1)/6 ≤ 6k` of rounds 49–56;
for the published `D = n^{1-δ}` it reads `6k ≥ 5(n-1) - 5n^{1-δ}`, i.e.
`k = 5n/6 - o(n)`: the catalog answer, with the *rate* the papers achieve. -/
theorem Pack.price {n k m : ℕ} (C : TwoOne n k m) (hc : Admissible (C.col)) (hn : 4 ≤ n)
    {D : ℕ} (hD : SparseL (PackL C) D) : 6 * k + 5 * D ≥ 5 * (n - 1) := by
  have h1 := C.price hc hn
  have h2 := Pack.census C
  have h3 := Pack.card_two_mul_le C hD
  have h5 : 30 * m ≤ 6 * (n * k) := by
    have h := Nat.mul_le_mul_left 6 h1
    convert h using 1 <;> ring
  have h6 : 5 * (n * (n - 1)) = 30 * m + 10 * (PackL C).card := by
    calc 5 * (n * (n - 1)) = 5 * (6 * m + 2 * (PackL C).card) := by rw [h2]
      _ = 30 * m + 10 * (PackL C).card := by ring
  have h7 : 10 * (PackL C).card ≤ 5 * (n * D) := by
    have h := Nat.mul_le_mul_left 5 h3
    convert h using 1 <;> ring
  have h8 : 5 * (n * (n - 1)) ≤ 6 * (n * k) + 5 * (n * D) := by omega
  have h8' : n * (5 * (n - 1)) ≤ n * (6 * k + 5 * D) := by
    convert h8 using 1 <;> ring
  have h8'' : (5 * (n - 1)) * n ≤ (6 * k + 5 * D) * n := by
    convert h8' using 1 <;> ring
  have h9 : 5 * (n - 1) ≤ 6 * k + 5 * D :=
    Nat.le_of_mul_le_mul_right h8'' (by omega : (0 : ℕ) < n)
  omega

/-! ### §3 — the second stage of a *partial* first stage -/

/-- **THE FIRST-STAGE LOCAL CONDITION (P0).**  For every four-set, the colours on the **covered**
edges, together with half the number of leftover edges (rounded up), reach five.  The `⌈t/2⌉`
is exact: a *proper* fresh colouring gives `⌈t/2⌉` distinct fresh colours on `t` leftover edges of a
four-set, because a colour class is a matching.

This is what the first stage of arXiv:2207.02920 §4 has to deliver — and note that it is **not**
`Admissible c₀`: on the leftover edges the colouring `C.col` carries no information at all, so a
partial packing cannot satisfy `Admissible c₀` and need not. -/
def FirstOk {n k : ℕ} (c₀ : Col n k) (L : Finset (Sym2 (Verts n))) : Prop :=
  ∀ S : Finset (Verts n), S.card = 4 →
    5 ≤ ((edgeFinset S \ L).image c₀).card + (edgeFinset S ∩ L).card / 2

/-- **THE CATALOG CONDITION IMPLIES (P0) FOR A LEFTOVER GRAPH WITH NO EDGE IN ANY FOUR-SET.**
In particular, for an empty leftover graph — a Steiner triple system — (P0) *is* `Admissible`, so
`FirstOk` is the correct generalisation of the catalog condition to a partial first stage: a partial
packing cannot satisfy `Admissible` (its colouring carries arbitrary values on the leftover edges),
and `FirstOk` is the local condition that replaces it. -/
theorem FirstOk.of_admissible {n k : ℕ} (c₀ : Col n k) (hc : Admissible c₀)
    {L : Finset (Sym2 (Verts n))} (hL : ∀ S : Finset (Verts n), S.card = 4 →
      (edgeFinset S ∩ L).card = 0) : FirstOk c₀ L := by
  intro S hS
  have h5 : 5 ≤ (colorsOn c₀ S).card := hc S hS
  have hsplit : edgeFinset S = (edgeFinset S \ L) ∪ (edgeFinset S ∩ L) := by
    ext e
    rw [Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter]
    tauto
  have hcard : (colorsOn c₀ S).card
      ≤ ((edgeFinset S \ L).image c₀).card + (edgeFinset S ∩ L).card := by
    have himg : ((edgeFinset S).image c₀)
        = ((edgeFinset S \ L).image c₀) ∪ ((edgeFinset S ∩ L).image c₀) :=
      (congrArg (fun t : Finset (Sym2 (Verts n)) => t.image c₀) hsplit).trans
        (Finset.image_union _ _)
    calc (colorsOn c₀ S).card
        = (((edgeFinset S \ L).image c₀) ∪ ((edgeFinset S ∩ L).image c₀)).card := by
          rw [colorsOn]
          exact congrArg (fun t : Finset (Fin k) => t.card) himg
      _ ≤ ((edgeFinset S \ L).image c₀).card + ((edgeFinset S ∩ L).image c₀).card :=
          Finset.card_union_le _ _
      _ ≤ ((edgeFinset S \ L).image c₀).card + (edgeFinset S ∩ L).card :=
          Nat.add_le_add_left Finset.card_image_le _
  have hle : (edgeFinset S ∩ L).card / 2 = (edgeFinset S ∩ L).card := by
    have h := hL S hS
    omega
  omega

/-- **(P0) FOR THE LEFTOVER GRAPH OF A PACKING, IN THE FULLY-COVERED CASE.**  For the Steiner triple
systems of `Block.lean` the first-stage condition of the published construction is the catalog
condition. -/
theorem FirstOk.of_decomposition {n k m : ℕ} (C : TwoOne n k m) (hc : Admissible (C.col))
    (hB : 6 * m = n * (n - 1)) : FirstOk (C.col) (PackL C) := by
  rw [TwoOne.decomposition_empty C hB]
  exact FirstOk.of_admissible (C.col) hc (fun _ _ => by simp)

/-- Three distinct elements of a finset of cardinality at least three. -/
private theorem exists_three {a : Type*} [DecidableEq a] {s : Finset a} (h : 3 ≤ s.card) :
    ∃ x y z : a, x ∈ s ∧ y ∈ s ∧ z ∈ s ∧ x ≠ y ∧ x ≠ z ∧ y ≠ z := by
  have hne : s.Nonempty := by
    by_contra hc
    have hz : s.card = 0 := Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hc)
    omega
  obtain ⟨x, hx⟩ := hne
  have hne' : s.erase x |>.Nonempty := by
    by_contra hc
    have h1 : (s.erase x).card = 0 :=
      Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hc)
    have h2 : (s.erase x).card = s.card - 1 := Finset.card_erase_of_mem hx
    omega
  obtain ⟨y, hy⟩ := hne'
  have hne'' : (s.erase x).erase y |>.Nonempty := by
    by_contra hc
    have h1 : ((s.erase x).erase y).card = 0 :=
      Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hc)
    have h2 : ((s.erase x).erase y).card = (s.erase x).card - 1 := Finset.card_erase_of_mem hy
    have h3 : (s.erase x).card = s.card - 1 := Finset.card_erase_of_mem hx
    omega
  obtain ⟨z, hz⟩ := hne''
  have hyx : y ∈ s.erase x := hy
  have hzx : z ∈ s.erase x := Finset.mem_of_mem_erase hz
  have hy_s : y ∈ s := Finset.mem_of_mem_erase hy
  have hz_s : z ∈ s := Finset.mem_of_mem_erase hzx
  refine ⟨x, y, z, hx, hy_s, hz_s, ?_, ?_, ?_⟩
  · rintro rfl
    exact (Finset.mem_erase.mp hyx).1 rfl
  · rintro rfl
    exact (Finset.mem_erase.mp hzx).1 rfl
  · rintro rfl
    exact (Finset.mem_erase.mp hz).1 rfl

/-- **THREE VERTEX-DISJOVER EDGES OF A FOUR-SET DO NOT EXIST.**  So a set of pairwise vertex-disjoint
edges of `K₄` has at most two elements — the fact that makes `⌈t/2⌉` the right count of fresh
colours on the `t` leftover edges of a four-set. -/
private theorem disjoint_card_le_two {n : ℕ} {S : Finset (Verts n)} {T : Finset (Sym2 (Verts n))}
    (hS : S.card = 4) (hT : T ⊆ edgeFinset S)
    (hd : ∀ e e' : Sym2 (Verts n), e ∈ T → e' ∈ T → e ≠ e' → ¬ Shares e e') :
    T.card ≤ 2 := by
  by_contra hbig
  have h3 : 3 ≤ T.card := by omega
  obtain ⟨e₁, e₂, e₃, he₁, he₂, he₃, hne12, hne13, hne23⟩ := exists_three h3
  obtain ⟨a₁, b₁, rfl⟩ : ∃ x y : Verts n, e₁ = s(x, y) :=
    Quot.inductionOn e₁ (fun p : Verts n × Verts n => ⟨p.1, p.2, rfl⟩)
  obtain ⟨a₂, b₂, rfl⟩ : ∃ x y : Verts n, e₂ = s(x, y) :=
    Quot.inductionOn e₂ (fun p : Verts n × Verts n => ⟨p.1, p.2, rfl⟩)
  obtain ⟨a₃, b₃, rfl⟩ : ∃ x y : Verts n, e₃ = s(x, y) :=
    Quot.inductionOn e₃ (fun p : Verts n × Verts n => ⟨p.1, p.2, rfl⟩)
  have hne1 : a₁ ≠ b₁ := offDiag_iff.mp (mem_edgeFinset.mp (hT he₁)).2
  have hne2 : a₂ ≠ b₂ := offDiag_iff.mp (mem_edgeFinset.mp (hT he₂)).2
  have hne3 : a₃ ≠ b₃ := offDiag_iff.mp (mem_edgeFinset.mp (hT he₃)).2
  have hno12 : ∀ x : Verts n, x ∈ s(a₁, b₁) → x ∈ s(a₂, b₂) → False := by
    intro x h1 h2
    exact hd _ _ he₁ he₂ hne12 ⟨x, h1, h2⟩
  have hno13 : ∀ x : Verts n, x ∈ s(a₁, b₁) → x ∈ s(a₃, b₃) → False := by
    intro x h1 h2
    exact hd _ _ he₁ he₃ hne13 ⟨x, h1, h2⟩
  have hno23 : ∀ x : Verts n, x ∈ s(a₂, b₂) → x ∈ s(a₃, b₃) → False := by
    intro x h1 h2
    exact hd _ _ he₂ he₃ hne23 ⟨x, h1, h2⟩
  have hne12a : a₁ ≠ a₂ := fun h => hno12 a₁ (by simp) (by simp [h])
  have hne12b : a₁ ≠ b₂ := fun h => hno12 a₁ (by simp) (by simp [h])
  have hne12c : b₁ ≠ a₂ := fun h => hno12 b₁ (by simp) (by simp [h])
  have hne12d : b₁ ≠ b₂ := fun h => hno12 b₁ (by simp) (by simp [h])
  have hne13a : a₁ ≠ a₃ := fun h => hno13 a₁ (by simp) (by simp [h])
  have hne13b : a₁ ≠ b₃ := fun h => hno13 a₁ (by simp) (by simp [h])
  have hne13c : b₁ ≠ a₃ := fun h => hno13 b₁ (by simp) (by simp [h])
  have hne13d : b₁ ≠ b₃ := fun h => hno13 b₁ (by simp) (by simp [h])
  have hne23a : a₂ ≠ a₃ := fun h => hno23 a₂ (by simp) (by simp [h])
  have hne23b : a₂ ≠ b₃ := fun h => hno23 a₂ (by simp) (by simp [h])
  have hne23c : b₂ ≠ a₃ := fun h => hno23 b₂ (by simp) (by simp [h])
  have hne23d : b₂ ≠ b₃ := fun h => hno23 b₂ (by simp) (by simp [h])
  have hmem1 : a₁ ∈ S ∧ b₁ ∈ S :=
    Finset.mk_mem_sym2_iff.mp (mem_edgeFinset.mp (hT he₁)).1
  have hmem2 : a₂ ∈ S ∧ b₂ ∈ S :=
    Finset.mk_mem_sym2_iff.mp (mem_edgeFinset.mp (hT he₂)).1
  have hmem3 : a₃ ∈ S ∧ b₃ ∈ S :=
    Finset.mk_mem_sym2_iff.mp (mem_edgeFinset.mp (hT he₃)).1
  have hcard : 6 = (insert a₁ (insert b₁ (insert a₂ (insert b₂ (insert a₃ (insert b₃ ∅))))) : Finset (Verts n)).card := by
    rw [Finset.card_insert_of_notMem (by simp [hne1, hne2, hne3, hne12a, hne12b, hne12c, hne12d, hne13a, hne13b, hne13c, hne13d, hne23a, hne23b, hne23c, hne23d]),
      Finset.card_insert_of_notMem (by simp [hne1, hne2, hne3, hne12a, hne12b, hne12c, hne12d, hne13a, hne13b, hne13c, hne13d, hne23a, hne23b, hne23c, hne23d]),
      Finset.card_insert_of_notMem (by simp [hne1, hne2, hne3, hne12a, hne12b, hne12c, hne12d, hne13a, hne13b, hne13c, hne13d, hne23a, hne23b, hne23c, hne23d]),
      Finset.card_insert_of_notMem (by simp [hne1, hne2, hne3, hne12a, hne12b, hne12c, hne12d, hne13a, hne13b, hne13c, hne13d, hne23a, hne23b, hne23c, hne23d]),
      Finset.card_insert_of_notMem (by simp [hne1, hne2, hne3, hne12a, hne12b, hne12c, hne12d, hne13a, hne13b, hne13c, hne13d, hne23a, hne23b, hne23c, hne23d]),
      Finset.card_insert_of_notMem (by simp [hne1, hne2, hne3, hne12a, hne12b, hne12c, hne12d, hne13a, hne13b, hne13c, hne13d, hne23a, hne23b, hne23c, hne23d])]
    simp [hne1, hne2]
  have hsub : (insert a₁ (insert b₁ (insert a₂ (insert b₂ (insert a₃ (insert b₃ ∅))))) : Finset (Verts n)) ⊆ S := by
    intro x hx
    simp only [Finset.mem_insert] at hx
    rcases hx with h | hx
    · rw [h]; exact hmem1.1
    rcases hx with h | hx
    · rw [h]; exact hmem1.2
    rcases hx with h | hx
    · rw [h]; exact hmem2.1
    rcases hx with h | hx
    · rw [h]; exact hmem2.2
    rcases hx with h | hx
    · rw [h]; exact hmem3.1
    rcases hx with h | hx
    · rw [h]; exact hmem3.2
    · exact absurd hx (by simp)
  have hle := Finset.card_le_card hsub
  omega

/-- **THE PIGEONHOLE PRINCIPLE, IN THE FORM USED HERE.**  If every colour fibre of `f` on `s` has at
most `M` elements then `|s| ≤ M · |image f|`. -/
private theorem pigeonhole {a b : Type*} [DecidableEq a] [DecidableEq b] (f : a → b) (s : Finset a)
    (M : ℕ) (h : ∀ y ∈ s.image f, (s.filter fun x => f x = y).card ≤ M) :
    s.card ≤ M * (s.image f).card := by
  have h1 : s.card ≤ ∑ y ∈ s.image f, M := by
    refine (Finset.card_eq_sum_card_image f s).le.trans ?_
    exact Finset.sum_le_sum fun y hy => h y hy
  calc s.card ≤ ∑ y ∈ s.image f, M := h1
    _ = M * (s.image f).card := by rw [Finset.sum_const, Nat.nsmul_eq_mul, Nat.mul_comm]

/-- **A PROPER COLOURING GIVES `⌈t/2⌉` DISTINCT COLOURS ON THE `t` LEFTOVER EDGES OF A FOUR-SET.**
The pigeonhole principle, with the fibre bound of `disjoint_card_le_two`: two leftover edges of the
same fresh colour cannot share a vertex (`Proper`), so a fibre of the colour map on the leftover
edges of a four-set is a set of pairwise vertex-disjoint edges of `K₄` and has at most two
elements.  So a proper second stage pays for `⌈t/2⌉` of the `t` leftover edges of a four-set, and
`FirstOk` is exactly the condition that pays for the rest. -/
theorem Pack.fresh_colours {n k : ℕ} {c : Col n k} {L : Finset (Sym2 (Verts n))} (hP : Proper c L)
    {S : Finset (Verts n)} (hS : S.card = 4) :
    (edgeFinset S ∩ L).card / 2 ≤ ((edgeFinset S ∩ L).image c).card := by
  have key : ∀ (t : Finset (Sym2 (Verts n))), t ⊆ edgeFinset S → t ⊆ L →
      t.card / 2 ≤ (t.image c).card := by
    intro t htS htL
    have hfib : ∀ y, (t.filter (fun e => c e = y)).card ≤ 2 := by
      intro y
      by_contra hbig
      have h3 : 3 ≤ (t.filter (fun e => c e = y)).card := by omega
      obtain ⟨e₁, e₂, e₃, he₁, he₂, he₃, hne12, hne13, hne23⟩ := exists_three h3
      have hsubF : t.filter (fun e => c e = y) ⊆ L := by
        intro e he
        exact htL ((Finset.mem_filter.mp he).1)
      have hsubF' : t.filter (fun e => c e = y) ⊆ edgeFinset S := by
        intro e he
        exact htS ((Finset.mem_filter.mp he).1)
      have hdisj : ∀ e e' : Sym2 (Verts n), e ∈ t.filter (fun e => c e = y) →
          e' ∈ t.filter (fun e => c e = y) → e ≠ e' → ¬ Shares e e' := by
        intro e e' he he' hne hsh
        obtain ⟨het, hec⟩ := Finset.mem_filter.mp he
        obtain ⟨he't, he'c⟩ := Finset.mem_filter.mp he'
        exact hP e (htL het) e' (htL he't) hne hsh (hec.trans he'c.symm)
      have hle2 := disjoint_card_le_two (T := t.filter (fun e => c e = y)) hS hsubF' hdisj
      exact absurd hle2 hbig
    have h1 : t.card ≤ 2 * (t.image c).card := pigeonhole c t 2 fun y _ => hfib y
    have hd0 := Nat.div_mul_le_self t.card 2
    have hd : 2 * (t.card / 2) ≤ t.card := by omega
    have hm : 2 * (t.card / 2) ≤ 2 * (t.image c).card := hd.trans h1
    exact Nat.le_of_mul_le_mul_left hm (by omega : (0 : ℕ) < 2)
  exact key _ Finset.inter_subset_left Finset.inter_subset_right

/-- **THE SECOND STAGE OF A PARTIAL FIRST STAGE — NO ADMISSIBILITY ASSUMPTION.**
`FirstOk (C.col) (PackL C)` together with a leftover of maximum degree `D` gives an **admissible**
`k + 2 * D + 1` colouring of `K_n`.  The `2D + 1` fresh colours are the greedy ones of
`proper_of_sparseL`: the deterministic half of arXiv:2207.02920 §12 / arXiv:2208.12563 §4 (the bad
events `A_{e,f,i}` = `B₁` are excluded greedily, with `O(n^{1-δ})` extra colours). -/
theorem Pack.second_stage {n k m D : ℕ} (C : TwoOne n k m) (hF : FirstOk (C.col) (PackL C))
    (hD : SparseL (PackL C) D) : ∃ (c : Col n (k + (2 * D + 1))), Admissible c := by
  obtain ⟨g, hg⟩ := proper_of_sparseL hD
  refine ⟨extendColDep (C.col) (PackL C) fun e h => g ⟨e, h⟩, ?_⟩
  have hE : Extends (liftCol (C.col) (Nat.le_add_right k (2 * D + 1)))
      (extendColDep (C.col) (PackL C) fun e h => g ⟨e, h⟩) (PackL C) := by
    exact Extends_extendColDep
  have hProper : Proper (extendColDep (C.col) (PackL C) fun e h => g ⟨e, h⟩) (PackL C) := by
    intro e he e' he' hne hsh
    rw [extendColDep_of_mem he, extendColDep_of_mem he']
    intro hcon
    apply hg ⟨e, he⟩ ⟨e', he'⟩ (fun hv => hne (congrArg Subtype.val hv)) hsh
    exact freshCol_inj _ _ hcon
  refine (admissible_iff_second_stage hE).mpr ?_
  intro S hS
  have h1 := Pack.fresh_colours hProper hS
  have h2 := hF S hS
  have h3 : ((edgeFinset S \ PackL C).image (C.col)).card
      ≤ ((edgeFinset S \ PackL C).image
        (liftCol (k' := k) (k := k + (2 * D + 1)) (C.col) (Nat.le_add_right k (2 * D + 1)))).card := by
    have himg : ((edgeFinset S \ PackL C).image (liftCol (k' := k) (k := k + (2 * D + 1)) (C.col) (Nat.le_add_right k (2 * D + 1))))
        = ((edgeFinset S \ PackL C).image (C.col)).image
          (fun j : Fin k => (⟨j.val, by omega⟩ : Fin (k + (2 * D + 1)))) := by
      ext y
      simp only [Finset.mem_image]
      constructor
      · rintro ⟨e, he, heq⟩
        refine ⟨(C.col e), ⟨e, he, rfl⟩, ?_⟩
        exact heq
      · rintro ⟨j, hj, heq⟩
        obtain ⟨e, he, hejc⟩ := hj
        refine ⟨e, he, ?_⟩
        calc (liftCol (k' := k) (k := k + (2 * D + 1)) (C.col) (Nat.le_add_right k (2 * D + 1))) e = (⟨(C.col e).val, by omega⟩ : Fin (k + (2 * D + 1))) := rfl
          _ = (⟨j.val, by omega⟩ : Fin (k + (2 * D + 1))) :=
              congrArg (fun z : Fin k => (⟨z.val, by omega⟩ : Fin (k + (2 * D + 1)))) hejc
          _ = y := heq
    rw [himg]
    have hf : Function.Injective (fun j : Fin k =>
        (⟨j.val, by omega⟩ : Fin (k + (2 * D + 1)))) := by
      intro a b hab
      exact (Fin.val_inj).mp (by simpa using hab)
    rw [Finset.card_image_iff.mpr (fun _ _ _ _ hab => hf hab)]
  omega

/-- **THE PALETTE OF THE TWO STAGES: `EG n ≤ k + 2 * D + 1`.** -/
theorem Pack.eg_le {n k m D : ℕ} (C : TwoOne n k m) (hF : FirstOk (C.col) (PackL C))
    (hD : SparseL (PackL C) D) : EG n ≤ k + 2 * D + 1 := by
  obtain ⟨c, hc⟩ := Pack.second_stage C hF hD
  exact EG_le n (k + (2 * D + 1)) c hc

/-! ### §4 — the prize hypothesis in design language -/

/-- **THE HYPOTHESIS OF THE PUBLISHED FIRST STAGE, IN DESIGN LANGUAGE.**

For every `ε' > 0` there is `N` such that every `n ≥ N` carries a **packing of edge-disjoint
triangles** `C : TwoOne n k₁ m` — a centre and two distinct colours per block — whose leftover
graph has maximum degree `D` (a constant in `n`), which satisfies the first-stage local condition
`FirstOk`, and which is priced by `6 * (k₁ + 2D + 1) ≤ 5 * (n-1) + ε' * n`.

This is weaker than round 33's `CrossStageFamily` in every respect that matters: there is **no
admissible colouring** among the hypotheses (not even `Admissible c₀`), no `Covers`, no `PairFree`,
no `NoCrossFour`, no `NoBadFour`, no `Tile`, no `Packed`, no `LeafClosed` and no second stage — all of
those are consequences of the local condition, and the second stage is built here
(`Pack.second_stage`).  What is left is the hypergraph matching of arXiv:2208.12563 §4 together
with the bound `D = O(n^{1-δ})` on its own output. -/
def PackFamily : Prop :=
  ∀ ε' : ℝ, 0 < ε' → ∃ N D : ℕ, ∀ n : ℕ, N ≤ n →
    ∃ (k₁ m : ℕ) (C : TwoOne n k₁ m),
      SparseL (PackL C) D ∧ FirstOk (C.col) (PackL C) ∧
        (6 : ℝ) * ((k₁ + (2 * D + 1) : ℕ) : ℝ) ≤ 5 * ((n - 1 : ℕ) : ℝ) + ε' * (n : ℝ)

/-- **THE UPPER HALF OF THE HEADLINE, FROM THE DESIGN HYPOTHESIS.** -/
theorem Pack.fiveSixthUpper_of_packFamily (h : PackFamily) : FiveSixthUpper EG := by
  intro ε hε
  obtain ⟨N, D, hN⟩ := h (6 * ε) (by positivity)
  refine ⟨max N 1, fun n hn => ?_⟩
  have hN' : N ≤ n := Nat.le_trans (Nat.le_max_left _ _) hn
  have h1 : 1 ≤ n := Nat.le_trans (Nat.le_max_right _ _) hn
  obtain ⟨k₁, m, C, hD, hF, hk⟩ := hN n hN'
  have heg : EG n ≤ k₁ + 2 * D + 1 := Pack.eg_le C hF hD
  have hcast : (EG n : ℝ) ≤ ((k₁ + 2 * D + 1 : ℕ) : ℝ) := by exact_mod_cast heg
  have hsub : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub h1, Nat.cast_one]
  rw [hsub] at hk
  have hexp : ((k₁ + 2 * D + 1 : ℕ) : ℝ) = (k₁ : ℝ) + 2 * (D : ℝ) + 1 := by
    push_cast
    ring
  have hexp' : ((k₁ + (2 * D + 1) : ℕ) : ℝ) = (k₁ : ℝ) + 2 * (D : ℝ) + 1 := by
    push_cast
    ring
  rw [hexp] at hcast
  rw [hexp'] at hk
  have hn' : (0 : ℝ) ≤ (n : ℝ) := by positivity
  nlinarith [hk, hn']

/-- **THE REQUIRED STATEMENT FROM THE DESIGN HYPOTHESIS: `PackFamily → jsp_000140_target`.**
The lower half is `Main.fiveSixthLower_eg`; the upper half is
`Pack.fiveSixthUpper_of_packFamily`. -/
theorem Pack.target_of_packFamily (h : PackFamily) : jsp_000140_target :=
  fiveSixth_iff.mpr ⟨fiveSixthLower_eg, Pack.fiveSixthUpper_of_packFamily h⟩

end JSP140
