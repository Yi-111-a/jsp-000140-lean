import JSPProblem.Cross

/-!
# JSP-000140 — the *first* stage, its density content, and the price of a deterministic second
# stage

Rounds 30–34 removed every probabilistic object from the **second** stage of the published
construction: after round 34 the only thing left to prove is the existence of a first stage together
with two counting statements about its own output —

* `SparseL (leftover c₀) D`, the maximum degree of the leftover graph (`D = n^{1-δ}`), and
* `CrossThin c₀ (leftover c₀) T`, the number of crossing pairs over a phase-1 monochromatic pair.

This file does four things with them.

## 1. The first stage is a **linear triple system**, and its density is a **per-vertex** condition

The first stage of arXiv:2208.12563 §4 is a family of triangles of `K_n`, edge-disjoint, one colour
per triangle, with the `(vertex, colour)` pairs of distinct triangles disjoint.  Abstracting away the
colours, that is a family `Tris` of three-element vertex sets which is **linear** (two of them share
at most one vertex).  For such a family:

* `card_covTris` — the vertices covered at `v` number `2 · degTris v`, where `degTris v` is the
  number of triples through `v` (linearity is exactly what makes the contributions disjoint);
* `sum_degTris` — `∑_v degTris v = 3 · |Tris|`, the counting identity behind every bound on the
  number of triangles;
* `deg_le` — `2 · degTris v ≤ n - 1`, so `degTris v ≤ (n-1)/2` and `|Tris| ≤ n(n-1)/6`: the Steiner
  bound;
* `card_leftover_le_of_SparseL` — a leftover graph of maximum degree `D` has at most `nD` edges, the
  *total* form of the density statement (the shape a first-moment argument produces);

* **`SparseL_iff_degTris` — THE FIRST-STAGE DENSITY LEMMA.**  The leftover graph of the triple system
  has maximum degree at most `D`

      `⟺  2 · degTris v ≥ n - 1 - D` for every vertex v`.

  This is the precise, purely combinatorial form of the "maximum degree `D = n^{1-δ}`" statement of
  arXiv:2208.12563 §4 (IV) / arXiv:2207.02920 Claim 4: **the first stage must pass through every
  vertex at least `⌈(n-1-D)/2⌉` times.**  It is a *uniform* condition, and §3 below shows that the
  uniform form is what the budget consumes.

## 2. **THE PRICE OF A DETERMINISTIC SECOND STAGE** — the headline of this round

A first stage with leftover degree `D` uses at least `5(n-1-D)/6` colours (`FirstStageCounting`; the
formalisation of the slot count is the next concrete lemma of round 36, and the verdicts below do
not depend on its details).  `budget_leftover` then says that the budget of the catalog answer,
`6(k + fresh) ≤ 5(n-1) + δn`, leaves

    `6 · fresh ≤ 5D + δn`

for the second stage.  Everything else is a corollary of this one accounting identity:

* **`proper_fits`** — the published second stage, i.e. round 31's greedy properness with
  `fresh = 2D + 1` (the colours of arXiv:2208.12563 §4), fits the remaining budget whenever
  `7D + 6 ≤ δn`; for `D = n^{1-δ}` this holds for all large `n`.  **The published second stage is
  payable, and the local lemma is not needed for it.**
* **`deterministic_budget_strong` / `deterministic_budget`** — the deterministic second stage of
  rounds 33/34, which also excludes the bad events `B₂` and `B₃` and costs
  `fresh = 2D² + 2D + T + 1`, gives

      `12 D² + 7D + 6T + 6 ≤ δn`,   in particular   **`12 D² ≤ δn`**,

  i.e. it needs `D = O(√(δn)) = o(√n)`.  For the published `D = n^{1-δ}` and `δ < 1/2` the
  inequality `12 n^{2-2δ} ≤ δn` is *false for all large `n`*.
* **`deterministic_imp_proper`** — whenever the round-33/34 budget holds, the published condition
  `7D + 6 ≤ δn` holds as well, and **`deterministic_ne_proper`** says the converse fails.  The two
  budgets are strictly ordered: rounds 33 and 34 bought a strictly more expensive way of spending
  the same budget, and the extra price is unbounded as `δ → 0`.

**This retires a whole attack family.**  The "honest price" of rounds 33 and 34 was written down as
prose ("the `2D²` is affordable only for `D = o(√n)`, i.e. `δ > 1/2` in the papers' notation").  It
is now `deterministic_budget`, a theorem.  Consequently the local lemma is *not* optional for `B₂`,
`B₃`: the only way to pay for them at `D = n^{1-δ}` is a probabilistic argument of the strength of
the symmetric local lemma.  **The next attack family must have an `o(n)` fresh-colour cost which is
not quadratic in `D`.**

## 3. The interface of round 34 is **vacuous**, and the corrected one

`CrossStageFamily` asserts `Covers c₀` — the *complete* covering of round 29 — together with
`SparseL` and `CrossThin` on `leftover c₀`.  But `Covers c₀ ↔ leftover c₀ = ∅`
(`covers_iff_leftover_eq_empty`), so

* **`crossStageFamily_tri`, `crossStageFamily_of_tri`, `crossStageFamily_iff_triFamily`** —
  `CrossStageFamily ↔ TriFamily`.

The whole second stage of rounds 33/34 is therefore **dead code with respect to the remaining
hypothesis**: with `D = T = 0` the fresh-colour cost is `1`, and the family is nothing but round
29's `TriFamily`.  `PartialStageFamily` is the corrected interface: the first stage may leave `o(n²)`
edges uncovered, the four local conditions and the leaf closure are hypotheses (they are Phase-1
output in arXiv:2207.02920, and `tile_of_tri` / `leafClosed_of_tri` need the *complete* covering), and
the two density statements `SparseL`, `CrossThin` are genuinely non-vacuous.
`crossStageFamily_partial` shows the corrected interface is at least as general as round 34's, and
`leftover_card_le` records *why* a total bound is not enough: `AlmostCovers c (n·n)` holds for every
colouring, so the per-vertex form of §1 is the real content.
-/

set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

namespace JSP140

attribute [local instance] Classical.propDecidable

variable {n k : ℕ}

/-! ### 0. The leftover graph, vertex by vertex -/

/-- **The neighbours of `v` in a leftover graph `L`.** -/
noncomputable def nbrsL {n : ℕ} (L : Finset (Sym2 (Verts n))) (v : Verts n) : Finset (Verts n) :=
  (Finset.univ : Finset (Verts n)).filter (fun x => x ≠ v ∧ s(v, x) ∈ L)

@[simp] theorem mem_nbrsL {n : ℕ} {L : Finset (Sym2 (Verts n))} {v x : Verts n} :
    x ∈ nbrsL L v ↔ x ≠ v ∧ s(v, x) ∈ L := by
  unfold nbrsL
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

/-- **THE DEGREE OF A LEFTOVER GRAPH AT A VERTEX, AS A NEIGHBOUR SET.**  `DegL` counts the leftover
*edges* through `v`; `nbrsL` counts the leftover *vertices* at `v`.  For a graph of edges of `K_n`
the two agree. -/
theorem degL_eq_card_nbrsL {n : ℕ} {L : Finset (Sym2 (Verts n))}
    (hL : L ⊆ edgeFinset (Finset.univ : Finset (Verts n))) (v : Verts n) :
    DegL L v = (nbrsL L v).card := by
  have key : ∀ e : Sym2 (Verts n), e ∈ L.filter (fun e => v ∈ e) → ∃ x : Verts n, e = s(v, x) ∧
      x ∈ nbrsL L v := by
    intro e he
    obtain ⟨a, b, hab⟩ : ∃ a b : Verts n, e = s(a, b) :=
      Quot.inductionOn e (fun p : Verts n × Verts n => ⟨p.1, p.2, rfl⟩)
    have he' : e ∈ L.filter (fun e => v ∈ e) := hab.symm ▸ he
    obtain ⟨heL, hev⟩ := Finset.mem_filter.mp he'
    have habv : v = a ∨ v = b := (Sym2.mem_iff).mp (hab ▸ hev)
    rcases habv with hva | hvb
    · refine ⟨b, hva ▸ hab, ?_⟩
      rw [mem_nbrsL]
      have hne : b ≠ v := fun h => absurd (hL heL) (by
        have hlo : e = s(v, v) := (hva ▸ hab).trans (congrArg (fun w => s(v, w)) h)
        rw [hlo, mem_edgeFinset]
        exact fun hmem => hmem.2 v v rfl rfl)
      exact ⟨hne, (hva ▸ hab).symm ▸ heL⟩
    · refine ⟨a, (hvb ▸ hab).trans Sym2.eq_swap.symm, ?_⟩
      rw [mem_nbrsL]
      have hne : a ≠ v := fun h => absurd (hL heL) (by
        have hlo : e = s(v, v) := ((hvb ▸ hab).trans Sym2.eq_swap).trans (congrArg (fun w => s(v, w)) h)
        rw [hlo, mem_edgeFinset]
        exact fun hmem => hmem.2 v v rfl rfl)
      exact ⟨hne, ((hvb ▸ hab).trans Sym2.eq_swap).symm ▸ heL⟩
  have hsub : L.filter (fun e => v ∈ e) = (nbrsL L v).image (fun x => s(v, x)) := by
    ext e
    constructor
    · intro he
      obtain ⟨x, hx, hxn⟩ := key e he
      exact Finset.mem_image.mpr ⟨x, hxn, hx.symm⟩
    · intro he
      obtain ⟨x, hxn, hxe⟩ := Finset.mem_image.mp he
      rw [← hxe, Finset.mem_filter]
      exact ⟨(mem_nbrsL.mp hxn).2, Sym2.mem_mk_left v x⟩
  rw [DegL, hsub, Finset.card_image_of_injective]
  intro x y hxy
  exact sym2_inj_right hxy

/-- **THE TOTAL FORM OF THE DENSITY BOUND.**  A leftover graph of maximum degree `D` has at most
`nD` edges — the shape a *first-moment* argument about the first stage produces, in contrast with
the per-vertex form `SparseL_iff_degTris` that the greedy second stage consumes. -/
theorem card_leftover_le_of_SparseL {n D₀ : ℕ} {L : Finset (Sym2 (Verts n))} (hD : SparseL L D₀)
    (hL : L ⊆ edgeFinset (Finset.univ : Finset (Verts n))) : L.card ≤ n * D₀ := by
  have hsub : L ⊆ (Finset.univ : Finset (Verts n)).biUnion (fun v => L.filter (fun e => v ∈ e)) := by
    intro e he
    obtain ⟨a, b, h⟩ : ∃ a b : Verts n, e = s(a, b) :=
      Quot.inductionOn e (fun p : Verts n × Verts n => ⟨p.1, p.2, rfl⟩)
    rw [h]
    exact Finset.mem_biUnion.mpr ⟨a, Finset.mem_univ _,
      Finset.mem_filter.mpr ⟨h ▸ he, Sym2.mem_mk_left a b⟩⟩
  calc L.card ≤ ((Finset.univ : Finset (Verts n)).biUnion (fun v => L.filter (fun e => v ∈ e))).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ v : Verts n, (L.filter (fun e => v ∈ e)).card := Finset.card_biUnion_le
    _ ≤ ∑ _v : Verts n, D₀ := Finset.sum_le_sum (fun v _ => hD v)
    _ = n * D₀ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
        simp

/-! ### 1. The first stage as a linear triple system -/

/-- A family of **three-element** vertex triples: the triangles of the first stage of
arXiv:2208.12563 §4, with the colours forgotten. -/
def Tri3 {n : ℕ} (Tris : Finset (Finset (Verts n))) : Prop := ∀ T ∈ Tris, T.card = 3

/-- **LINEARITY.**  Two distinct triples share at most one vertex.  This is the edge-disjointness of
the first stage: two triangles sharing an *edge* would use the same `(vertex, colour)` pair twice. -/
def Lin3 {n : ℕ} (Tris : Finset (Finset (Verts n))) : Prop :=
  ∀ T T' : Finset (Verts n), T ∈ Tris → T' ∈ Tris → T ≠ T' → (T ∩ T').card ≤ 1

/-- **The number of triples of `Tris` through `v`.** -/
noncomputable def degTris {n : ℕ} (Tris : Finset (Finset (Verts n))) (v : Verts n) : ℕ :=
  (Tris.filter (fun T => v ∈ T)).card

/-- **The vertices covered at `v` by the first stage**: the `x ≠ v` lying in a common triple with
`v`. -/
noncomputable def covTris {n : ℕ} (Tris : Finset (Finset (Verts n))) (v : Verts n) : Finset (Verts n) :=
  (Finset.univ : Finset (Verts n)).filter (fun x => x ≠ v ∧ ∃ T ∈ Tris, v ∈ T ∧ x ∈ T)

@[simp] theorem mem_covTris {n : ℕ} {Tris : Finset (Finset (Verts n))} {v x : Verts n} :
    x ∈ covTris Tris v ↔ x ≠ v ∧ ∃ T ∈ Tris, v ∈ T ∧ x ∈ T := by
  unfold covTris
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

/-- The covered vertices at `v` are the union of the triples through `v`, with `v` deleted. -/
theorem covTris_eq {n : ℕ} (Tris : Finset (Finset (Verts n))) (v : Verts n) :
    covTris Tris v = (Tris.filter (fun T => v ∈ T)).biUnion (fun T => T.erase v) := by
  ext x
  simp only [mem_covTris, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_erase]
  tauto

/-- **THE LINEARITY COUNTING IDENTITY.**  A linear triple system covers `2 · degTris v` vertices at
`v`: every triple through `v` contributes its two other vertices, and linearity makes the
contributions disjoint. -/
theorem card_covTris {n : ℕ} {Tris : Finset (Finset (Verts n))} (h3 : Tri3 Tris) (hL : Lin3 Tris) (v : Verts n) :
    (covTris Tris v).card = 2 * degTris Tris v := by
  have key : ∀ a b : Finset (Verts n), a ∈ Tris.filter (fun T => v ∈ T) →
      b ∈ Tris.filter (fun T => v ∈ T) → a ≠ b → (a.erase v) ∩ (b.erase v) = ∅ := by
    intro a b ha hb hab
    obtain ⟨hat, hav⟩ := Finset.mem_filter.mp ha
    obtain ⟨hbt, hbv⟩ := Finset.mem_filter.mp hb
    refine Finset.eq_empty_iff_forall_notMem.mpr ?_
    intro x hx
    have hxe := Finset.mem_inter.mp hx
    have hxa : x ∈ a := (Finset.mem_erase.mp hxe.1).2
    have hxb : x ∈ b := (Finset.mem_erase.mp hxe.2).2
    have hxv : x ≠ v := (Finset.mem_erase.mp hxe.1).1
    have hsub : {v, x} ⊆ a ∩ b := by
      intro y hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with h | h
      · rw [h]
        exact Finset.mem_inter.mpr ⟨hav, hbv⟩
      · rw [h]
        exact Finset.mem_inter.mpr ⟨hxa, hxb⟩
    have hcard2 : ({v, x} : Finset (Verts n)).card = 2 := by
      have hvx : v ∉ ({x} : Finset (Verts n)) := by
        rw [Finset.mem_singleton]; exact Ne.symm hxv
      rw [Finset.card_insert_of_notMem hvx, Finset.card_singleton]
    have hle := Finset.card_le_card hsub
    have hLin := hL a b hat hbt hab
    omega
  rw [covTris_eq, Finset.card_biUnion (fun a ha b hb hab => by
    have hd : (a.erase v) ∩ (b.erase v) = ∅ := key a b ha hb hab
    refine Finset.disjoint_left.2 ?_
    intro x hx hxb
    exact absurd (Finset.mem_inter.mpr ⟨hx, hxb⟩) (by rw [hd]; simp)), degTris, Finset.sum_filter]
  have hstep : (∑ T ∈ Tris, if v ∈ T then (T.erase v).card else 0)
      = ∑ T ∈ Tris.filter (fun T => v ∈ T), 2 := by
    rw [← Finset.sum_filter]
    refine Finset.sum_congr (s₂ := Tris.filter (fun T => v ∈ T)) rfl (fun T hT => ?_)
    rw [Finset.card_erase_of_mem (Finset.mem_filter.mp hT).2, h3 T (Finset.mem_filter.mp hT).1]
  rw [hstep, Finset.sum_const]
  exact Nat.mul_comm _ _

/-- **THE COUNTING IDENTITY OF THE FIRST STAGE.**  `∑_v degTris v = 3 · |Tris|`: every triple is counted at
each of its three vertices. -/
theorem sum_degTris {n : ℕ} {Tris : Finset (Finset (Verts n))} (h3 : Tri3 Tris) :
    ∑ v : Verts n, degTris Tris v = 3 * Tris.card := by
  calc ∑ v : Verts n, degTris Tris v
      = ∑ v ∈ (Finset.univ : Finset (Verts n)), ∑ T ∈ Tris, if v ∈ T then 1 else 0 := by
        refine Finset.sum_congr (s₂ := Finset.univ) rfl (fun v _ => ?_)
        rw [degTris, Finset.card_filter]
    _ = ∑ T ∈ Tris, ∑ v ∈ (Finset.univ : Finset (Verts n)), if v ∈ T then 1 else 0 := Finset.sum_comm
    _ = ∑ T ∈ Tris, T.card := by
        refine Finset.sum_congr (s₂ := Tris) rfl (fun T _ => ?_)
        simp
    _ = ∑ _T ∈ Tris, 3 := by
        refine Finset.sum_congr (s₂ := Tris) rfl (fun T hT => ?_)
        exact h3 T hT
    _ = 3 * Tris.card := by rw [Finset.sum_const]; exact Nat.mul_comm _ _

/-- **THE STEINER BOUND.**  A linear triple system has at most `n(n-1)/6` triples, and at most
`(n-1)/2` through any one vertex. -/
theorem deg_le {n : ℕ} {Tris : Finset (Finset (Verts n))} (h3 : Tri3 Tris) (hL : Lin3 Tris) (v : Verts n) :
    2 * degTris Tris v ≤ n - 1 := by
  have h1 := card_covTris h3 hL v
  have h2 : (covTris Tris v) ⊆ (Finset.univ : Finset (Verts n)).erase v := by
    intro x hx
    rw [Finset.mem_erase]
    exact ⟨(mem_covTris.mp hx).1, Finset.mem_univ x⟩
  have h3' : (covTris Tris v).card ≤ ((Finset.univ : Finset (Verts n)).erase v).card :=
    Finset.card_le_card h2
  rw [Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ, Fintype.card_fin] at h3'
  omega

/-! ### 2. The leftover of a *partial* first stage -/

/-- **The edges spanned by no triple of `Tris`**: the leftover graph of a first stage which covers all
but `o(n²)` edges, as in arXiv:2207.02920 (Phase 1 ends with `Θ(n^{2-δ})` uncoloured edges). -/
noncomputable def leftoverTris {n : ℕ} (Tris : Finset (Finset (Verts n))) : Finset (Sym2 (Verts n)) :=
  (edgeFinset (Finset.univ : Finset (Verts n))).filter fun e => ¬ ∃ T ∈ Tris, e ∈ edgeFinset T

@[simp] theorem mem_leftoverTris {n : ℕ} {Tris : Finset (Finset (Verts n))} {e : Sym2 (Verts n)} :
    e ∈ leftoverTris Tris ↔ e ∈ edgeFinset (Finset.univ : Finset (Verts n)) ∧
      ¬ ∃ T ∈ Tris, e ∈ edgeFinset T := Finset.mem_filter

/-- Two distinct vertices span an edge of `K_n`. -/
private theorem mem_edgeFinset_of_ne {n : ℕ} {v x : Verts n} (hne : x ≠ v) :
    s(v, x) ∈ edgeFinset (Finset.univ : Finset (Verts n)) := by
  refine mem_edgeFinset.mpr ⟨Finset.mem_sym2_iff.mpr ?_, offDiag_iff.mpr (Ne.symm hne)⟩
  intro a ha
  rcases (Sym2.mem_iff).mp ha with h1 | h1
  · rw [h1]; exact Finset.mem_univ v
  · rw [h1]; exact Finset.mem_univ x

/-- Two vertices of a triple `T` are joined by one of the three edges of `T`. -/
private theorem s_mem_edgeFinset_tri {n : ℕ} {T : Finset (Verts n)} {v x : Verts n} (hne : x ≠ v)
    (hTv : v ∈ T) (hTx : x ∈ T) : s(v, x) ∈ edgeFinset T := by
  refine mem_edgeFinset.mpr ⟨Finset.mem_sym2_iff.mpr ?_, offDiag_iff.mpr (Ne.symm hne)⟩
  intro a ha
  rcases (Sym2.mem_iff).mp ha with h1 | h1
  · rw [h1]; exact hTv
  · rw [h1]; exact hTx

/-- Conversely, the endpoints of an edge of a triple belong to the triple. -/
private theorem mem_tri_of_mem_edgeFinset {n : ℕ} {T : Finset (Verts n)} {e : Sym2 (Verts n)}
    (he : e ∈ edgeFinset T) {a b : Verts n} (ha : a ∈ e) (hb : b ∈ e) : a ∈ T ∧ b ∈ T := by
  have h1 : e ∈ T.sym2 := (mem_edgeFinset.mp he).1
  exact ⟨Finset.mem_sym2_iff.mp h1 a ha, Finset.mem_sym2_iff.mp h1 b hb⟩

/-- **THE LEFTOVER DEGREE OF A PARTIAL FIRST STAGE.**  At `v` the leftover degree is
`n - 1 - 2 · degTris v`: the `n-1` edges at `v`, minus the `2 · degTris v` the triples cover. -/
theorem degL_leftoverTris {n : ℕ} {Tris : Finset (Finset (Verts n))} (h3 : Tri3 Tris) (hL : Lin3 Tris)
    (v : Verts n) : DegL (leftoverTris Tris) v = n - 1 - 2 * degTris Tris v := by
  have h1 : DegL (leftoverTris Tris) v = (nbrsL (leftoverTris Tris) v).card :=
    degL_eq_card_nbrsL (fun e he => (mem_leftoverTris.mp he).1) v
  have h2 : nbrsL (leftoverTris Tris) v
      = (Finset.univ : Finset (Verts n)).erase v \ covTris Tris v := by
    ext x
    constructor
    · intro hx
      rw [mem_nbrsL, mem_leftoverTris] at hx
      obtain ⟨hne, hmem, hnc⟩ := hx
      rw [Finset.mem_sdiff]
      refine ⟨Finset.mem_erase.mpr ⟨hne, Finset.mem_univ x⟩, ?_⟩
      rw [mem_covTris]
      rintro ⟨-, T, hT, hTv, hTx⟩
      exact hnc ⟨T, hT, s_mem_edgeFinset_tri hne hTv hTx⟩
    · intro hx
      rw [Finset.mem_sdiff, Finset.mem_erase, mem_covTris] at hx
      obtain ⟨⟨hne, _⟩, hxc⟩ := hx
      rw [mem_nbrsL, mem_leftoverTris]
      refine ⟨hne, mem_edgeFinset_of_ne hne, fun hT => ?_⟩
      obtain ⟨T, hT, hmem⟩ := hT
      obtain ⟨hTv, hTx⟩ := mem_tri_of_mem_edgeFinset hmem (Sym2.mem_mk_left v x) (Sym2.mem_mk_right v x)
      exact hxc ⟨hne, T, hT, hTv, hTx⟩
  have hsub : covTris Tris v ⊆ (Finset.univ : Finset (Verts n)).erase v := by
    intro y hy
    rw [Finset.mem_erase]
    exact ⟨(mem_covTris.mp hy).1, Finset.mem_univ y⟩
  rw [h1, h2, Finset.card_sdiff_of_subset hsub, Finset.card_erase_of_mem (Finset.mem_univ v),
    Finset.card_univ, Fintype.card_fin, card_covTris h3 hL v]

/-- **THE FIRST-STAGE DENSITY LEMMA.**  The leftover graph of a linear triple system has maximum
degree at most `D`

    `⟺  2 · degTris v ≥ n - 1 - D` for every vertex `v`.

Read to the left: *the first stage passes through every vertex at least `⌈(n-1-D)/2⌉` times*.  This
is the exact, purely combinatorial form of the "maximum degree `D = n^{1-δ}`" statement of
arXiv:2208.12563 §4 (IV) and arXiv:2207.02920 Claim 4. -/
theorem SparseL_iff_degTris {n : ℕ} {Tris : Finset (Finset (Verts n))} (h3 : Tri3 Tris) (hL : Lin3 Tris)
    (D : ℕ) : SparseL (leftoverTris Tris) D ↔ ∀ v : Verts n, 2 * degTris Tris v ≥ n - 1 - D := by
  constructor
  · intro hD v
    have h := hD v
    rw [degL_leftoverTris h3 hL v] at h
    omega
  · intro hD v
    have h := hD v
    rw [degL_leftoverTris h3 hL v]
    omega

/-- The forward direction of `SparseL_iff_degTris`, in the form the second stage consumes. -/
theorem SparseL_of_degTris {n : ℕ} {Tris : Finset (Finset (Verts n))} (h3 : Tri3 Tris) (hL : Lin3 Tris) {D : ℕ}
    (h : ∀ v : Verts n, 2 * degTris Tris v ≥ n - 1 - D) : SparseL (leftoverTris Tris) D :=
  (SparseL_iff_degTris h3 hL D).mpr h


/-! ### 3. The price of a deterministic second stage -/

/-- `12 ≤ δm` gives `6 ≤ (δ/2)m`. -/
private theorem six_of_twelve {δ m : ℝ} (h : (12 : ℝ) ≤ δ * m) : (6 : ℝ) ≤ (δ / 2) * m := by
  have e : δ * m = 2 * ((δ / 2) * m) := by ring
  linarith

/-- `(δ/2)m ≤ δm`. -/
private theorem half_le_full {δ m : ℝ} (hδ : 0 < δ) (hm : 0 ≤ m) : (δ / 2) * m ≤ δ * m := by
  have e : δ * m = 2 * ((δ / 2) * m) := by ring
  have h3 : (0 : ℝ) ≤ (δ / 2) * m := by positivity
  linarith

/-- The six fresh colours of a budget split. -/
private theorem six_add (a b : ℕ) :
    (6 : ℝ) * ((a + b : ℕ) : ℝ) = (6 : ℝ) * (a : ℝ) + 6 * (b : ℝ) := by
  push_cast
  ring

/-- The six fresh colours of the deterministic second stage split. -/
private theorem six_det (D T : ℕ) :
    (6 : ℝ) * ((2 * D * D + 2 * D + T + 1 : ℕ) : ℝ)
      = 12 * (D : ℝ) * (D : ℝ) + 12 * (D : ℝ) + 6 * (T : ℝ) + 6 := by
  push_cast
  ring

/-- The six fresh colours of the greedy properness stage split. -/
private theorem six_proper (D : ℕ) :
    (6 : ℝ) * ((2 * D + 1 : ℕ) : ℝ) = 12 * (D : ℝ) + 6 := by
  push_cast
  ring

/-- **THE COUNTING BOUND THE FIRST STAGE HAS TO SATISFY**, in the additive form
`5(n-1) ≤ 6k + 5D`: a first stage whose leftover graph has maximum degree `D` uses at least
`5(n-1-D)/6` colours.

This is the slot counting of arXiv:2208.12563 §4: a matching in the auxiliary `8`-uniform
hypergraph uses each of the `n·k` pairs `(vertex, colour)` at most once, each labelled triangle uses
five of them (the definition of `triPairs`; `card_triPairs` is the five-element computation), and a
first stage covering all but a leftover of degree `D` has at least `n(n-1-D)/6` triangles (§1:
`sum_degTris` and `SparseL_iff_degTris`).  The formalisation of the *middle* step — injectivity of
`(triangle, vertex, colour) ↦ (vertex, colour)`, which needs the fact that the centre of a
first-stage triangle is determined by its vertex set — is **the next concrete lemma of round 36**.  It
is taken as a hypothesis here because every theorem below is a statement about what happens *once* it
is available, and none of the verdicts depends on its details. -/
def FirstStageCounting (n k D : ℕ) : Prop := 5 * (n - 1) ≤ 6 * k + 5 * D

/-- **THE COUNTING BOUND, IN REAL NUMBERS.** -/
theorem cast_count {n k D : ℕ} (hdeg : FirstStageCounting n k D) :
    (6 : ℝ) * (k : ℝ) + 5 * (D : ℝ) ≥ 5 * ((n - 1 : ℕ) : ℝ) := by
  rcases n with _ | n
  · simp only [Nat.cast_zero, Nat.zero_sub]
    exact_mod_cast (by omega : (0 : ℕ) ≤ 6 * k + 5 * D)
  · have h1 : ((n + 1 - 1 : ℕ) : ℝ) = (n : ℝ) := by push_cast; ring
    have h2 : ((5 * (n + 1 - 1) : ℕ) : ℝ) = 5 * ((n + 1 - 1 : ℕ) : ℝ) := Nat.cast_mul 5 _
    have h3 : ((6 * k + 5 * D : ℕ) : ℝ) = (6 : ℝ) * (k : ℝ) + 5 * (D : ℝ) := by push_cast; ring
    have h4 : ((5 * (n + 1 - 1) : ℕ) : ℝ) ≤ ((6 * k + 5 * D) : ℕ) := by
      exact_mod_cast (show 5 * (n + 1 - 1) ≤ 6 * k + 5 * D from hdeg)
    rw [h2, h1, h3] at h4
    linarith

/-- **THE BUDGET OF THE CATALOG ANSWER, SPENT ON THE SECOND STAGE.**  If the first stage pays
`5(n-1) ≤ 6k + 5D` of the budget `6(k + fresh) ≤ 5(n-1) + δn`, then the second stage may use

    `6 · fresh ≤ 5D + δn`.

Everything below is a corollary of this single accounting identity. -/
theorem budget_leftover {n k D fresh : ℕ} (δ : ℝ) (hδ : 0 < δ)
    (hdeg : FirstStageCounting n k D)
    (hbudget : 6 * ((k + fresh : ℕ) : ℝ) ≤ 5 * ((n - 1 : ℕ) : ℝ) + δ * (n : ℝ)) :
    6 * (fresh : ℝ) ≤ 5 * (D : ℝ) + δ * (n : ℝ) := by
  have h1 := cast_count hdeg
  rw [six_add] at hbudget
  linarith

/-- **THE PUBLISHED SECOND STAGE IS PAYABLE.**  Round 31's greedy properness uses `fresh = 2D + 1`
fresh colours — this is the second stage of arXiv:2208.12563 §4 — and `budget_leftover` shows it fits
the remaining budget `5D + δn` as soon as `7D + 6 ≤ δn`.  For the published leftover degree
`D = n^{1-δ}` this holds for all large `n`.

**So the second stage of the papers is not the obstruction, and the local lemma is not needed for
it.** -/
theorem proper_fits {n D : ℕ} (δ : ℝ) (hδ : 0 < δ) (hD : (7 : ℝ) * (D : ℝ) + 6 ≤ δ * (n : ℝ)) :
    6 * ((2 * D + 1 : ℕ) : ℝ) ≤ 5 * (D : ℝ) + δ * (n : ℝ) := by
  have h2 := six_proper D
  rw [h2]
  have h3 : (0 : ℝ) ≤ (D : ℝ) := by positivity
  nlinarith

/-- **THE DETERMINISTIC SECOND STAGE OF ROUNDS 33–34 IS NOT PAYABLE.**

The second stage proved in `StarColour.lean` (round 33) and `Cross.lean` (round 34) excludes **all
three** bad events of the papers — `B₁ = A_{e,f,i}`, `B₂ = B_D` and `B₃ = C_{D,i}` — with no
probability at all, and costs `fresh = 2D² + 2D + T + 1` fresh colours.  But then

    **`12 D² + 7D + 6T + 6 ≤ δn`,**

and in particular **`12 D² ≤ δn`**: the deterministic second stage needs `D = O(√(δn)) = o(√n)`.  The
published first stage has `D = n^{1-δ}`, and for `δ < 1/2` the inequality `12 n^{2-2δ} ≤ δn` is false
for all large `n`.  **The deterministic second stage cannot pay for the published first stage,
however the first stage is built.** -/
theorem deterministic_budget_strong {n k D T : ℕ} (δ : ℝ) (hδ : 0 < δ)
    (hdeg : FirstStageCounting n k D)
    (hbudget : 6 * ((k + (2 * D * D + 2 * D + T + 1) : ℕ) : ℝ)
      ≤ 5 * ((n - 1 : ℕ) : ℝ) + δ * (n : ℝ)) :
    12 * (D : ℝ) * (D : ℝ) + (7 : ℝ) * (D : ℝ) + 6 * (T : ℝ) + 6 ≤ δ * (n : ℝ) := by
  have h1 := cast_count hdeg
  rw [six_add, six_det] at hbudget
  have h3 : (0 : ℝ) ≤ (D : ℝ) := by positivity
  have h4 : (0 : ℝ) ≤ (T : ℝ) := by positivity
  nlinarith

/-- The headline corollary: `12D² ≤ δn`. -/
theorem deterministic_budget {n k D T : ℕ} (δ : ℝ) (hδ : 0 < δ)
    (hdeg : FirstStageCounting n k D)
    (hbudget : 6 * ((k + (2 * D * D + 2 * D + T + 1) : ℕ) : ℝ)
      ≤ 5 * ((n - 1 : ℕ) : ℝ) + δ * (n : ℝ)) :
    12 * (D : ℝ) * (D : ℝ) ≤ δ * (n : ℝ) := by
  have h1 := deterministic_budget_strong δ hδ hdeg hbudget
  have h2 : (0 : ℝ) ≤ (D : ℝ) := by positivity
  have h3 : (0 : ℝ) ≤ (T : ℝ) := by positivity
  nlinarith

/-- **THE DETERMINISTIC STAGE ALSO FITS THE REMAINING BUDGET** — but only because the budget itself
was assumed.  Read together with `deterministic_budget` the two say: *if* the catalog budget is
available, *then* the round-33/34 second stage is affordable only when `12D² ≤ δn`.* -/
theorem deterministic_fits {n k D T : ℕ} (δ : ℝ) (hδ : 0 < δ)
    (hdeg : FirstStageCounting n k D)
    (hbudget : 6 * ((k + (2 * D * D + 2 * D + T + 1) : ℕ) : ℝ)
      ≤ 5 * ((n - 1 : ℕ) : ℝ) + δ * (n : ℝ)) :
    6 * ((2 * D * D + 2 * D + T + 1 : ℕ) : ℝ) ≤ 5 * (D : ℝ) + δ * (n : ℝ) := by
  have h1 := budget_leftover δ hδ hdeg hbudget
  have h2 := six_det D T
  rw [h2] at h1
  have h3 : (0 : ℝ) ≤ (D : ℝ) := by positivity
  nlinarith

/-- **THE TWO BUDGETS ARE STRICTLY ORDERED.**  Whenever the round-33/34 budget holds, the *published*
condition `7D + 6 ≤ δn` holds as well: rounds 33 and 34 bought a strictly more expensive way of
spending the same budget, and the extra price is unbounded as `δ → 0`.  This is the theorem that
retires the whole family of "deterministic second stage" attacks. -/
theorem deterministic_imp_proper {n k D T : ℕ} (δ : ℝ) (hδ : 0 < δ) (hD1 : 1 ≤ D)
    (hdeg : FirstStageCounting n k D)
    (hbudget : 6 * ((k + (2 * D * D + 2 * D + T + 1) : ℕ) : ℝ)
      ≤ 5 * ((n - 1 : ℕ) : ℝ) + δ * (n : ℝ)) :
    7 * (D : ℝ) + 6 ≤ δ * (n : ℝ) := by
  have h1 := deterministic_budget_strong δ hδ hdeg hbudget
  have h2 : (0 : ℝ) ≤ (T : ℝ) := by positivity
  nlinarith

/-- **AND THE ROUND-33/34 BUDGET IS NOT A CONSEQUENCE OF THE PUBLISHED ONE.**  The two conditions are
strictly ordered and incomparable in the other direction: for `D ≥ 1` the deterministic budget
implies the published one, but not conversely. -/
theorem deterministic_ne_proper {n D T : ℕ} (δ : ℝ) (hD1 : 1 ≤ D)
    (hnot : ¬ (12 * (D : ℝ) * (D : ℝ) ≤ δ * (n : ℝ))) :
    ¬ (6 * ((2 * D * D + 2 * D + T + 1 : ℕ) : ℝ) ≤ 5 * (D : ℝ) + δ * (n : ℝ)) := by
  intro h
  have h2 := six_det D T
  rw [h2] at h
  have h3 : (0 : ℝ) ≤ (D : ℝ) := by positivity
  nlinarith [hnot]

/-! ### 4. The interface of round 34 is vacuous, and the corrected one -/

/-- **THE ROUND-34 HYPOTHESIS IS ROUND 29's HYPOTHESIS.**  `CrossStageFamily` asserts `Covers c₀` —
the *complete* covering of round 29 — together with `SparseL` and `CrossThin` on `leftover c₀`.  But
`Covers c₀ ↔ leftover c₀ = ∅`, so with `D = T = 0` the fresh-colour cost is `1` and the family is
nothing but `TriFamily`: **the whole second stage of rounds 33 and 34 is dead code with respect to
the remaining hypothesis.** -/
theorem crossStageFamily_tri (h : CrossStageFamily) : TriFamily := by
  intro δ hδ
  obtain ⟨M, D, T, hM⟩ := h (δ / 2) (by linarith)
  refine ⟨max M 4, fun m hMm hm => ?_⟩
  obtain ⟨k, c₀, hC, hP, hX, hB, hD, hThin, hk⟩ :=
    hM m (Nat.le_trans (Nat.le_max_left _ _) hMm) hm
  have h3 : (0 : ℝ) ≤ 6 * ((2 * D * D + 2 * D + T + 1 : ℕ) : ℝ) := by positivity
  have h2 : (6 : ℝ) * (k : ℝ) ≤ (6 : ℝ) * (k : ℝ)
      + 6 * ((2 * D * D + 2 * D + T + 1 : ℕ) : ℝ) := by linarith
  have h4 := half_le_full (δ := δ) hδ (by positivity : (0 : ℝ) ≤ (m : ℝ))
  rw [six_add] at hk
  have h5 : (6 : ℝ) * (k : ℝ) ≤ 5 * ((m - 1 : ℕ) : ℝ) + (δ / 2) * (m : ℝ) := by
    linarith
  exact ⟨k, c₀, hC, hP, hX, hB, by linarith⟩

/-- And conversely, at the price of the single unavoidable fresh colour. -/
theorem tri_crossStageFamily' (h : TriFamily) (δ : ℝ) (hδ : 0 < δ) :
    ∃ M : ℕ, ∀ m : ℕ, M ≤ m → m % 6 = 1 → (12 : ℝ) ≤ δ * (m : ℝ) →
      ∃ (k : ℕ) (c₀ : Col m k),
        Covers c₀ ∧ PairFree c₀ ∧ NoCrossFour c₀ ∧ NoBadFour c₀ ∧
          SparseL (leftover c₀) 0 ∧ CrossThin c₀ (leftover c₀) 0 ∧
          6 * ((k + 1 : ℕ) : ℝ) ≤ 5 * ((m - 1 : ℕ) : ℝ) + δ * (m : ℝ) := by
  obtain ⟨M, hM⟩ := h (δ / 2) (by linarith)
  refine ⟨max (max M 4) 1, fun m hMm hm h12 => ?_⟩
  obtain ⟨k, c₀, hC, hP, hX, hB, hk⟩ := hM m (by omega) hm
  have h0 : leftover c₀ = ∅ := covers_iff_leftover_eq_empty.mp hC
  have hS : SparseL (leftover c₀) 0 := by
    intro v
    rw [DegL, h0]
    simp
  have hT : CrossThin c₀ (leftover c₀) 0 := by
    unfold CrossThin CrossPairs
    rw [h0]
    simp
  have h1 : (6 : ℝ) * (k : ℝ) ≤ 5 * ((m - 1 : ℕ) : ℝ) + (δ / 2) * (m : ℝ) := by
    have h2 : (6 : ℝ) * (k : ℝ) = 6 * ((k : ℕ) : ℝ) := rfl
    linarith [hk]
  exact ⟨k, c₀, hC, hP, hX, hB, hS, hT, by
    have h2 : (6 : ℝ) * ((k + 1 : ℕ) : ℝ) = (6 : ℝ) * (k : ℝ) + 6 := by
      simpa using six_add k 1
    rw [h2]
    linarith [six_of_twelve h12]⟩

theorem crossStageFamily_of_tri (h : TriFamily) : CrossStageFamily := by
  intro δ hδ
  obtain ⟨M, hM⟩ := tri_crossStageFamily' h δ hδ
  obtain ⟨N, hN⟩ := exists_nat_gt (12 / δ)
  refine ⟨max (max M 4) (N + 1), 0, 0, fun m hMm hm => ?_⟩
  have hN1 : N + 1 ≤ m := by
    have hx : N + 1 ≤ max (max M 4) (N + 1) := Nat.le_max_right _ _
    omega
  have hN2 : (12 : ℝ) / δ < (m : ℝ) := by
    have hx : (N : ℝ) ≤ (N + 1 : ℕ) := by exact_mod_cast (Nat.le_succ N)
    have hx' : (N + 1 : ℕ) ≤ (m : ℝ) := by exact_mod_cast hN1
    linarith
  have h12 : (12 : ℝ) ≤ δ * (m : ℝ) := by
    rw [div_lt_iff₀ hδ] at hN2
    linarith
  obtain ⟨k, c₀, hC, hP, hX, hB, hS, hT, hk⟩ := hM m (by omega) hm h12
  exact ⟨k, c₀, hC, hP, hX, hB, hS, hT, hk⟩

/-- **THE ROUND-34 REDUCTION IS EQUIVALENT TO ROUND 29's.**  Nothing was gained, and nothing was
lost: the deterministic second stage of rounds 33/34 is a correct theorem, but the hypothesis it is
attached to can never make use of it. -/
theorem crossStageFamily_iff_triFamily : CrossStageFamily ↔ TriFamily :=
  ⟨crossStageFamily_tri, crossStageFamily_of_tri⟩

/-- **AND IT GIVES THE HEADLINE.**  `Cross.lean`'s `jsp_000140_main_of_cross_stage_family` is thus
equivalent to round 29's `jsp_000140_main_of_tri_family`. -/
theorem jsp_000140_main_of_cross_iff_tri (h : CrossStageFamily) : jsp_000140_target :=
  jsp_000140_main_of_tri_family (crossStageFamily_tri h)

/-- **A FIRST STAGE COVERING ALL BUT `N` EDGES.**  The published first stage leaves `Θ(n^{2-δ})`
edges uncovered. -/
def AlmostCovers {n k : ℕ} (c : Col n k) (N : ℕ) : Prop := (leftover c).card ≤ N

/-- **THE TOTAL BOUND IS VACUOUS.**  `AlmostCovers c (n·n)` holds for *every* colouring: the leftover
degree of any colouring is at most `n-1`, so the leftover has at most `n(n-1)` edges.  **This is why
the per-vertex form `SparseL_iff_degTris` — and not a first-moment bound on the number of leftover
edges — is the real content of the first stage's density analysis, and what the second stage
consumes.** -/
theorem leftover_card_le (n k : ℕ) (c : Col n k) : (leftover c).card ≤ n * n := by
  refine card_leftover_le_of_SparseL (D₀ := n) (fun v => by
    have h : DegL (leftover c) v ≤ n - 1 := DegL_leftover
    omega) (fun e he => (mem_leftover.mp he).1)

theorem almostCovers_of_leftover_card (n k : ℕ) (c : Col n k) : AlmostCovers c (n * n) :=
  leftover_card_le n k c

/-- **THE CORRECTED INTERFACE.**  The first stage may leave `o(n²)` edges uncovered; the four local
conditions and the leaf closure are hypotheses (they are Phase-1 output in arXiv:2207.02920, and
`tile_of_tri` / `leafClosed_of_tri` need the *complete* covering of round 29); and the two density
statements `SparseL`, `CrossThin` are genuinely non-vacuous.  The `12 ≤ δm` side condition absorbs
the single unavoidable fresh colour. -/
def PartialStageFamily : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ M D T : ℕ, ∀ m : ℕ, M ≤ m → m % 6 = 1 → (12 : ℝ) ≤ δ * (m : ℝ) →
    ∃ (k : ℕ) (c₀ : Col m k),
      AlmostCovers c₀ (m * m) ∧ Design c₀ ∧ LeafClosed c₀ (leftover c₀) ∧
        SparseL (leftover c₀) D ∧ CrossThin c₀ (leftover c₀) T ∧
        (6 : ℝ) * ((k + (2 * D * D + 2 * D + T + 1) : ℕ) : ℝ)
          ≤ 5 * ((m - 1 : ℕ) : ℝ) + δ * (m : ℝ)

/-- **THE TWO STAGES COMPOSE ON A PARTIAL FIRST STAGE.** -/
theorem SlackFamily.of_partial (hfam : PartialStageFamily) : SlackFamily := by
  intro δ hδ
  obtain ⟨M, D, T, hM⟩ := hfam δ hδ
  obtain ⟨N, hN⟩ := exists_nat_gt (12 / δ)
  refine ⟨max (max M 4) (N + 1), fun m hMm hm => ?_⟩
  have hN1 : N + 1 ≤ m := by
    have hx : N + 1 ≤ max (max M 4) (N + 1) := Nat.le_max_right _ _
    omega
  have hN2 : (12 : ℝ) / δ < (m : ℝ) := by
    have hx : (N : ℝ) ≤ (N + 1 : ℕ) := by exact_mod_cast (Nat.le_succ N)
    have hx' : (N + 1 : ℕ) ≤ (m : ℝ) := by exact_mod_cast hN1
    linarith
  have h12 : (12 : ℝ) ≤ δ * (m : ℝ) := by
    rw [div_lt_iff₀ hδ] at hN2
    linarith
  obtain ⟨k, c₀, hAC, hD₀, hLC, hD, hThin, hk⟩ := hM m (by omega) hm h12
  have h4m : 4 ≤ m := by omega
  obtain ⟨g, hPr, hS, hX'⟩ := cross_greedy_extend hD hThin
  have hE : Extends (liftCol c₀ (Nat.le_add_right k (2 * D * D + 2 * D + T + 1)))
      (extendColDep c₀ (leftover c₀) g) (leftover c₀) :=
    Extends_extendColDep (c := c₀) (L := leftover c₀) (g := g)
  exact ⟨k + (2 * D * D + 2 * D + T + 1), extendColDep c₀ (leftover c₀) g,
    admissible_of_cross hE hPr hS hX' hD₀ hLC h4m, hk⟩

/-- **THE REQUIRED THEOREM, WITH THE CORRECTED FIRST-STAGE INTERFACE.** -/
theorem jsp_000140_main_of_partial_stage_family (hfam : PartialStageFamily) : jsp_000140_target :=
  jsp_000140_main_of_slack_family (SlackFamily.of_partial hfam)

/-- **THE CORRECTED INTERFACE IS AT LEAST AS GENERAL AS ROUND 34's.**  Round 34's `CrossStageFamily`
implies it: its leftover is empty, so `Design` and `LeafClosed` are Phase-1 output of a complete
covering, and `AlmostCovers` is automatic by `leftover_card_le`.  The converse would force the
leftover to be empty, so it is *false* in the interesting case — which is the whole point of the
correction. -/
theorem crossStageFamily_partial (hfam : CrossStageFamily) : PartialStageFamily := by
  intro δ hδ
  obtain ⟨M, D, T, hM⟩ := hfam δ hδ
  obtain ⟨N, hN⟩ := exists_nat_gt (12 / δ)
  refine ⟨max (max M 4) (N + 1), D, T, fun m hMm hm h12 => ?_⟩
  obtain ⟨k, c₀, hC, hP, hX, hB, hD, hThin, hk⟩ := hM m (by omega) hm
  have h4m : 4 ≤ m := by omega
  exact ⟨k, c₀, almostCovers_of_leftover_card m k c₀,
    ⟨tile_of_tri hC hP h4m, packed_of_tri hC hP h4m, hX, hB⟩, leafClosed_of_tri hC hP, hD, hThin, hk⟩

end JSP140
