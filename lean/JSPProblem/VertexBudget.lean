import JSPProblem.Slot
import JSPProblem.Cover
import JSPProblem.ApexPrice
import JSPProblem.Surplus
import JSPProblem.Leftover
import JSPProblem.Strict

/-!
# JSP-000140 — round 92: **THE PER-VERTEX BUDGET OF THE FIRST STAGE** — the local form of the
# packing bound, the refined bound `Isolated c + 5|triSets c| ≤ n·k`, and the price of a complete
# covering

Ninety-one rounds of this development attacked `f(n,4,5) = 5n/6 + o(n)` from the outside: the
counting bound `5(n-1) ≤ 6k` (`Cherry.lean`), its exact surplus form
`6·Isolated c + 2·Defect c = n(6k - 5(n-1))` (`Surplus.lean`), the impossibility of the equality
case (`Strict.lean`), the global packing bound `5·|triSets c| ≤ n·k` of the *labelled-triangle*
encoding (`Cover.lean`, `Slot.lean`), the union-bound barrier for a uniform colouring
(`Barrier.lean`), the deterministic structure of the extremal case (`PathFac.lean`), and the exact
two-stage interface of arXiv:2208.12563 §4 (`Leftover.lean`).

**Every one of those statements is a statement about aggregates.**  `5·|T| ≤ n·k` counts the five
`(vertex, colour)` slots of a triangle against the `n·k` available *globally*; `3a_i + 2b_i = n`
(`Cell.lean`, `PathFac.lean`) reads one *colour* at a time; `Isolated c` is a total over colours.
The object the literature actually builds — a *matching* in an auxiliary `8`-uniform hypergraph
(arXiv:2208.12563 §4) — is a matching of `(vertex, colour)` **pairs**, so the bound that matters
for it is a *per-vertex* one, and this development had never written it down.

**This round writes the per-vertex budget, and the price of a complete covering falls out of it.**

## §0 — the two roles of a vertex in the first stage

A labelled triangle `(u; p, q)` uses `u` once (as apex) and `p`, `q` twice each (as leaves): its
five slots are `(u, λ), (p, λ), (q, λ), (p, μ), (q, μ)`.  So a vertex of the first stage plays
exactly two roles, and

* `ApexPrice.apexTris c v` — the triangles whose apex is `v` (`ApexPrice.lean`, round 89);
* **`leafTris c v` — the triangles in which `v` is a leaf** (new);
* `atVertex c v = ApexPrice.apexTris c v ∪ leafTris c v`, the two disjointly (`apex_eq_of_triVerts`:
  **a triangle has a unique apex**, which was also never stated);
* the double counts `Σ_v |atVertex c v| = 3·|triSets c|`, `Σ_v |ApexPrice.apexTris c v| = |triSets c|` and
  `Σ_v |leafTris c v| = 2·|triSets c|` (`sum_card_atVertex`, `sum_card_apexTris`,
  `sum_card_leafTris`).

## §1 — the per-vertex *edge* budget

Every triangle through `v` uses exactly **two** of the `n-1` edges at `v` (the two cherry edges if
`v` is the apex, the cherry edge and the opposite edge if `v` is a leaf), and distinct triangles
share no edge (`Slot.lin3_triSets`, from admissibility alone).  Hence, for **every** admissible
colouring and **every** vertex,

* **`two_mul_card_atVertex_le — 2·|atVertex c v| ≤ n - 1`**;
* **`degAt c v = n - 1 - 2·|atVertex c v|` is the number of edges at `v` that lie in no labelled
  triangle — the edges of the leftover graph `L` of arXiv:2208.12563 §4 incident with `v`, the
  workload of the second stage at `v` — and
  `sum_degAt_eq_two_mul_leftover: Σ_v degAt c v = 2·|leftover c|`** (§4 of
  arXiv:2208.12563, in per-vertex form).

## §2 — the per-vertex *slot* budget

Each triangle uses one slot at its apex and two at each leaf, and the slots of distinct triangles
are disjoint (`Cover.triVerts_eq_of_mem_triPairs`, i.e. admissibility).  With
`vSlots c v = {p ∈ Slots c | p.1 = v}`:

* **`card_vSlots_eq — |vSlots c v| = |ApexPrice.apexTris c v| + 2·|leafTris c v|`** (the "five pairs per
  triangle" identity, vertex by vertex);
* **`card_vSlots_le` and `slotBudget — |ApexPrice.apexTris c v| + 2·|leafTris c v| ≤ k`**, the local form of
  `Slot.slots_five`, i.e. `two_mul_card_leafTris_le: 2·|leafTris c v| ≤ k`;
* `sum_card_vSlots` and `sum_slot_eq_five_mul_card`: the global statement is recovered from the
  local ones, `Σ_v (|ApexPrice.apexTris c v| + 2·|leafTris c v|) = 5·|triSets c|`.

## §3 — THE REFINED PACKING BOUND

An isolated `(vertex, colour)` cell (`v ∈ zeroA c i`: `v` has no `i`-edge) is **never a slot**:
if `(v, i) ∈ anchorPairs c T` then `v ∈ T` and some `y ≠ v` satisfies `c s(v,y) = i`
(`Slot.mem_anchorPairs`).  So the `nk` slots split into the `5|triSets c|` used ones and at least
`Isolated c` unused ones:

* **`Isolated_add_five_mul_card_le — `Isolated c + 5·|triSets c| ≤ n·k`**,

a strict sharpening of `Slot.slots_five` for every colouring with an isolated cell — and the
*first* statement of this development that puts the two defects of `Surplus.lean` and the slot
counting of `Cover.lean` in one inequality.

## §4 — the price of a complete covering

Assume now `Covers c`: every edge of `K_n` lies in a labelled triangle.  Then every edge at `v` is
used, so the edge budget of §1 is an equality and the slot budget of §2 becomes a statement about
`k - (n-1)/2`:

* **`covers_two_mul_card_atVertex`, `covers_card_atVertex — `Covers c → |ApexPrice.apexTris c v| +
  |leafTris c v| = (n-1)/2`** (every vertex lies in exactly `(n-1)/2` triangles);
* **`covers_apex_ge — `Covers c → n - 1 - k ≤ |ApexPrice.apexTris c v|`** and
  **`covers_leaf_le — `Covers c → |leafTris c v| ≤ k - (n-1)/2`**: a vertex is the apex of at
  least `n-1-k` triangles and a leaf of at most `k - (n-1)/2`;
* hence **`covers_apex_ge_one`**: if `k ≤ n-2` then *every* vertex is the apex of a labelled
  triangle, and by `Strict.apex_zeroA` (round 45) every vertex then has an isolated cell:
  **`covers_isolated_ge — `n ≤ Isolated c`**;
* **`covers_price — `Covers c ∧ k ≤ n-2 → 5(n-1) + 6 ≤ 6k`** — **THE PRICE OF A COMPLETE FIRST
  STAGE**: with `6|triSets c| = n(n-1)` (`covers_six_mul_card`) and `Isolated c ≥ n`, §3 gives
  `k ≥ 5(n-1)/6 + 1`.  This is *strictly stronger* than round 89's `ApexPrice.covered_price`
  (`5n - 3 ≤ 6k`, i.e. `5(n-1)/6 + 1/3`): a complete labelled-triangle covering of `K_n` cannot
  come within a third of a colour of the catalogue rate — it must pay a whole extra colour;
* **`covers_dichotomy`**, **`covers_not_extremal`** (`7 ≤ n`), **`covers_residual_ge`**
  (`6k = 5(n-1) + r → 6 ≤ r`) and the two-stage reading **`covers_two_stage_price`: the published
  hypothesis `6(k+K) ≤ 5(m-1) + δm` forces `δm ≥ 6` whenever the first stage is a complete
  covering**, i.e. at the catalogue rate the second stage of arXiv:2208.12563 §4 is not an
  optimisation but a necessity.

## §5 — what the construction still has to do

`Main.AdmissibleUpper ε` (`0 < ε < 1/6`) — the existence of admissible `k`-colourings with
`k ≤ 5n/6 + εn` — is unchanged and is still the sole missing content of `jsp_000140_main`.  What
this round adds is the *price list* such a construction must satisfy, vertex by vertex:

* `two_mul_card_atVertex_le`, `slotBudget`: the local form of both budgets, for free;
* `covers_price`: `+1` colour, one whole unit of the `6k` budget, at the rate;
* `sum_degAt_eq_two_mul_leftover`: the workload of the second stage, per vertex.
-/

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

namespace JSP140
namespace VertexBudget

attribute [local instance] Classical.propDecidable

variable {n k : ℕ}

/-! ### A generic double count -/

/-- **DOUBLE COUNTING OVER A FINSET.**  For a finset `s` of finsets, the number of pairs
`(x, y)` with `y ∈ s` and `x ∈ f y` is counted both ways. -/
private theorem sum_card_filter_eq {α β : Type*} [DecidableEq α] [DecidableEq β] [Fintype β]
    (s : Finset α) (f : α → Finset β) :
    (∑ x : β, (s.filter fun y => x ∈ f y).card) = ∑ y ∈ s, (f y).card := by
  have key : ∀ x : β, (s.filter fun y => x ∈ f y).card
      = ∑ y ∈ s, (if x ∈ f y then (1 : ℕ) else 0) := by
    intro x
    calc (s.filter fun y => x ∈ f y).card = ∑ y ∈ s.filter (fun y => x ∈ f y), (1 : ℕ) :=
          Finset.card_eq_sum_ones _
      _ = ∑ y ∈ s, (if x ∈ f y then (1 : ℕ) else 0) :=
          Finset.sum_filter (fun y => x ∈ f y) (fun _ => (1 : ℕ))
  calc (∑ x : β, (s.filter fun y => x ∈ f y).card)
      = ∑ x : β, ∑ y ∈ s, (if x ∈ f y then (1 : ℕ) else 0) :=
        Finset.sum_congr rfl fun x _ => key x
    _ = ∑ y ∈ s, ∑ x : β, (if x ∈ f y then (1 : ℕ) else 0) := by rw [Finset.sum_comm]
    _ = ∑ y ∈ s, (f y).card := by
        refine Finset.sum_congr rfl fun y _ => ?_
        have h1 : (∑ x : β, (if x ∈ f y then (1 : ℕ) else 0))
            = (Finset.filter (fun x : β => x ∈ f y) (Finset.univ : Finset β)).card :=
          Finset.sum_boole _ _
        have h2 : Finset.filter (fun x : β => x ∈ f y) (Finset.univ : Finset β) = f y := by
          ext x
          simp
        rw [h1, h2]

/-! ### §0 — the two roles of a vertex in the first stage -/

/-- **THE LABELLED TRIANGLES OF `c` IN WHICH `v` IS A LEAF** — the triangles through `v` whose apex
is somebody else.  Together with `ApexPrice.apexTris c v` these are the two roles a vertex plays
in the first stage of arXiv:2208.12563 §4, and they are counted vertex by vertex here. -/
noncomputable def leafTris {n k : ℕ} (c : Col n k) (v : Verts n) : Finset (Finset (Verts n)) :=
  (triSets c).filter fun T => ∃ u p q : Verts n, LabTri c u p q ∧ triVerts u p q = T ∧ v ∈ T ∧ v ≠ u

@[simp] theorem mem_leafTris {n k : ℕ} {c : Col n k} {v : Verts n} {T : Finset (Verts n)} :
    T ∈ leafTris c v ↔ T ∈ triSets c ∧
      ∃ u p q : Verts n, LabTri c u p q ∧ triVerts u p q = T ∧ v ∈ T ∧ v ≠ u :=
  Finset.mem_filter

/-- **THE TRIANGLES OF THE FIRST STAGE THROUGH `v`.** -/
noncomputable def atVertex {n k : ℕ} (c : Col n k) (v : Verts n) : Finset (Finset (Verts n)) :=
  (triSets c).filter fun T => v ∈ T

@[simp] theorem mem_atVertex {n k : ℕ} {c : Col n k} {v : Verts n} {T : Finset (Verts n)} :
    T ∈ atVertex c v ↔ T ∈ triSets c ∧ v ∈ T := Finset.mem_filter

theorem leafTris_subset {n k : ℕ} {c : Col n k} (v : Verts n) : leafTris c v ⊆ triSets c := by
  intro T hT; exact (mem_leafTris.mp hT).1

theorem atVertex_subset {n k : ℕ} {c : Col n k} (v : Verts n) : atVertex c v ⊆ triSets c := by
  intro T hT; exact (mem_atVertex.mp hT).1

/-- **THREE VERTICES.**  Membership in the vertex set of a labelled triangle is one of the three
alternatives. -/
private theorem mem_triVerts {n : ℕ} {a b c x : Verts n} (hx : x ∈ triVerts a b c) :
    x = a ∨ x = b ∨ x = c := by
  have hx' : x ∈ insert a (insert b (insert c (∅ : Finset (Verts n)))) := hx
  rcases (Finset.mem_insert.mp hx') with h | h
  · exact Or.inl h
  rcases (Finset.mem_insert.mp h) with h | h
  · exact Or.inr (Or.inl h)
  rcases (Finset.mem_insert.mp h) with h | h
  · exact Or.inr (Or.inr h)
  · exact absurd h (by simp)

/-- **A TRIANGLE HAS A UNIQUE APEX.**  Two labelled triangles of `c` with the same vertex set have
the same apex — the local rigidity which makes `apexTris` a *partition* of the triangles by apex,
and which the per-vertex counting of §0–§2 uses. -/
theorem apex_eq_of_triVerts {n k : ℕ} {c : Col n k} {u p q u' p' q' : Verts n} (h1 : LabTri c u p q)
    (h2 : LabTri c u' p' q') (hE : triVerts u p q = triVerts u' p' q') : u = u' := by
  have hne2 := LabTri.ne h2
  have hlam : c s(u, p) = c s(u, q) := h1.2.2.2.1
  have hmu : c s(u, p) ≠ c s(p, q) := h1.2.2.2.2
  have hswap : ∀ a b : Verts n, c s(a, b) = c s(b, a) := by
    intro a b
    congr 1
    exact Sym2.eq_swap
  have memU : ∀ x : Verts n, x ∈ triVerts u' p' q' → x ∈ triVerts u p q := by
    intro x hx
    rw [hE]
    exact hx
  -- the four colour contradictions of a same-vertex-set relabelling
  have cA : ∀ (h1' : u' = p) (h2' : p' = u) (h3' : q' = q), False := by
    intro h1' h2' h3'
    have key : c s(u, p) = c s(p, q) := by
      calc c s(u, p) = c s(p, u) := hswap _ _
        _ = c s(p, q) := by rw [← h1', ← h2', ← h3']; exact h2.2.2.2.1
    exact absurd key hmu
  have cB : ∀ (h1' : u' = p) (h2' : p' = q) (h3' : q' = u), False := by
    intro h1' h2' h3'
    have key : c s(u, p) = c s(p, q) := by
      calc c s(u, p) = c s(p, u) := hswap _ _
        _ = c s(p, q) := by rw [← h1', ← h2', ← h3']; exact h2.2.2.2.1.symm
    exact absurd key hmu
  have cC : ∀ (h1' : u' = q) (h2' : p' = u) (h3' : q' = p), False := by
    intro h1' h2' h3'
    have key : c s(u, p) = c s(p, q) := by
      calc c s(u, p) = c s(u, q) := hlam
        _ = c s(q, u) := hswap _ _
        _ = c s(q, p) := by rw [← h1', ← h2', ← h3']; exact h2.2.2.2.1
        _ = c s(p, q) := hswap _ _
    exact absurd key hmu
  have cD : ∀ (h1' : u' = q) (h2' : p' = p) (h3' : q' = u), False := by
    intro h1' h2' h3'
    have key : c s(u, p) = c s(p, q) := by
      calc c s(u, p) = c s(u, q) := hlam
        _ = c s(q, u) := hswap _ _
        _ = c s(q, p) := by rw [← h1', ← h2', ← h3']; exact h2.2.2.2.1.symm
        _ = c s(p, q) := hswap _ _
    exact absurd key hmu
  rcases mem_triVerts (memU u' (by simp [triVerts])) with h | h
  · exact h.symm
  rcases h with h | h
  · -- the case u' = p
    exfalso
    have hne2' : p ≠ p' ∧ p ≠ q' ∧ p' ≠ q' := by rw [← h]; exact hne2
    rcases mem_triVerts (memU p' (by simp [triVerts])) with hp | hp
    · rcases mem_triVerts (memU q' (by simp [triVerts])) with hq | hq
      · exact absurd hq.symm (hp ▸ hne2'.2.2)
      rcases hq with hq | hq
      · exact absurd hq.symm hne2'.2.1
      · exact cA h hp hq
    rcases hp with hp | hp
    · exact absurd hp.symm hne2'.1
    rcases mem_triVerts (memU q' (by simp [triVerts])) with hq | hq
    · exact cB h hp hq
    rcases hq with hq | hq
    · exact absurd hq.symm hne2'.2.1
    · exact absurd hq.symm (hp ▸ hne2'.2.2)
  · -- the case u' = q
    exfalso
    have hne2' : q ≠ p' ∧ q ≠ q' ∧ p' ≠ q' := by rw [← h]; exact hne2
    rcases mem_triVerts (memU p' (by simp [triVerts])) with hp | hp
    · rcases mem_triVerts (memU q' (by simp [triVerts])) with hq | hq
      · exact absurd hq.symm (hp ▸ hne2'.2.2)
      rcases hq with hq | hq
      · exact cC h hp hq
      · exact absurd hq.symm hne2'.2.1
    rcases hp with hp | hp
    · rcases mem_triVerts (memU q' (by simp [triVerts])) with hq | hq
      · exact cD h hp hq
      rcases hq with hq | hq
      · exact absurd hq.symm (hp ▸ hne2'.2.2)
      · exact absurd hq.symm hne2'.2.1
    · exact absurd hp.symm hne2'.1

/-- **THE TWO ROLES PARTITION THE TRIANGLES THROUGH `v`.** -/
theorem atVertex_eq_union {n k : ℕ} {c : Col n k} (v : Verts n) :
    atVertex c v = ApexPrice.apexTris c v ∪ leafTris c v := by
  ext T
  constructor
  · intro hT
    have hT' := mem_atVertex.mp hT
    obtain ⟨u, p, q, hlt, hE⟩ := mem_triSets.mp hT'.1
    by_cases hu : v = u
    · exact Finset.mem_union_left _ (ApexPrice.mem_apexTris.mpr
        ⟨hT'.1, p, q, (Eq.symm hu) ▸ hlt, (Eq.symm hu) ▸ hE⟩)
    · exact Finset.mem_union_right _ (mem_leafTris.mpr
        ⟨hT'.1, u, p, q, hlt, hE, hT'.2, hu⟩)
  · intro hT
    rw [Finset.mem_union] at hT
    rcases hT with hT | hT
    · obtain ⟨hT', p, q, hlt, hE⟩ := ApexPrice.mem_apexTris.mp hT
      refine mem_atVertex.mpr ⟨hT', ?_⟩
      rw [← hE]; simp [triVerts]
    · obtain ⟨hT', u, p, q, hlt, hE, hv, hne⟩ := mem_leafTris.mp hT
      refine mem_atVertex.mpr ⟨hT', ?_⟩
      rw [← hE]
      rcases mem_triVerts (hE.symm ▸ hv) with h | h | h
      · exact absurd h hne
      · simp [triVerts, h]
      · simp [triVerts, h]

/-- **A VERTEX IS AN APEX OR A LEAF, NEVER BOTH.** -/
theorem disjoint_apexTris_leafTris {n k : ℕ} {c : Col n k} (v : Verts n) :
    Disjoint (ApexPrice.apexTris c v) (leafTris c v) := by
  refine Finset.disjoint_left.2 fun T hT hT' => ?_
  obtain ⟨hT1, p, q, hlt, hE⟩ := ApexPrice.mem_apexTris.mp hT
  obtain ⟨hT2, u, p', q', hlt', hE', hv, hne⟩ := mem_leafTris.mp hT'
  exact hne (apex_eq_of_triVerts hlt hlt' (hE.trans hE'.symm))

/-- **THE NUMBER OF TRIANGLES THROUGH `v`.** -/
theorem card_atVertex_eq {n k : ℕ} {c : Col n k} (v : Verts n) :
    (atVertex c v).card = (ApexPrice.apexTris c v).card + (leafTris c v).card := by
  rw [atVertex_eq_union v]
  exact Finset.card_union_of_disjoint (by
    refine Finset.disjoint_left.2 fun T h1 h2 => ?_
    exact absurd h2 ((Finset.disjoint_left.mp (disjoint_apexTris_leafTris v)) h1))

/-- **THE FIRST DOUBLE COUNT: every triangle has three vertices.** -/
theorem sum_card_atVertex {n k : ℕ} {c : Col n k} :
    (∑ v : Verts n, (atVertex c v).card) = 3 * (triSets c).card := by
  have h := sum_card_filter_eq (triSets c) (fun T : Finset (Verts n) => T)
  have key : ∀ T ∈ triSets c, T.card = 3 := fun T hT => card_mem_triSets hT
  calc (∑ v : Verts n, (atVertex c v).card) 
      = ∑ x : Verts n, ((triSets c).filter fun y => x ∈ y).card := by
        unfold atVertex
        rfl
    _ = ∑ T ∈ triSets c, T.card := h
    _ = ∑ _T ∈ triSets c, (3 : ℕ) := Finset.sum_congr rfl fun T hT => key T hT
    _ = 3 * (triSets c).card := by rw [Finset.sum_const]; simp [Nat.mul_comm]

/-- **THE TRIANGLES WITH APEX `v` PARTITION THE FIRST STAGE** — the finiteness consequence of
`apex_eq_of_triVerts`. -/
theorem sum_card_apexTris {n k : ℕ} {c : Col n k} :
    (∑ v : Verts n, (ApexPrice.apexTris c v).card) = (triSets c).card := by
  calc (∑ v : Verts n, (ApexPrice.apexTris c v).card)
      = ((Finset.univ : Finset (Verts n)).biUnion fun v => ApexPrice.apexTris c v).card := by
        rw [Finset.card_biUnion (fun a ha b hb hab => by
          refine Finset.disjoint_left.2 fun T hT1 hT2 => ?_
          obtain ⟨hT1', p, q, hlt1, hE1⟩ := ApexPrice.mem_apexTris.mp hT1
          obtain ⟨hT2', pu, qu, hlt2, hE2⟩ := ApexPrice.mem_apexTris.mp hT2
          exact hab (apex_eq_of_triVerts hlt1 hlt2 (hE1.trans hE2.symm)))]
    _ = (triSets c).card := by
        have key : ((Finset.univ : Finset (Verts n)).biUnion
            fun v => ApexPrice.apexTris c v) = triSets c := by
          ext T
          constructor
          · intro hT
            rw [Finset.mem_biUnion] at hT
            obtain ⟨v, hv, hmem⟩ := hT
            obtain ⟨hT', p, q, hlt, hE⟩ := ApexPrice.mem_apexTris.mp hmem
            exact mem_triSets.mpr ⟨v, p, q, hlt, hE⟩
          · intro hT
            obtain ⟨u, p, q, hlt, hE⟩ := mem_triSets.mp hT
            refine Finset.mem_biUnion.mpr ⟨u, Finset.mem_univ u, ?_⟩
            exact ApexPrice.mem_apexTris.mpr ⟨hT, p, q, hlt, hE⟩
        rw [key]

/-- **THE SECOND DOUBLE COUNT: every triangle has two leaves.** -/
theorem sum_card_leafTris {n k : ℕ} {c : Col n k} :
    (∑ v : Verts n, (leafTris c v).card) = 2 * (triSets c).card := by
  have h1 : (∑ v : Verts n, (atVertex c v).card)
      = (∑ v : Verts n, (ApexPrice.apexTris c v).card) + ∑ v : Verts n, (leafTris c v).card := by
    calc (∑ v : Verts n, (atVertex c v).card)
        = ∑ v : Verts n, ((ApexPrice.apexTris c v).card + (leafTris c v).card) :=
          Finset.sum_congr rfl fun v _ => card_atVertex_eq v
      _ = (∑ v : Verts n, (ApexPrice.apexTris c v).card)
          + ∑ v : Verts n, (leafTris c v).card := Finset.sum_add_distrib
  have h2 := sum_card_atVertex (c := c)
  have h3 := sum_card_apexTris (c := c)
  omega

/-! ### §1 — the per-vertex edge budget -/

/-- **TWO DISTINCT TRIANGLES THROUGH `v` SHARE NO VERTEX OTHER THAN `v`.** -/
private theorem inter_erase_v_eq_empty {n k : ℕ} {c : Col n k} (hc : Admissible c) (v : Verts n)
    {T T' : Finset (Verts n)} (hT : T ∈ atVertex c v) (hT' : T' ∈ atVertex c v) (hne : T ≠ T') :
    T.erase v ∩ T'.erase v = ∅ := by
  refine Finset.eq_empty_iff_forall_notMem.2 fun x hx => ?_
  rw [Finset.mem_inter] at hx
  obtain ⟨hx1, hx2⟩ := hx
  have hxv : x ≠ v := (Finset.mem_erase.mp hx1).1
  have hxT : x ∈ T := (Finset.mem_erase.mp hx1).2
  have hxT' : x ∈ T' := (Finset.mem_erase.mp hx2).2
  have hvv : v ∈ T := (mem_atVertex.mp hT).2
  have hvv' : v ∈ T' := (mem_atVertex.mp hT').2
  have hsub : ({x, v} : Finset (Verts n)) ⊆ T ∩ T' := by
    intro y hy
    rw [Finset.mem_insert] at hy
    rcases hy with hy | hy
    · rw [hy]
      exact Finset.mem_inter.mpr ⟨hxT, hxT'⟩
    · rw [Finset.mem_singleton] at hy
      rw [hy]
      exact Finset.mem_inter.mpr ⟨hvv, hvv'⟩
  have hcard2 : ({x, v} : Finset (Verts n)).card = 2 := by
    rw [Finset.card_insert_of_notMem (by rw [Finset.mem_singleton]; exact hxv),
      Finset.card_singleton]
  have h2 : 2 ≤ (T ∩ T').card := le_trans hcard2.ge (Finset.card_le_card hsub)
  have h3 : (T ∩ T').card ≤ 1 := lin3_triSets (PairFree_of_admissible hc) T T'
    (mem_atVertex.mp hT).1 (mem_atVertex.mp hT').1 hne
  omega

/-- **A TRIANGLE THROUGH `v` USES EXACTLY TWO OF THE `n-1` EDGES AT `v`.** -/
private theorem card_erase_v_eq_two {n k : ℕ} {c : Col n k} {T : Finset (Verts n)} {v : Verts n}
    (hT : T ∈ triSets c) (hv : v ∈ T) : (T.erase v).card = 2 := by
  have h3 : T.card = 3 := card_mem_triSets hT
  rw [Finset.card_erase_of_mem hv]
  omega

/-- **THE PER-VERTEX EDGE BUDGET: `2·|atVertex c v| ≤ n - 1`, FOR EVERY ADMISSIBLE COLOURING.**
Every labelled triangle through `v` uses two of the `n-1` edges at `v`, and distinct triangles
share no edge. -/
theorem two_mul_card_atVertex_le {n k : ℕ} {c : Col n k} (hc : Admissible c) (v : Verts n) :
    2 * (atVertex c v).card ≤ n - 1 := by
  have hbi : ((atVertex c v).biUnion fun T => T.erase v).card = 2 * (atVertex c v).card := by
    calc ((atVertex c v).biUnion fun T => T.erase v).card
        = ∑ T ∈ atVertex c v, (T.erase v).card := by
          exact Finset.card_biUnion (fun a ha b hb hab => by
            refine Finset.disjoint_left.2 fun x hx hxb => ?_
            have hmem : x ∈ a.erase v ∩ b.erase v := Finset.mem_inter.mpr ⟨hx, hxb⟩
            have hne' := inter_erase_v_eq_empty hc v ha hb hab
            rw [hne'] at hmem
            exact absurd hmem (by simp))
      _ = ∑ _T ∈ atVertex c v, (2 : ℕ) := by
          refine Finset.sum_congr rfl fun T hT => ?_
          exact card_erase_v_eq_two (mem_atVertex.mp hT).1 (mem_atVertex.mp hT).2
      _ = 2 * (atVertex c v).card := by rw [Finset.sum_const]; simp [Nat.mul_comm]
  have hsub : ((atVertex c v).biUnion fun T => T.erase v)
      ⊆ (Finset.univ : Finset (Verts n)).erase v := by
    intro x hx
    obtain ⟨T, hT, hxT⟩ := Finset.mem_biUnion.mp hx
    have hxv : x ≠ v := (Finset.mem_erase.mp hxT).1
    exact Finset.mem_erase.mpr ⟨hxv, Finset.mem_univ x⟩
  calc 2 * (atVertex c v).card = ((atVertex c v).biUnion fun T => T.erase v).card := hbi.symm
    _ ≤ ((Finset.univ : Finset (Verts n)).erase v).card := Finset.card_le_card hsub
    _ = n - 1 := by simp

/-- **THE LEFTOVER DEGREE OF `v`**: the edges at `v` lying in no labelled triangle, i.e. the edges
of the leftover graph `L` of arXiv:2208.12563 §4 incident with `v` — the workload of the second
stage at `v`. -/
noncomputable def degAt {n k : ℕ} (c : Col n k) (v : Verts n) : ℕ :=
  n - 1 - 2 * (atVertex c v).card

/-! ### §2 — the per-vertex slot budget -/

/-- **THE SLOTS OF THE FIRST STAGE BELONGING TO THE VERTEX `v`.** -/
noncomputable def vSlots {n k : ℕ} (c : Col n k) (v : Verts n) : Finset (Verts n × Fin k) :=
  (Slots c).filter fun p => p.1 = v

@[simp] theorem mem_vSlots {n k : ℕ} {c : Col n k} {v : Verts n} {p : Verts n × Fin k} :
    p ∈ vSlots c v ↔ p ∈ Slots c ∧ p.1 = v := Finset.mem_filter

/-- **THERE ARE AT MOST `k` SLOTS AT `v`.** -/
theorem card_vSlots_le {n k : ℕ} {c : Col n k} (v : Verts n) : (vSlots c v).card ≤ k := by
  calc (vSlots c v).card
      ≤ (({v} : Finset (Verts n)).product (Finset.univ : Finset (Fin k))).card := by
        refine Finset.card_le_card ?_
        intro p hp
        rw [mem_vSlots] at hp
        exact Finset.mem_product.mpr
          ⟨by rw [Finset.mem_singleton]; exact hp.2, Finset.mem_univ _⟩
    _ = k := by simp

/-- **THE FIVE PAIRS OF A LABELLED TRIANGLE, ONE BY ONE.** -/
private theorem mem_triPairs {n k : ℕ} {c : Col n k} {u p q : Verts n} (h : LabTri c u p q)
    {x : Verts n × Fin k} (hx : x ∈ triPairs c u p q) :
    x = (u, c s(u, p)) ∨ x = (p, c s(u, p)) ∨ x = (q, c s(u, p))
      ∨ x = (p, c s(p, q)) ∨ x = (q, c s(p, q)) := by
  rcases (Finset.mem_insert.mp hx) with h' | h'
  · exact Or.inl h'
  rcases (Finset.mem_insert.mp h') with h' | h'
  · exact Or.inr (Or.inl h')
  rcases (Finset.mem_insert.mp h') with h' | h'
  · exact Or.inr (Or.inr (Or.inl h'))
  rcases (Finset.mem_insert.mp h') with h' | h'
  · exact Or.inr (Or.inr (Or.inr (Or.inl h')))
  rcases (Finset.mem_insert.mp h') with h' | h'
  · exact Or.inr (Or.inr (Or.inr (Or.inr h')))
  · exact absurd h' (by simp)

/-- **THE SLOTS OF `v` INSIDE ONE TRIANGLE: ONE AT AN APEX, TWO AT A LEAF.** -/
private theorem card_filter_triPairs {n k : ℕ} {c : Col n k} {u p q v : Verts n} (h : LabTri c u p q)
    (hv : v ∈ triVerts u p q) :
    ((triPairs c u p q).filter fun x => x.1 = v).card = if v = u then 1 else 2 := by
  have hne := LabTri.ne h
  have hcol : c s(u, p) ≠ c s(p, q) := h.2.2.2.2
  have hsplit : v = u ∨ v = p ∨ v = q := mem_triVerts hv
  rcases hsplit with hu | hu | hu
  · rw [hu]
    rw [show (triPairs c u p q).filter (fun x => x.1 = u) = {(u, c s(u, p))} by
      ext x
      rw [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · intro hx
        obtain ⟨hA, hB⟩ := hx
        rcases mem_triPairs h hA with h1 | h2 | h3 | h4 | h5
        · exact h1
        · have k1 : p = u := (congrArg Prod.fst h2).symm.trans hB
          exact (hne.1 k1.symm).elim
        · have k1 : q = u := (congrArg Prod.fst h3).symm.trans hB
          exact (hne.2.1 k1.symm).elim
        · have k1 : p = u := (congrArg Prod.fst h4).symm.trans hB
          exact (hne.1 k1.symm).elim
        · have k1 : q = u := (congrArg Prod.fst h5).symm.trans hB
          exact (hne.2.1 k1.symm).elim
      · intro hx
        rw [hx]
        exact ⟨Finset.mem_insert_self _ _, rfl⟩]
    simp
  · rw [hu]
    rw [show (triPairs c u p q).filter (fun x => x.1 = p)
        = {(p, c s(u, p)), (p, c s(p, q))} by
      ext x
      rw [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · intro hx
        obtain ⟨hA, hB⟩ := hx
        rcases mem_triPairs h hA with h1 | h2 | h3 | h4 | h5
        · have k1 : u = p := (congrArg Prod.fst h1).symm.trans hB
          exact (hne.1 k1).elim
        · exact Or.inl h2
        · have k1 : q = p := (congrArg Prod.fst h3).symm.trans hB
          exact (hne.2.2.symm k1).elim
        · exact Or.inr h4
        · have k1 : q = p := (congrArg Prod.fst h5).symm.trans hB
          exact (hne.2.2.symm k1).elim
      · intro hx
        rcases hx with rfl | rfl
        · exact ⟨Finset.mem_insert_of_mem (Finset.mem_insert_self _ _), rfl⟩
        · exact ⟨Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
            (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))), rfl⟩]
    simp [hcol, hne.1.symm]
  · rw [hu]
    rw [show (triPairs c u p q).filter (fun x => x.1 = q)
        = {(q, c s(u, p)), (q, c s(p, q))} by
      ext x
      rw [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · intro hx
        obtain ⟨hA, hB⟩ := hx
        rcases mem_triPairs h hA with h1 | h2 | h3 | h4 | h5
        · have k1 : u = q := (congrArg Prod.fst h1).symm.trans hB
          exact (hne.2.1 k1).elim
        · have k1 : p = q := (congrArg Prod.fst h2).symm.trans hB
          exact (hne.2.2 k1).elim
        · exact Or.inl h3
        · have k1 : p = q := (congrArg Prod.fst h4).symm.trans hB
          exact (hne.2.2 k1).elim
        · exact Or.inr h5
      · intro hx
        rcases hx with rfl | rfl
        · exact ⟨Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
            (Finset.mem_insert_self _ _)), rfl⟩
        · exact ⟨Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
            (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
              (Finset.mem_insert_self _ _)))), rfl⟩]
    simp [hcol, hne.2.1.symm]

/-- **THE PER-VERTEX SLOT COUNT: `|vSlots c v| = |ApexPrice.apexTris c v| + 2·|leafTris c v|`.**  This is the
"five `(vertex, colour)` pairs per triangle" identity (`Cover.card_triPairs_five`) counted vertex
by vertex: one pair at the apex, two at each leaf. -/
theorem card_vSlots_eq {n k : ℕ} {c : Col n k} (hc : Admissible c) (v : Verts n) :
    (vSlots c v).card = (ApexPrice.apexTris c v).card + 2 * (leafTris c v).card := by
  have key0 : ∀ T : Finset (Verts n), T ∈ triSets c → v ∉ T →
      (anchorPairs c T).filter (fun p => p.1 = v) = ∅ := by
    intro T hT hvT
    ext p
    rw [Finset.mem_filter]
    constructor
    · intro h
      obtain ⟨hA, hB⟩ := h
      have hp1T : p.1 ∈ T := (mem_anchorPairs.mp hA).1
      exact (hvT (hB ▸ hp1T)).elim
    · intro h
      nomatch h
  have hbi : vSlots c v
      = (atVertex c v).biUnion fun T => (anchorPairs c T).filter (fun p => p.1 = v) := by
    ext p
    constructor
    · intro h
      rw [mem_vSlots] at h
      have h1 : p ∈ Slots c := h.1
      have hpv : p.1 = v := h.2
      obtain ⟨T, hT, hmem⟩ := mem_Slots.mp h1
      by_cases hvT : v ∈ T
      · exact Finset.mem_biUnion.mpr ⟨T, mem_atVertex.mpr ⟨hT, hvT⟩,
          Finset.mem_filter.mpr ⟨hmem, hpv⟩⟩
      · exact absurd (mem_anchorPairs.mp hmem).1 (fun hp1T => hvT (hpv ▸ hp1T))
    · intro h
      obtain ⟨T, hT, hmem⟩ := Finset.mem_biUnion.mp h
      have hmem' := Finset.mem_filter.mp hmem
      exact mem_vSlots.mpr ⟨mem_Slots.mpr ⟨T, (mem_atVertex.mp hT).1, hmem'.1⟩, hmem'.2⟩
  have hdisc : ∀ T T' : Finset (Verts n), T ∈ atVertex c v → T' ∈ atVertex c v → T ≠ T' →
      Disjoint ((anchorPairs c T).filter (fun p => p.1 = v))
        ((anchorPairs c T').filter (fun p => p.1 = v)) := by
    intro T T' hT hT' hne
    refine Finset.disjoint_left.2 fun p hp1 hp2 => ?_
    have hp1' := Finset.mem_filter.mp hp1
    have hp2' := Finset.mem_filter.mp hp2
    have hmem : p ∈ anchorPairs c T ∩ anchorPairs c T' :=
      Finset.mem_inter.mpr ⟨hp1'.1, hp2'.1⟩
    obtain ⟨u, pu, q, h1, hE1⟩ := mem_triSets.mp (mem_atVertex.mp hT).1
    obtain ⟨u', pu', q', h2, hE2⟩ := mem_triSets.mp (mem_atVertex.mp hT').1
    have hmem2 : p ∈ triPairs c u pu q ∩ triPairs c u' pu' q' := by
      have hmem' : p ∈ anchorPairs c (triVerts u pu q) ∩ anchorPairs c (triVerts u' pu' q') := by
        rw [← hE1, ← hE2] at hmem
        exact hmem
      rw [triPairs_eq_anchorPairs h1, triPairs_eq_anchorPairs h2]
      exact hmem'
    have hvv := triVerts_eq_of_mem_triPairs hc h1 h2 hmem2
    exact hne (hE2.symm.trans (hE1.symm.trans hvv).symm).symm
  have key1 : ∀ T ∈ atVertex c v,
      ((anchorPairs c T).filter (fun p => p.1 = v)).card
        = if ∃ p q : Verts n, LabTri c v p q ∧ triVerts v p q = T then (1 : ℕ) else 2 := by
    intro T hT
    obtain ⟨u, p, q, hlt, hE⟩ := mem_triSets.mp (mem_atVertex.mp hT).1
    have hvT : v ∈ triVerts u p q := by rw [hE]; exact (mem_atVertex.mp hT).2
    have hcard : ((anchorPairs c T).filter (fun p => p.1 = v)).card
        = if v = u then (1 : ℕ) else 2 := by
      rw [← hE, ← triPairs_eq_anchorPairs hlt, card_filter_triPairs hlt hvT]
    rw [hcard]
    by_cases hz : ∃ p q : Verts n, LabTri c v p q ∧ triVerts v p q = T
    · rw [if_pos hz]
      obtain ⟨pu, qu, hlt2, hE2⟩ := hz
      have hvu : v = u := apex_eq_of_triVerts hlt2 hlt (hE2.trans hE.symm)
      rw [hvu]
      simp
    · rw [if_neg hz]
      have hne' : ¬(v = u) := fun hv => hz ⟨p, q, by rw [hv]; exact hlt, by rw [hv]; exact hE⟩
      rw [if_neg hne']
  have key2 : ∀ T ∈ ApexPrice.apexTris c v,
      ((anchorPairs c T).filter (fun p => p.1 = v)).card = (1 : ℕ) := by
    intro T hT
    obtain ⟨hT', p, q, hlt, hE⟩ := ApexPrice.mem_apexTris.mp hT
    have hvT : v ∈ T := by rw [← hE]; simp [triVerts]
    rw [key1 T (mem_atVertex.mpr ⟨hT', hvT⟩)]
    rw [if_pos ⟨p, q, hlt, hE⟩]
  have key3 : ∀ T ∈ leafTris c v,
      ((anchorPairs c T).filter (fun p => p.1 = v)).card = (2 : ℕ) := by
    intro T hT
    obtain ⟨hT', u, p, q, hlt, hE, hv, hne⟩ := mem_leafTris.mp hT
    have hvT : v ∈ T := hv
    rw [key1 T (mem_atVertex.mpr ⟨hT', hvT⟩)]
    rw [if_neg (fun hz => by
      obtain ⟨pu, qu, hlt2, hE2⟩ := hz
      exact hne (apex_eq_of_triVerts hlt2 hlt (hE2.trans hE.symm)))]
  calc (vSlots c v).card = ((atVertex c v).biUnion
        fun T => (anchorPairs c T).filter (fun p => p.1 = v)).card := by rw [hbi]
    _ = ∑ T ∈ atVertex c v, ((anchorPairs c T).filter (fun p => p.1 = v)).card :=
        Finset.card_biUnion (fun a ha b hb hab => hdisc a b ha hb hab)
    _ = ∑ T ∈ ApexPrice.apexTris c v ∪ leafTris c v,
        ((anchorPairs c T).filter (fun p => p.1 = v)).card := by rw [atVertex_eq_union v]
    _ = (∑ T ∈ ApexPrice.apexTris c v, ((anchorPairs c T).filter (fun p => p.1 = v)).card)
        + ∑ T ∈ leafTris c v, ((anchorPairs c T).filter (fun p => p.1 = v)).card :=
        Finset.sum_union (by
          refine Finset.disjoint_left.2 fun T h1 h2 => ?_
          exact absurd h2 ((Finset.disjoint_left.mp (disjoint_apexTris_leafTris v)) h1))
    _ = ∑ _T ∈ ApexPrice.apexTris c v, (1 : ℕ) + ∑ _T ∈ leafTris c v, (2 : ℕ) := by
        rw [Finset.sum_congr rfl fun T hT => key2 T hT,
          Finset.sum_congr rfl fun T hT => key3 T hT]
    _ = (ApexPrice.apexTris c v).card + 2 * (leafTris c v).card := by
        rw [Finset.card_eq_sum_ones, Finset.card_eq_sum_ones]
        simp [Nat.mul_comm]

/-- **THE PER-VERTEX SLOT BUDGET — THE LOCAL FORM OF `Slot.slots_five`:**

  `|ApexPrice.apexTris c v| + 2·|leafTris c v| ≤ k`.

This is the inequality the auxiliary `8`-uniform hypergraph of arXiv:2208.12563 §4 needs, read at
one vertex: the first stage may use at most `k` of the pairs `(v, ·)`. -/
theorem slotBudget {n k : ℕ} {c : Col n k} (hc : Admissible c) (v : Verts n) :
    (ApexPrice.apexTris c v).card + 2 * (leafTris c v).card ≤ k := by
  rw [← card_vSlots_eq hc v]
  exact card_vSlots_le v

/-- **A VERTEX IS A LEAF OF AT MOST `k/2` TRIANGLES.** -/
theorem two_mul_card_leafTris_le {n k : ℕ} {c : Col n k} (hc : Admissible c) (v : Verts n) :
    2 * (leafTris c v).card ≤ k := by
  have h := slotBudget hc v
  omega

/-- **THE SLOTS OF `v`, OVER ALL VERTICES, ARE ALL THE SLOTS.** -/
theorem sum_card_vSlots {n k : ℕ} {c : Col n k} :
    (∑ v : Verts n, (vSlots c v).card) = (Slots c).card := by
  calc (∑ v : Verts n, (vSlots c v).card)
      = ((Finset.univ : Finset (Verts n)).biUnion fun v => vSlots c v).card := by
        rw [Finset.card_biUnion (fun a ha b hb hab => by
          refine Finset.disjoint_left.2 fun p hp1 hp2 => ?_
          obtain ⟨hp1', hp2'⟩ := Finset.mem_filter.mp hp1, Finset.mem_filter.mp hp2
          exact hab (hp1'.2.symm.trans hp2'.2))]
    _ = (Slots c).card := by
        have key : ((Finset.univ : Finset (Verts n)).biUnion fun v => vSlots c v) = Slots c := by
          ext p
          constructor
          · intro h
            obtain ⟨v, hv, hmem⟩ := Finset.mem_biUnion.mp h
            exact (mem_vSlots.mp hmem).1
          · intro h
            obtain ⟨T, hT, hmem⟩ := mem_Slots.mp h
            exact Finset.mem_biUnion.mpr
              ⟨p.1, Finset.mem_univ p.1,
                mem_vSlots.mpr ⟨mem_Slots.mpr ⟨T, hT, hmem⟩, rfl⟩⟩
        rw [key]

/-- **THE TOTAL SLOT COUNT, VERTEX BY VERTEX: `5·|triSets c|`.** -/
theorem sum_slot_eq_five_mul_card {n k : ℕ} {c : Col n k} (hc : Admissible c) :
    (∑ v : Verts n, ((ApexPrice.apexTris c v).card + 2 * (leafTris c v).card)) = 5 * (triSets c).card := by
  calc (∑ v : Verts n, ((ApexPrice.apexTris c v).card + 2 * (leafTris c v).card))
      = ∑ v : Verts n, (vSlots c v).card := by
        refine Finset.sum_congr rfl fun v _ => ?_
        exact (card_vSlots_eq hc v).symm
    _ = (Slots c).card := sum_card_vSlots
    _ = 5 * (triSets c).card := card_Slots (PairFree_of_admissible hc)

/-! ### §3 — the refined packing bound -/

/-- **THE ISOLATED `(VERTEX, COLOUR)` CELLS, AS PAIRS.** -/
noncomputable def isoPairs {n k : ℕ} (c : Col n k) : Finset (Verts n × Fin k) :=
  (Finset.univ : Finset (Fin k)).biUnion fun i => (zeroA c i).product ({i} : Finset (Fin k))

/-- **`|isoPairs c| = Isolated c`**: the same pairs, counted. -/
theorem card_isoPairs {n k : ℕ} (c : Col n k) : (isoPairs c).card = Isolated c := by
  calc (isoPairs c).card
      = ∑ i ∈ (Finset.univ : Finset (Fin k)),
        ((zeroA c i).product ({i} : Finset (Fin k))).card := by
          exact Finset.card_biUnion (fun a ha b hb hab => by
            refine Finset.disjoint_left.2 fun p hp1 hp2 => ?_
            have hp1a : p.2 = a := Finset.mem_singleton.mp (Finset.mem_product.mp hp1).2
            have hp2a : p.2 = b := Finset.mem_singleton.mp (Finset.mem_product.mp hp2).2
            exact hab (hp1a.symm.trans hp2a))
    _ = ∑ i : Fin k, (zeroA c i).card := by
        refine Finset.sum_congr rfl fun i _ => ?_
        simp
    _ = Isolated c := rfl

/-- **AN ISOLATED CELL IS NEVER A SLOT**: if `v ∈ zeroA c i` then `(v, i) ∉ Slots c`, because
`(v, i) ∈ anchorPairs c T` would exhibit an `i`-edge at `v` (`Slot.mem_anchorPairs`). -/
theorem not_mem_Slots_of_zeroA {n k : ℕ} {c : Col n k} {i : Fin k} {v : Verts n}
    (hv : v ∈ zeroA c i) : (v, i) ∉ Slots c := by
  intro hmem
  obtain ⟨T, hT, hmem'⟩ := mem_Slots.mp hmem
  obtain ⟨hxT, hmem''⟩ := mem_anchorPairs.mp hmem'
  obtain ⟨y, hyT, hyx, hcy⟩ := hmem''
  have hN : y ∈ Nbrs c i v := by
    rw [mem_Nbrs]
    exact ⟨hyx, hcy⟩
  have h1 : 1 ≤ (Nbrs c i v).card := Finset.card_le_card (Finset.singleton_subset_iff.mpr hN)
  have h0 : (Nbrs c i v).card = 0 := mem_zeroA.mp hv
  omega

/-- **THE ISOLATED CELLS ARE UNUSED SLOTS.** -/
theorem isoPairs_subset_unused {n k : ℕ} (c : Col n k) :
    isoPairs c ⊆ (Finset.univ : Finset (Verts n × Fin k)).filter fun p => p ∉ Slots c := by
  intro p hp
  obtain ⟨i, hi, hmem⟩ := Finset.mem_biUnion.mp hp
  have hi1 : p.1 ∈ zeroA c i := (Finset.mem_product.mp hmem).1
  have hpi' : p.2 = i := Finset.mem_singleton.mp (Finset.mem_product.mp hmem).2
  have hpEq : p = (p.1, i) := Prod.ext (by rfl) hpi'
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun hslot => ?_⟩
  exact not_mem_Slots_of_zeroA hi1 (hpEq ▸ hslot)

/-- **THE NUMBER OF UNUSED SLOTS.** -/
theorem card_unused_slots {n k : ℕ} (c : Col n k) :
    ((Finset.univ : Finset (Verts n × Fin k)).filter fun p => p ∉ Slots c).card
      = n * k - (Slots c).card := by
  have key : (Finset.univ : Finset (Verts n × Fin k)).filter (fun p => p ∉ Slots c)
      = (Finset.univ : Finset (Verts n × Fin k)) \ Slots c := by
    ext p
    simp
  calc ((Finset.univ : Finset (Verts n × Fin k)).filter fun p => p ∉ Slots c).card
      = ((Finset.univ : Finset (Verts n × Fin k)) \ Slots c).card := by rw [key]
    _ = (Finset.univ : Finset (Verts n × Fin k)).card - (Slots c).card :=
      Finset.card_sdiff_of_subset (Finset.subset_univ _)
    _ = n * k - (Slots c).card := by rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
      Fintype.card_fin]

/-- **THE REFINED PACKING BOUND: `Isolated c + 5·|triSets c| ≤ n·k`.**

The `nk` slots split into the `5|triSets c|` used by the first stage and at least `Isolated c`
unused ones, so this is a strict sharpening of `Slot.slots_five` for every colouring with an
isolated `(vertex, colour)` cell — and the first statement of this development that combines the
defect accounting of `Surplus.lean` with the slot counting of `Cover.lean`. -/
theorem Isolated_add_five_mul_card_le {n k : ℕ} {c : Col n k} (hc : Admissible c) :
    Isolated c + 5 * (triSets c).card ≤ n * k := by
  have h5 : 5 * (triSets c).card ≤ n * k := slots_five (PairFree_of_admissible hc)
  have hbound : Isolated c ≤ n * k - 5 * (triSets c).card := by
    calc Isolated c = (isoPairs c).card := (card_isoPairs c).symm
      _ ≤ ((Finset.univ : Finset (Verts n × Fin k)).filter fun p => p ∉ Slots c).card :=
          Finset.card_le_card (isoPairs_subset_unused c)
      _ = n * k - (Slots c).card := card_unused_slots c
      _ = n * k - 5 * (triSets c).card := by rw [card_Slots (PairFree_of_admissible hc)]
  omega

/-! ### §4 — the price of a complete covering -/

/-- **UNDER A COMPLETE COVERING EVERY EDGE AT `v` IS USED, SO THE EDGE BUDGET IS AN EQUALITY.** -/
theorem covers_two_mul_card_atVertex {n k : ℕ} {c : Col n k} (hc : Admissible c) (hC : Covers c)
    (v : Verts n) : 2 * (atVertex c v).card = n - 1 := by
  have hbi : ((atVertex c v).biUnion fun T => T.erase v).card = 2 * (atVertex c v).card := by
    calc ((atVertex c v).biUnion fun T => T.erase v).card
        = ∑ T ∈ atVertex c v, (T.erase v).card := by
          exact Finset.card_biUnion (fun a ha b hb hab => by
            refine Finset.disjoint_left.2 fun x hx hxb => ?_
            have hmem : x ∈ a.erase v ∩ b.erase v := Finset.mem_inter.mpr ⟨hx, hxb⟩
            have hne' := inter_erase_v_eq_empty hc v ha hb hab
            rw [hne'] at hmem
            exact absurd hmem (by simp))
      _ = ∑ _T ∈ atVertex c v, (2 : ℕ) := by
          refine Finset.sum_congr rfl fun T hT => ?_
          exact card_erase_v_eq_two (mem_atVertex.mp hT).1 (mem_atVertex.mp hT).2
      _ = 2 * (atVertex c v).card := by rw [Finset.sum_const]; simp [Nat.mul_comm]
  have hsub : ((atVertex c v).biUnion fun T => T.erase v)
      ⊆ (Finset.univ : Finset (Verts n)).erase v := by
    intro x hx
    obtain ⟨T, hT, hxT⟩ := Finset.mem_biUnion.mp hx
    have hxv : x ≠ v := (Finset.mem_erase.mp hxT).1
    exact Finset.mem_erase.mpr ⟨hxv, Finset.mem_univ x⟩
  have hsub' : ((Finset.univ : Finset (Verts n)).erase v)
      ⊆ ((atVertex c v).biUnion fun T => T.erase v) := by
    intro x hx
    rw [Finset.mem_erase] at hx
    obtain ⟨hxv, hxu⟩ := hx
    have hC' : Covered c s(v, x) := hC _ (offDiag_iff.mpr hxv.symm)
    obtain ⟨T, hT, heT⟩ := mem_covered.mp (covered_of_Covered hC')
    have hmem : ∀ z : Verts n, z ∈ s(v, x) → z ∈ T := by
      intro z hz
      exact Finset.mem_sym2_iff.mp (mem_edgeFinset.mp heT).1 z hz
    rw [Finset.mem_biUnion]
    exact ⟨T, mem_atVertex.mpr ⟨hT, hmem v (by simp)⟩,
      Finset.mem_erase.mpr ⟨hxv, hmem x (by simp)⟩⟩
  calc 2 * (atVertex c v).card = ((atVertex c v).biUnion fun T => T.erase v).card := hbi.symm
    _ = ((Finset.univ : Finset (Verts n)).erase v).card := by
          apply le_antisymm
          · exact Finset.card_le_card hsub
          · exact hbi ▸ Finset.card_le_card hsub'
    _ = n - 1 := by simp

/-- **EVERY VERTEX LIES IN EXACTLY `(n-1)/2` TRIANGLES OF A COMPLETE COVERING.** -/
theorem covers_card_atVertex {n k : ℕ} {c : Col n k} (hc : Admissible c) (hC : Covers c)
    (v : Verts n) : (ApexPrice.apexTris c v).card + (leafTris c v).card = (n - 1) / 2 := by
  have h := covers_two_mul_card_atVertex hc hC v
  rw [card_atVertex_eq v] at h
  omega

/-- **A COMPLETE COVERING HAS EXACTLY `n(n-1)/6` TRIANGLES.** -/
theorem covers_six_mul_card {n k : ℕ} {c : Col n k} (hc : Admissible c) (hC : Covers c) :
    6 * (triSets c).card = n * (n - 1) := by
  have h1 := edgeCover_count (PairFree_of_admissible hc)
  have h2 := covers_iff_leftover_eq_empty.mp hC
  have h3 := card_edgeFinset_univ_two n
  rw [h2, Finset.card_empty] at h1
  omega

/-- **A VERTEX IS THE APEX OF AT LEAST `n - 1 - k` TRIANGLES**, in the division-free form
`n - 1 ≤ |apexTris c v| + k`. -/
theorem covers_apex_add {n k : ℕ} {c : Col n k} (hc : Admissible c) (hC : Covers c) (v : Verts n) :
    n - 1 ≤ (ApexPrice.apexTris c v).card + k := by
  have h1 := covers_two_mul_card_atVertex hc hC v
  have h2 := slotBudget hc v
  have h3 := card_atVertex_eq (c := c) v
  omega

theorem covers_apex_ge {n k : ℕ} {c : Col n k} (hc : Admissible c) (hC : Covers c) (v : Verts n) :
    n - 1 - k ≤ (ApexPrice.apexTris c v).card := by
  have h := covers_apex_add hc hC v
  omega

/-- **THE DOUBLED LEAF BOUND: `2·|leafTris c v| + (n-1) ≤ 2k`.** -/
theorem covers_two_mul_card_leafTris_add {n k : ℕ} {c : Col n k} (hc : Admissible c) (hC : Covers c)
    (v : Verts n) : 2 * (leafTris c v).card + (n - 1) ≤ 2 * k := by
  have h1 := covers_two_mul_card_atVertex hc hC v
  have h2 := slotBudget hc v
  have h3 := card_atVertex_eq (c := c) v
  omega

/-- **A VERTEX IS A LEAF OF AT MOST `k - (n-1)/2` TRIANGLES.** -/
theorem covers_leaf_le {n k : ℕ} {c : Col n k} (hc : Admissible c) (hC : Covers c) (v : Verts n) :
    (leafTris c v).card ≤ k - (n - 1) / 2 := by
  have h1 := covers_card_atVertex hc hC v
  have h2 := slotBudget hc v
  have h3 := card_atVertex_eq (c := c) v
  have h5 : (leafTris c v).card + (n - 1) / 2 ≤ k := by omega
  omega

/-- **IF THE PALETTE IS AT MOST `n-2` THEN EVERY VERTEX IS THE APEX OF A LABELLED TRIANGLE.** -/
theorem covers_apex_ge_one {n k : ℕ} {c : Col n k} (hc : Admissible c) (hC : Covers c)
    (hn : 2 ≤ n) (hk : k ≤ n - 2) (v : Verts n) : 0 < (ApexPrice.apexTris c v).card := by
  have h := covers_apex_add hc hC v
  have hk1 : k + 1 ≤ n - 1 := by rw [← Nat.sub_add_cancel hn]; omega
  have h2 : k + 1 ≤ (ApexPrice.apexTris c v).card + k := by omega
  omega

/-- **EVERY VERTEX HAS AN ISOLATED CELL: `n ≤ Isolated c`.**  Every vertex is the apex of a
labelled triangle, and by `Strict.apex_zeroA` an apex misses a colour entirely. -/
theorem covers_isolated_ge {n k : ℕ} {c : Col n k} (hc : Admissible c) (hC : Covers c)
    (hn : 2 ≤ n) (hk : k ≤ n - 2) : (Finset.univ : Finset (Verts n)).card ≤ Isolated c := by
  have key : ∀ v : Verts n, ∃ i : Fin k, v ∈ zeroA c i := by
    intro v
    exact ApexPrice.zeroA_of_mem_apexVerts hc
      (ApexPrice.mem_apexVerts.mpr (Nat.ne_of_gt (covers_apex_ge_one hc hC hn hk v)))
  have hone : ∀ v : Verts n,
      (1 : ℕ) ≤ ∑ i : Fin k, (if v ∈ zeroA c i then 1 else 0) := by
    intro v
    obtain ⟨i, hi⟩ := key v
    have h1 : (∑ j : Fin k, (if v ∈ zeroA c j then (1 : ℕ) else 0))
        = ((Finset.univ : Finset (Fin k)).filter fun j => v ∈ zeroA c j).card :=
          Finset.sum_boole _ _
    rw [h1]
    exact Finset.card_le_card (Finset.singleton_subset_iff.mpr
      (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩))
  calc (Finset.univ : Finset (Verts n)).card = ∑ _v : Verts n, (1 : ℕ) := by
        rw [← Finset.card_eq_sum_ones]
    _ ≤ ∑ v : Verts n, ∑ i : Fin k, (if v ∈ zeroA c i then (1 : ℕ) else 0) :=
        Finset.sum_le_sum fun v _ => hone v
    _ = ∑ i : Fin k, ∑ v : Verts n, (if v ∈ zeroA c i then (1 : ℕ) else 0) := by
        rw [Finset.sum_comm]
    _ = ∑ i : Fin k, (zeroA c i).card := by
        refine Finset.sum_congr rfl fun i _ => ?_
        have h1 : (∑ v : Verts n, (if v ∈ zeroA c i then (1 : ℕ) else 0))
            = ((Finset.univ : Finset (Verts n)).filter fun v => v ∈ zeroA c i).card :=
              Finset.sum_boole _ _
        have h2 : ((Finset.univ : Finset (Verts n)).filter fun v : Verts n => v ∈ zeroA c i)
            = zeroA c i := by
          ext v
          simp
        rw [h1, h2]
    _ = Isolated c := rfl

/-- **THE PRICE OF A COMPLETE FIRST STAGE: `5(n-1) + 6 ≤ 6k`.**

A complete labelled-triangle covering of `K_n` with a palette of at most `n-2` colours has
`6|triSets c| = n(n-1)` triangles, so `5|triSets c| = 5n(n-1)/6` slots, **and** every vertex has an
isolated cell, i.e. at least `n` slots are wasted; `Isolated_add_five_mul_card_le` then forces

    `k ≥ 5(n-1)/6 + 1`.

This is strictly stronger than round 89's `ApexPrice.covered_price` (`5n - 3 ≤ 6k`, i.e.
`5(n-1)/6 + 1/3`): a complete first stage must pay a **whole** extra colour, not a third of one. -/
theorem covers_price {n k : ℕ} {c : Col n k} (hc : Admissible c) (hC : Covers c)
    (hn : 2 ≤ n) (hk : k ≤ n - 2) : 5 * (n - 1) + 6 ≤ 6 * k := by
  have h1 := Isolated_add_five_mul_card_le hc
  have h2 := covers_isolated_ge hc hC hn hk
  have h3 := covers_six_mul_card hc hC
  have hn0 : 0 < n := by omega
  have h6 : 6 * (Isolated c + 5 * (triSets c).card) ≤ 6 * (n * k) := by
    have h := Nat.mul_le_mul_right 6 h1
    simpa [Nat.mul_comm] using h
  have h7 : 6 * n ≤ 6 * Isolated c := by
    have h := Nat.mul_le_mul_right 6 h2
    simpa [Nat.mul_comm] using h
  have h9 : 30 * (triSets c).card = 5 * n * (n - 1) := by
    have h := congrArg (fun t => 5 * t) h3
    calc 30 * (triSets c).card = 5 * (6 * (triSets c).card) := by ring
      _ = 5 * (n * (n - 1)) := h
      _ = 5 * n * (n - 1) := by ring
  have h8 : 6 * n + 30 * (triSets c).card ≤ 6 * (n * k) := by
    calc 6 * n + 30 * (triSets c).card ≤ 6 * Isolated c + 30 * (triSets c).card :=
          Nat.add_le_add_right h7 _
      _ = 6 * (Isolated c + 5 * (triSets c).card) := by
          have h' : 30 * (triSets c).card = 6 * (5 * (triSets c).card) := by ring
          rw [h']
          ring
      _ ≤ 6 * (n * k) := h6
  have key : n * (5 * (n - 1) + 6) ≤ n * (6 * k) := by
    calc n * (5 * (n - 1) + 6) = 5 * (n * (n - 1)) + 6 * n := by ring
      _ = 30 * (triSets c).card + 6 * n := by omega
      _ ≤ 6 * (n * k) := by simpa [Nat.add_comm] using h8
      _ = n * (6 * k) := by ring
  exact Nat.le_of_mul_le_mul_left key hn0

/-- **THE PRICE IN REAL FORM: `k ≥ 5(n-1)/6 + 1`.** -/
theorem covers_price_real {n k : ℕ} {c : Col n k} (hc : Admissible c) (hC : Covers c)
    (hn : 2 ≤ n) (hk : k ≤ n - 2) : (5 : ℝ) * ((n - 1 : ℕ) : ℝ) / 6 + 1 ≤ (k : ℝ) := by
  have h := covers_price hc hC hn hk
  have h' : (5 : ℝ) * ((n - 1 : ℕ) : ℝ) + 6 ≤ 6 * (k : ℝ) := by exact_mod_cast h
  linarith

/-- **THE APEX DILEMMA OF A COMPLETE FIRST STAGE:** either *every* vertex is the apex of a
labelled triangle (and then §3–§4 pay a whole extra colour, `covers_price`), or the palette is
at least `n-1` — much worse than the catalogue rate.  So there is no third way: a first stage with
fewer than `n-1` colours is forced to use its apexes at every vertex, and hence to waste a slot at
every vertex. -/
theorem covers_apex_or_palette {n k : ℕ} {c : Col n k} (hc : Admissible c) (hC : Covers c)
    (hn : 2 ≤ n) : (∀ v : Verts n, 0 < (ApexPrice.apexTris c v).card) ∨ (n - 1) ≤ k := by
  by_cases hall : ∀ v : Verts n, 0 < (ApexPrice.apexTris c v).card
  · exact Or.inl hall
  · right
    push_neg at hall
    obtain ⟨v, hv⟩ := hall
    have hv0 : (ApexPrice.apexTris c v).card = 0 := Nat.eq_zero_of_le_zero hv
    have h1 := covers_two_mul_card_atVertex hc hC v
    have h2 := slotBudget hc v
    have h3 := card_atVertex_eq (c := c) v
    rw [hv0] at h2 h3
    omega

/-- **A COMPLETE COVERING NEVER ATTAINS THE CATALOGUE RATE:** with `2 ≤ n`, no admissible
`k`-colouring of `K_n` whose edges are all covered by labelled triangles satisfies
`6k = 5(n-1)`.  So the exact counting bound is unreachable by a complete first stage — which is
why arXiv:2208.12563 §4 needs the second stage. -/
theorem covers_not_extremal {n k : ℕ} {c : Col n k} (hc : Admissible c) (hC : Covers c)
    (hn : 2 ≤ n) : ¬ (6 * k = 5 * (n - 1)) := by
  by_cases hk : k ≤ n - 2
  · intro h6
    exact absurd (covers_price hc hC hn hk) (by rw [h6]; omega)
  · intro h6
    exfalso
    have hnk : n - 1 ≤ k := by
      have hlt : n - 2 < k := Nat.lt_of_not_ge hk
      have hstep : n - 2 + 1 ≤ k := Nat.succ_le_of_lt hlt
      have hle : n - 1 ≤ n - 2 + 1 := by omega
      exact le_trans hle hstep
    have hstep : 6 * (n - 1) ≤ 6 * k := by omega
    rw [h6] at hstep
    have hz : n - 1 = 0 := by omega
    have hD : 1 ≤ n - 1 := by omega
    omega

/-- **THE RESIDUAL OF A COMPLETE FIRST STAGE IS AT LEAST `6`: with `k ≤ n-2`, the equation
`6k = 5(n-1) + r` forces `6 ≤ r`.**  (The regime `k ≤ n-2` is the one of the catalogue rate:
`5(n-1)/6 ≤ n-2` for `n ≥ 7`.) -/
theorem covers_residual_ge {n k r : ℕ} {c : Col n k} (hc : Admissible c) (hC : Covers c)
    (hn : 2 ≤ n) (hk : k ≤ n - 2) (h6 : 6 * k = 5 * (n - 1) + r) : 6 ≤ r := by
  have h := covers_price hc hC hn hk
  omega

/-- **THE PRICE IN THE FORM OF THE PUBLISHED TWO-STAGE HYPOTHESIS.**  If the first stage of
arXiv:2208.12563 §4 is a complete covering and the whole construction respects the published
budget `6(k+K) ≤ 5(n-1) + δn`, then **`δn ≥ 6`**: the two stages together cannot be within six
units of the counting bound.  So either the first stage leaves a leftover graph (and the second
stage — `K ≥ 1` fresh colours — is *necessary*), or the published accuracy must pay. -/
theorem covers_two_stage_price {n k K : ℕ} {c : Col n k} (hc : Admissible c) (hC : Covers c)
    (hn : 2 ≤ n) (hk : k ≤ n - 2) {δ : ℝ} (hδ : 0 < δ)
    (hbudget : (6 : ℝ) * ((k + K : ℕ) : ℝ) ≤ 5 * ((n - 1 : ℕ) : ℝ) + δ * (n : ℝ)) :
    6 ≤ δ * (n : ℝ) := by
  have hreal : (5 : ℝ) * ((n - 1 : ℕ) : ℝ) + 6 ≤ (6 : ℝ) * ((k : ℕ) : ℝ) := by
    have h := covers_price hc hC hn hk
    exact_mod_cast h
  have hkK : (6 : ℝ) * ((k : ℕ) : ℝ) ≤ (6 : ℝ) * ((k + K : ℕ) : ℝ) := by
    have h1 : ((k : ℕ) : ℝ) ≤ ((k + K : ℕ) : ℝ) := Nat.cast_le.2 (by omega)
    exact mul_le_mul_of_nonneg_left h1 (by norm_num)
  have hmain : (5 : ℝ) * ((n - 1 : ℕ) : ℝ) + 6 ≤ 5 * ((n - 1 : ℕ) : ℝ) + δ * (n : ℝ) :=
    le_trans (le_trans hreal hkK) hbudget
  linarith

/-! ### §5 — the workload of the second stage -/

/-- **THE WORKLOAD OF THE SECOND STAGE, PER VERTEX: `Σ_v degAt c v = 2·|leftover c|`.**
The leftover graph `L` of arXiv:2208.12563 §4 has degree `degAt c v` at `v`, and its edges are
counted twice by this sum — the per-vertex form of `edgeCover_count`. -/
theorem sum_degAt_eq_two_mul_leftover {n k : ℕ} {c : Col n k} (hc : Admissible c) :
    (∑ v : Verts n, degAt c v) = 2 * (leftover c).card := by
  have h1 := sum_card_atVertex (c := c)
  have h2 := edgeCover_count (PairFree_of_admissible hc)
  have h3 := card_edgeFinset_univ_two n
  have hkey : ((∑ v : Verts n, degAt c v) + ∑ v : Verts n, (2 * (atVertex c v).card))
      = ∑ v : Verts n, (n - 1) := by
    have hpoint : ∀ v : Verts n, degAt c v + 2 * (atVertex c v).card = n - 1 := by
      intro v
      have hle := two_mul_card_atVertex_le hc v
      unfold degAt
      omega
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun v _ => hpoint v
  have hA : (∑ v : Verts n, (2 * (atVertex c v).card)) = 6 * (triSets c).card := by
    have hB : (∑ v : Verts n, (2 * (atVertex c v).card))
        = 2 * ∑ v : Verts n, (atVertex c v).card := by rw [Finset.mul_sum]
    rw [hB, h1]
    ring
  have hB' : (∑ v : Verts n, (n - 1)) = n * (n - 1) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    simp
  have h4 : n * (n - 1) = 2 * (3 * (triSets c).card + (leftover c).card) := by
    rw [← h2, h3]
  calc (∑ v : Verts n, degAt c v)
      = (∑ v : Verts n, (n - 1)) - ∑ v : Verts n, (2 * (atVertex c v).card) := by
        rw [← hkey, Nat.add_sub_cancel]
    _ = n * (n - 1) - 6 * (triSets c).card := by rw [hB', hA]
    _ = 2 * (leftover c).card := by omega

end VertexBudget
end JSP140
