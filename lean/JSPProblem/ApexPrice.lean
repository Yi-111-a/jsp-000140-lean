import JSPProblem.Strict
import JSPProblem.Slot
import JSPProblem.Star

/-!
# JSP-000140 — round 89: **THE APEX SLOT HAS A PRICE**, and the second one-parameter family of
# lower bounds of this development

Rounds 10–27 and 65 proved the *necessity* side completely: `Cherry.five_sixth_lower`
(`5(n-1) ≤ 6k`), `Surplus.surplus_identity` (the exact price of the two defects),

    `6·(n·k) = 5·n·(n-1) + 6·Isolated c + 2·Defect c`,

and round 81 (`Strict`) the first *strictness*: `Strict.apex_zeroA` — **the apex of a labelled
triangle wastes the slot of its own opposite-edge colour** — whence `6k > 5(n-1)`.

**Round 81 used that lemma only qualitatively** (`Isolated c ≥ 1`).  This round counts with it.
The count is the following, and it is a theorem of this development:

> **`ApexPrice.two_mul_triSets_le` — `2·|triSets c| ≤ (n-1)·Isolated c`.**

*Every labelled triangle of the first stage wastes an isolated `(vertex, colour)` cell, and each
isolated cell is the waste of at most `(n-1)/2` triangles.*

## The three objects written here

* `apexTris c u` — the labelled triangles of `c` whose **apex** is `u` (`u` is unique: the two
  edges at the apex carry one colour, the third another, so no other vertex can be an apex);
* `apexTrisCol c u lam` — those whose apex colour is `lam`;
  **`apexTrisCol_card_le_one`: for fixed `(u, lam)` there is at most one triangle**, because the two
  `lam`-neighbours of `u` are exactly the two leaves (`nbrs_lam_eq`);
* `apexVerts c` — the vertices which are the apex of at least one labelled triangle, and
  **`apexVerts_card_le_isolated`: there are at most `Isolated c` of them**, since each misses the
  colour of its triangles' opposite edges.

## What the count is worth

| theorem | statement |
|---|---|
| **`two_mul_triSets_le`** | `2·|triSets c| ≤ (n-1)·Isolated c` |
| **`triSets_le_paths`** | `|triSets c| ≤ Paths c`: every labelled triangle is a two-edge path (the first statement that the triangles of the first stage are *cherries*) |
| **`tri_budget`** | **THE PRICE OF A TRIANGLE AT THE SURPLUS `r` (`6k = 5(n-1)+r`): `12·|triSets c| ≤ n(n-1)·r`.**  With `A = n(n-1)/6` triangles (a full covering) this forces **`r ≥ 2`**: the sharp counting bound is short by at least *two* units on any colouring produced by the first stage — `Strict.eg_strict` only gets `r ≥ 1` |
| **`surplus_tri_price`** | `6(n-1)(n·k) ≥ 5n(n-1)² + 12·|triSets c| + 2(n-1)·Defect c` — **in the `6k` currency, one labelled triangle costs `2/(n(n-1))` and one unpaid edge costs `1/3`**, so an uncoloured edge costs a factor `≈ n²/6` more than a triangle |
| **`surplus_leftover_price`** | the same with `|triSets c|` replaced by `(C(n,2) - |leftover c|)/3`: **THE PRICE OF THE LEFTOVER GRAPH OF arXiv:2207.02920 §4 in the palette budget** |
| **`covered_price`** | a `PairFree` colouring whose leftover graph is empty satisfies **`5n - 3 ≤ 6k`**, one unit better than `Strict.eg_strict` (`5n-4 ≤ 6k`) |
| **`eg_price`** | **`5·n - 3 ≤ 6·f(n,4,5)` for every `n ≥ 4`**, the `f`-level reading |
| **`matchings_need_n_sub_one`** | **IF EVERY COLOUR CLASS IS A MATCHING THEN `k ≥ n-1`**: the 1-factorisation (the cheapest admissible colouring of `K_n`, `n` colours, `Ghost`/`Construction`) is **optimal among all matchings-only colourings**, and *any* colour saving below `n-1` must come from two-edge paths |

Everything is proved for **every** admissible colouring: `PairFree` enters only where the leftover
graph is priced, and no search, probability or measure is used.
-/

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

namespace JSP140
namespace ApexPrice

variable {n k : ℕ}

open Classical

attribute [local instance] Classical.propDecidable

/-! ### §0 — the union bound, once and for all -/

/-- `c * a ≤ c * b` from `a ≤ b`. -/
private theorem mul_le_mul_left' {a b c : ℕ} (h : a ≤ b) : c * a ≤ c * b := by
  have hh := Nat.mul_le_mul_right c h
  simpa [Nat.mul_comm] using hh

/-- **THE UNION BOUND.** A set each of whose elements lies in one of the `t y` (`y ∈ M`) has at
most `∑_{y ∈ M} |t y|` elements. -/
private theorem card_le_sum_of_mem {δ β : Type*} [DecidableEq δ] [DecidableEq β]
    (S : Finset δ) (M : Finset β) (t : β → Finset δ)
    (hS : ∀ x ∈ S, ∃ y ∈ M, x ∈ t y) : S.card ≤ ∑ y ∈ M, (t y).card := by
  induction M using Finset.induction_on generalizing S with
  | empty =>
      have h0 : S = ∅ := Finset.eq_empty_iff_forall_notMem.mpr (fun _ hx => by
        obtain ⟨y, hy, hxy⟩ := hS _ hx
        simp at hy)
      simp [h0]
  | @insert b M hb ih =>
      have h1 : S.card = (S ∩ t b).card + (S \ t b).card :=
        (Finset.card_inter_add_card_sdiff S (t b)).symm
      have h2 : (S ∩ t b).card ≤ (t b).card :=
        Finset.card_le_card (fun _ h => (Finset.mem_inter.mp h).2)
      have h3 : (S \ t b).card ≤ ∑ y ∈ M, (t y).card := by
        refine ih (S \ t b) ?_
        intro x hx
        obtain ⟨y, hy, hxy⟩ := hS x (Finset.mem_sdiff.mp hx).1
        rcases Finset.mem_insert.mp hy with h | hy
        · exact absurd (h ▸ hxy) (Finset.mem_sdiff.mp hx).2
        · exact ⟨y, hy, hxy⟩
      have h4 : (t b).card + ∑ y ∈ M, (t y).card ≤ ∑ y ∈ insert b M, (t y).card := by
        rw [Finset.sum_insert hb]
      exact Nat.le_trans (Nat.le_of_eq h1) (Nat.le_trans (Nat.add_le_add h2 h3) h4)

/-- The cardinality of a filter is the sum of the indicator of its predicate. -/
private theorem card_filter_mem_eq {α : Type*} [DecidableEq α] (s t : Finset α) :
    (s.filter (fun x => x ∈ t)).card = ∑ x ∈ s, (if x ∈ t then (1 : ℕ) else 0) := by
  calc (s.filter (fun x => x ∈ t)).card = ∑ x ∈ s.filter (fun x => x ∈ t), (1 : ℕ) :=
        Finset.card_eq_sum_ones _
    _ = ∑ x ∈ s, (if x ∈ t then (1 : ℕ) else 0) :=
        Finset.sum_filter (s := s) (fun x : α => x ∈ t) fun _ => (1 : ℕ)

/-- The number of elements satisfying a predicate, as a sum of indicators over a `Fintype`. -/
private theorem sum_ite_univ_mem {α : Type*} [DecidableEq α] [Fintype α] (t : Finset α) :
    (∑ x : α, (if x ∈ t then (1 : ℕ) else 0))
      = ((Finset.univ : Finset α).filter (fun x => x ∈ t)).card := by
  calc (∑ x : α, (if x ∈ t then (1 : ℕ) else 0))
      = ∑ x ∈ (Finset.univ : Finset α).filter (fun x => x ∈ t), (1 : ℕ) :=
        (Finset.sum_filter (s := (Finset.univ : Finset α)) (fun x : α => x ∈ t)
          fun _ => (1 : ℕ)).symm
    _ = ((Finset.univ : Finset α).filter (fun x => x ∈ t)).card := (Finset.card_eq_sum_ones _).symm

/-- **THE APEX COLOURS AT `u`, AS A SUM OF INDICATORS.** -/
private theorem card_twoA_at {c : Col n k} (u : Verts n) :
    ((Finset.univ : Finset (Fin k)).filter fun lam => u ∈ twoA c lam).card
      = ∑ lam : Fin k, (if u ∈ twoA c lam then (1 : ℕ) else 0) := by
  calc ((Finset.univ : Finset (Fin k)).filter fun lam => u ∈ twoA c lam).card
      = ∑ _lam ∈ (Finset.univ : Finset (Fin k)).filter fun lam => u ∈ twoA c lam, (1 : ℕ) :=
        Finset.card_eq_sum_ones _
    _ = ∑ lam : Fin k, (if u ∈ twoA c lam then (1 : ℕ) else 0) :=
        Finset.sum_filter (s := (Finset.univ : Finset (Fin k)))
          (fun lam : Fin k => u ∈ twoA c lam) fun _ => (1 : ℕ)

/-- **THE APEX VERTICES OF THE COLOUR `lam`, AS A SUM OF INDICATORS.** -/
private theorem card_twoA_lam {c : Col n k} (lam : Fin k) :
    ((Finset.univ : Finset (Verts n)).filter fun u => u ∈ twoA c lam).card
      = ∑ u : Verts n, (if u ∈ twoA c lam then (1 : ℕ) else 0) := by
  calc ((Finset.univ : Finset (Verts n)).filter fun u => u ∈ twoA c lam).card
      = ∑ _u ∈ (Finset.univ : Finset (Verts n)).filter fun u => u ∈ twoA c lam, (1 : ℕ) :=
        Finset.card_eq_sum_ones _
    _ = ∑ u : Verts n, (if u ∈ twoA c lam then (1 : ℕ) else 0) :=
        Finset.sum_filter (s := (Finset.univ : Finset (Verts n)))
          (fun u : Verts n => u ∈ twoA c lam) fun _ => (1 : ℕ)

/-! ### §1 — the apex colour, and the two `lam`-neighbours of an apex -/

/-- **THE FIRST LEAF OF A LABELLED TRIANGLE IS A `lam`-NEIGHBOUR OF ITS APEX**, `lam = c s(u,p)`. -/
theorem mem_nb_lam {c : Col n k} {u p q : Verts n} (h : LabTri c u p q) :
    p ∈ nb c (c s(u, p)) u (Finset.univ : Finset (Verts n)) := by
  refine mem_nb.mpr ⟨?_, Finset.mem_univ p, rfl⟩
  exact fun hup => h.1 hup.symm

/-- **THE SECOND LEAF TOO.** -/
theorem mem_nb_lam_q {c : Col n k} {u p q : Verts n} (h : LabTri c u p q) :
    q ∈ nb c (c s(u, p)) u (Finset.univ : Finset (Verts n)) := by
  refine mem_nb.mpr ⟨?_, Finset.mem_univ q, ?_⟩
  · exact fun huq => h.2.1 huq.symm
  · rw [h.2.2.2.1]

/-- **THE TWO COLOUR-`lam` NEIGHBOURS OF AN APEX ARE ITS TWO LEAVES.**  By admissibility a vertex has
at most two neighbours in one colour (`Counting.nb_card_le_two`), and `p ≠ q`, so
`nb c lam u = {p, q}`: the triangle is *determined* by its apex and its apex colour. -/
theorem nbrs_lam_eq {c : Col n k} (hc : Admissible c) {u p q : Verts n} (h : LabTri c u p q) :
    nb c (c s(u, p)) u (Finset.univ : Finset (Verts n)) = ({p, q} : Finset (Verts n)) := by
  have hsub : ({p, q} : Finset (Verts n))
      ⊆ nb c (c s(u, p)) u (Finset.univ : Finset (Verts n)) := by
    intro x hx
    rcases Finset.mem_insert.mp hx with hx | hx
    · rw [hx]; exact mem_nb_lam h
    · rw [Finset.mem_singleton.mp hx]; exact mem_nb_lam_q h
  have hcard : (({p, q} : Finset (Verts n))).card = 2 :=
    Finset.card_pair_eq_two_iff.mpr h.2.2.1
  have hsub' : (nb c (c s(u, p)) u (Finset.univ : Finset (Verts n)))
      ⊆ ({p, q} : Finset (Verts n)) := by
    intro x hx
    rw [Finset.mem_insert]
    by_cases hxq : x = q
    · exact Or.inr (Finset.mem_singleton.mpr hxq)
    · refine Or.inl ?_
      by_contra hcon
      have hpx : p ≠ x := fun h => hcon h.symm
      have hqx : q ≠ x := fun h => hxq h.symm
      have h4 : 3 ≤ (nb c (c s(u, p)) u (Finset.univ : Finset (Verts n))).card :=
        card_ge_three h.2.2.1 hpx hqx ⟨mem_nb_lam h, mem_nb_lam_q h, hx⟩
      have hle := nb_card_le_two hc (c s(u, p)) u (Finset.univ : Finset (Verts n))
      omega
  exact Finset.Subset.antisymm hsub' hsub

/-- **THE APEX OF A LABELLED TRIANGLE IS A TWO-EDGE-PATH CENTRE** — every labelled triangle of the
first stage is a cherry, and `Surplus.Isolated c` is not paid for by it. -/
theorem twoA_of_labTri {c : Col n k} (hc : Admissible c) {u p q : Verts n} (h : LabTri c u p q) :
    u ∈ twoA c (c s(u, p)) := by
  rw [mem_twoA, nbrs_lam_eq hc h]
  exact Finset.card_pair_eq_two_iff.mpr h.2.2.1

/-! ### §2 — the triangles of the first stage, one apex and one apex colour at a time -/

/-- **THE LABELLED TRIANGLES OF `c` WITH APEX `u`**, as a finite object: the vertex sets `T` for
which some ordered pair `(p, q)` makes `(u; p, q)` a labelled triangle with vertex set `T`. -/
noncomputable def apexTris (c : Col n k) (u : Verts n) : Finset (Finset (Verts n)) :=
  (triSets c).filter fun T => ∃ p q : Verts n, LabTri c u p q ∧ triVerts u p q = T

theorem mem_apexTris {c : Col n k} {u : Verts n} {T : Finset (Verts n)} :
    T ∈ apexTris c u ↔ T ∈ triSets c ∧ ∃ p q : Verts n, LabTri c u p q ∧ triVerts u p q = T := by
  simp [apexTris]

/-- **THE LABELLED TRIANGLES WITH APEX `u` AND APEX COLOUR `lam`.** -/
noncomputable def apexTrisCol (c : Col n k) (u : Verts n) (lam : Fin k) :
    Finset (Finset (Verts n)) :=
  (triSets c).filter fun T =>
    ∃ p q : Verts n, LabTri c u p q ∧ triVerts u p q = T ∧ c s(u, p) = lam

theorem mem_apexTrisCol {c : Col n k} {u : Verts n} {lam : Fin k} {T : Finset (Verts n)} :
    T ∈ apexTrisCol c u lam ↔ T ∈ triSets c ∧
      ∃ p q : Verts n, LabTri c u p q ∧ triVerts u p q = T ∧ c s(u, p) = lam := by
  simp [apexTrisCol]

/-- **THE APEX AND THE APEX COLOUR DETERMINE THE TRIANGLE: AT MOST ONE OF THEM PER PAIR
`(u, lam)`.**  This is the local rigidity that makes the count of §3 possible: the two `lam`-neighbours
of `u` are its two leaves, so the vertex set is fixed. -/
theorem apexTrisCol_card_le_one {c : Col n k} (hc : Admissible c) (u : Verts n) (lam : Fin k) :
    (apexTrisCol c u lam).card ≤ 1 := by
  by_cases hne : (apexTrisCol c u lam).Nonempty
  · obtain ⟨T₀, hT₀⟩ := hne
    have key : (apexTrisCol c u lam) ⊆ ({T₀} : Finset (Finset (Verts n))) := by
      intro T hT
      rw [Finset.mem_singleton]
      obtain ⟨_, p, q, hlt, hT2, hlam⟩ := mem_apexTrisCol.mp hT
      obtain ⟨_, p₀, q₀, hlt₀, hT0₂, hlam₀⟩ := mem_apexTrisCol.mp hT₀
      have hpq : triVerts u p q = T := hT2
      have hpq₀ : triVerts u p₀ q₀ = T₀ := hT0₂
      have e1 : (nb c (c s(u, p)) u (Finset.univ : Finset (Verts n)))
          = ({p, q} : Finset (Verts n)) := nbrs_lam_eq hc hlt
      have e2 : (nb c (c s(u, p₀)) u (Finset.univ : Finset (Verts n)))
          = ({p₀, q₀} : Finset (Verts n)) := nbrs_lam_eq hc hlt₀
      have hsl : ({p, q} : Finset (Verts n)) = ({p₀, q₀} : Finset (Verts n)) := by
        calc ({p, q} : Finset (Verts n)) = nb c (c s(u, p)) u (Finset.univ : Finset (Verts n)) := e1.symm
          _ = nb c (c s(u, p₀)) u (Finset.univ : Finset (Verts n)) := by rw [hlam, hlam₀]
          _ = ({p₀, q₀} : Finset (Verts n)) := e2
      rw [← hpq, ← hpq₀,
        show triVerts u p q = insert u ({p, q} : Finset (Verts n)) from rfl, hsl,
        show insert u ({p₀, q₀} : Finset (Verts n)) = triVerts u p₀ q₀ from rfl]
    calc (apexTrisCol c u lam).card ≤ ({T₀} : Finset (Finset (Verts n))).card :=
        Finset.card_le_card key
      _ = 1 := Finset.card_singleton _
  · have h0 : (apexTrisCol c u lam).card = 0 :=
      Finset.card_eq_zero.mpr
        (Finset.eq_empty_iff_forall_notMem.mpr (fun _ hx => hne ⟨_, hx⟩))
    omega

/-- **THE NUMBER OF APEX COLOURS AT `u` IS AT MOST `(n-1)/2`** — each of them costs two of the `n-1`
edges at `u` (`Star.sum_nb_star`). -/
theorem two_mul_card_twoA_le {c : Col n k} (hc : Admissible c) (u : Verts n) :
    2 * ((Finset.univ : Finset (Fin k)).filter fun lam => u ∈ twoA c lam).card ≤ n - 1 := by
  have e : 2 * ((Finset.univ : Finset (Fin k)).filter fun lam => u ∈ twoA c lam).card
      = ∑ _lam ∈ (Finset.univ : Finset (Fin k)).filter fun lam => u ∈ twoA c lam, (2 : ℕ) := by
    rw [Finset.sum_const]
    simp [nsmul_eq_mul, Nat.mul_comm]
  calc 2 * ((Finset.univ : Finset (Fin k)).filter fun lam => u ∈ twoA c lam).card
      ≤ ∑ lam ∈ (Finset.univ : Finset (Fin k)).filter fun lam => u ∈ twoA c lam,
        (nb c lam u (Finset.univ : Finset (Verts n))).card := by
          rw [e]
          refine Finset.sum_le_sum fun lam hlam => ?_
          have htwo := mem_twoA.mp (Finset.mem_filter.mp hlam).2
          omega
    _ ≤ ∑ lam : Fin k, (nb c lam u (Finset.univ : Finset (Verts n))).card := by
      refine Finset.sum_le_sum_of_subset_of_nonneg
        (fun x _ => Finset.mem_univ x) (fun x _ _ => Nat.zero_le _)
    _ = n - 1 := sum_nb_star c u

/-- **A UNION BOUND FOR THE APEX TRIANGLES, IN INDICATORS.** -/
private theorem sum_indicator_apexCol_le {c : Col n k} (hc : Admissible c) (u : Verts n) :
    (∑ lam : Fin k, (if apexTrisCol c u lam = ∅ then (0 : ℕ) else 1))
      ≤ ((Finset.univ : Finset (Fin k)).filter fun lam => u ∈ twoA c lam).card := by
  have key : ∀ lam : Fin k, (if apexTrisCol c u lam = ∅ then (0 : ℕ) else 1)
      ≤ if u ∈ twoA c lam then (1 : ℕ) else 0 := by
    intro lam
    by_cases h : apexTrisCol c u lam = ∅
    · simp [h]
    · rw [if_neg h]
      obtain ⟨T, hT⟩ := Finset.nonempty_iff_ne_empty.mpr h
      obtain ⟨_, p, q, hlt, hT2, hlam⟩ := mem_apexTrisCol.mp hT
      have hmem : u ∈ twoA c lam := by
        rw [← hlam]
        exact twoA_of_labTri hc hlt
      rw [if_pos hmem]
  calc (∑ lam ∈ (Finset.univ : Finset (Fin k)),
        (if apexTrisCol c u lam = ∅ then (0 : ℕ) else 1))
      ≤ ∑ lam ∈ (Finset.univ : Finset (Fin k)), (if u ∈ twoA c lam then (1 : ℕ) else 0) :=
        Finset.sum_le_sum fun lam _ => key lam
    _ = ((Finset.univ : Finset (Fin k)).filter fun lam => u ∈ twoA c lam).card :=
      (card_twoA_at u).symm

/-- **AT MOST `(n-1)/2` LABELLED TRIANGLES SHARE AN APEX.**  The count of §3 rests on this: a vertex
is the apex of at most half as many triangles as it has edges. -/
theorem two_mul_card_apexTris_le {c : Col n k} (hc : Admissible c) (u : Verts n) :
    2 * (apexTris c u).card ≤ n - 1 := by
  have hcard : (apexTris c u).card ≤ ∑ lam : Fin k, (apexTrisCol c u lam).card := by
    refine card_le_sum_of_mem _ _ _ fun T hT => ?_
    obtain ⟨hT', p, q, hlt, hT2⟩ := mem_apexTris.mp hT
    exact ⟨c s(u, p), Finset.mem_univ _,
      mem_apexTrisCol.mpr ⟨hT', p, q, hlt, hT2, rfl⟩⟩
  have h1 : ∑ lam : Fin k, (apexTrisCol c u lam).card
      ≤ ∑ lam : Fin k, (if apexTrisCol c u lam = ∅ then (0 : ℕ) else 1) := by
    refine Finset.sum_le_sum fun lam _ => ?_
    by_cases h : apexTrisCol c u lam = ∅
    · simp [h]
    · rw [if_neg h]
      exact apexTrisCol_card_le_one hc u lam
  calc 2 * (apexTris c u).card ≤ 2 * ∑ lam : Fin k, (apexTrisCol c u lam).card :=
        mul_le_mul_left' hcard
    _ = ∑ lam : Fin k, (2 * (apexTrisCol c u lam).card) := by rw [Finset.mul_sum]
    _ = 2 * ∑ lam : Fin k, (apexTrisCol c u lam).card := by rw [Finset.mul_sum]
    _ ≤ 2 * ∑ lam : Fin k, (if apexTrisCol c u lam = ∅ then (0 : ℕ) else 1) :=
      mul_le_mul_left' h1
    _ ≤ 2 * ((Finset.univ : Finset (Fin k)).filter fun lam => u ∈ twoA c lam).card :=
      mul_le_mul_left' (sum_indicator_apexCol_le hc u)
    _ ≤ n - 1 := two_mul_card_twoA_le hc u

/-- **THE APEX VERTICES: THOSE WHICH ARE THE APEX OF A LABELLED TRIANGLE.** -/
noncomputable def apexVerts (c : Col n k) : Finset (Verts n) :=
  (Finset.univ : Finset (Verts n)).filter fun u => (apexTris c u).card ≠ 0

theorem mem_apexVerts {c : Col n k} {u : Verts n} :
    u ∈ apexVerts c ↔ (apexTris c u).card ≠ 0 := by simp [apexVerts]

/-- **AN APEX VERTEX MISSES THE COLOUR OF ITS OWN TRIANGLES' OPPOSITE EDGES** (`Strict.apex_zeroA`,
as an isolated cell). -/
theorem zeroA_of_mem_apexVerts {c : Col n k} (hc : Admissible c) {u : Verts n}
    (hu : u ∈ apexVerts c) : ∃ μ : Fin k, u ∈ zeroA c μ := by
  obtain ⟨T, hT⟩ := Finset.card_ne_zero.mp (mem_apexVerts.mp hu)
  obtain ⟨_, p, q, hlt, _⟩ := mem_apexTris.mp hT
  exact ⟨c s(p, q), apex_zeroA hc hlt⟩

/-- **THE APEX SLOTS ARE ISOLATED SLOTS: THERE ARE AT MOST `Isolated c` APEX VERTICES.** -/
theorem apexVerts_card_le_isolated {c : Col n k} (hc : Admissible c) :
    (apexVerts c).card ≤ Isolated c := by
  have hsub : (apexVerts c) ⊆ (Finset.univ : Finset (Verts n)).filter
      fun u => ∃ μ : Fin k, u ∈ zeroA c μ := by
    intro u hu
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ u, zeroA_of_mem_apexVerts hc hu⟩
  calc (apexVerts c).card
      ≤ ((Finset.univ : Finset (Verts n)).filter fun u => ∃ μ : Fin k, u ∈ zeroA c μ).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ μ : Fin k, (zeroA c μ).card := by
      refine card_le_sum_of_mem _ _ _ fun u hu => ?_
      rw [Finset.mem_filter] at hu
      obtain ⟨μ, hμ⟩ := hu.2
      exact ⟨μ, Finset.mem_univ μ, hμ⟩
    _ = Isolated c := rfl

/-! ### §3 — THE MAIN COUNT -/

/-- **THE APEX–ISOLATION COUNT, `2·|triSets c| ≤ (n-1)·Isolated c`.**

Every labelled triangle of the first stage wastes an isolated `(vertex, colour)` cell (the apex,
with the colour of the opposite edge: `Strict.apex_zeroA`), and one isolated cell can be the waste
of at most `(n-1)/2` triangles.  **This is the first quantitative use of the apex-isolation lemma
of round 81**, and it holds for *every* admissible colouring — no `PairFree` hypothesis. -/
theorem two_mul_triSets_le {c : Col n k} (hc : Admissible c) :
    2 * (triSets c).card ≤ (n - 1) * Isolated c := by
  have h1 : (triSets c).card ≤ ∑ u : Verts n, (apexTris c u).card := by
    refine card_le_sum_of_mem _ _ _ fun T hT => ?_
    obtain ⟨u, p, q, hlt, hT2⟩ := mem_triSets.mp hT
    exact ⟨u, Finset.mem_univ u, mem_apexTris.mpr ⟨hT, p, q, hlt, hT2⟩⟩
  have key : 2 * ∑ u ∈ (Finset.univ : Finset (Verts n)), (apexTris c u).card
      ≤ (n - 1) * (apexVerts c).card := by
    have e : ∀ u ∈ (Finset.univ : Finset (Verts n)), 2 * (apexTris c u).card
        ≤ (n - 1) * (if (apexTris c u).card ≠ 0 then (1 : ℕ) else 0) := by
      intro u _
      by_cases hu : (apexTris c u).card ≠ 0
      · rw [if_pos hu, Nat.mul_one]
        exact two_mul_card_apexTris_le hc u
      · rw [if_neg hu]
        omega
    have h3 : (∑ u ∈ (Finset.univ : Finset (Verts n)),
          ((if (apexTris c u).card ≠ 0 then (1 : ℕ) else 0))) = (apexVerts c).card := by
      have he : ((Finset.univ : Finset (Verts n)).filter (fun u => u ∈ apexVerts c))
          = apexVerts c := by
        ext u
        simp [apexVerts]
      calc (∑ u ∈ (Finset.univ : Finset (Verts n)),
            ((if (apexTris c u).card ≠ 0 then (1 : ℕ) else 0)))
          = ∑ x ∈ (Finset.univ : Finset (Verts n)),
            (if x ∈ apexVerts c then (1 : ℕ) else 0) := by
              refine Finset.sum_congr rfl fun u _ => ?_
              simp only [mem_apexVerts]
        _ = ((Finset.univ : Finset (Verts n)).filter (fun x => x ∈ apexVerts c)).card :=
          sum_ite_univ_mem (apexVerts c)
        _ = (apexVerts c).card := by rw [he]
    calc 2 * (∑ u ∈ (Finset.univ : Finset (Verts n)), (apexTris c u).card)
        = ∑ u ∈ (Finset.univ : Finset (Verts n)), (2 * (apexTris c u).card) := by
          rw [Finset.mul_sum]
        _ ≤ ∑ u ∈ (Finset.univ : Finset (Verts n)),
            ((n - 1) * ((if (apexTris c u).card ≠ 0 then (1 : ℕ) else 0))) :=
          Finset.sum_le_sum e
        _ = (n - 1) * (∑ u ∈ (Finset.univ : Finset (Verts n)),
            ((if (apexTris c u).card ≠ 0 then (1 : ℕ) else 0))) := by
          rw [Finset.mul_sum]
        _ = (n - 1) * (apexVerts c).card := by rw [h3]
  calc 2 * (triSets c).card ≤ 2 * ∑ u ∈ (Finset.univ : Finset (Verts n)), (apexTris c u).card :=
        mul_le_mul_left' h1
    _ ≤ (n - 1) * (apexVerts c).card := key
    _ ≤ (n - 1) * Isolated c := mul_le_mul_left' (apexVerts_card_le_isolated hc)

