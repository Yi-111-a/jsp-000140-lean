import JSPProblem.Partial

/-!
# JSP-000140 — round 40: the auxiliary hypergraph as **data**, and the **failure of the greedy
method** for the first stage

Everything proved up to round 39 concerns the *verification* side: given a matching in the auxiliary
hypergraph, the induced colouring is a partial labelled-triangle system (`Fam`, `Partial`), and
`jsp_000140_main` is reduced to the existence of that matching (`Partial.FamGreedyFamily`).  The
**existence** side had never been touched in the matching world: rounds 31–38 only assumed it.

This round attacks it, and gets theorems out of it: **the cheapest deterministic way of producing a
matching in `H` — a maximal one, which is what a greedy algorithm returns — is provably short of
what the catalog budget demands, by a factor of more than four.**  So the Rödl nibble /
random-triangle-removal step of arXiv:2208.12563 §4 (Thm 4.2) = arXiv:2207.02920 Phase 1 is not an
artifact of the analysis: it is *necessary*, and this file proves that.

## §1 — `auxF`: the edge set of `H`, and its census

The hypervertices of `H` are the slots `Verts n × Fin k`; its hyperedges are the five-slot sets of
the well-formed configurations.

* **`card_auxF` — THE CENSUS OF `H`: `|E(H)| = n(n-1)(n-2)·k(k-1)`.**  An ordered triple of distinct
  vertices (`card_offdiag`) and, for each, an ordered pair of distinct colours.

## §2 — the slot degrees

* **`card_ok_centre`** and the four transfer lemmas `card_ok_leafP`, `card_ok_leafQ`,
  `card_ok_leafPJ`, `card_ok_leafQJ` — the number of hyperedges prescribing two given slots (one
  vertex and one colour);
* **`card_auxDeg_le` — `|{ g ∈ H : σ ∈ slots g }| ≤ 5(n-1)(n-2)(k-1)`**: the exact degree of a
  hypervertex of `H`.  The three involutions `swapUP`, `swapPQ`, `swapIJ` of `Cfg n k` move the
  prescribed pair around, so one count suffices.

## §3 — the greedy (maximal-matching) analysis

* **`SlotMaximal`** — no hyperedge of `H` is slot-disjoint from `F`;
* **`blocked_card_le`** — the hyperedges sharing a slot with a fixed member: at most
  `25(n-1)(n-2)(k-1)`;
* **`card_auxF_le_of_maximal`** — the double count `|E(H)| ≤ 25(n-1)(n-2)(k-1)·|F|`;
* **`greedy_guarantee` — WHAT THE TRIVIAL ARGUMENT PROVES: `25|F| ≥ n·k`, i.e. `|F| ≥ nk/25`.**
  This is the whole content of the greedy/nibble-free argument.

## §4 — what the budget demands, and the gap

* **`budget_k_le`, `budget_le_D`** — from the budget `6(k+2D+1) ≤ 5(n-1)+δn` and the slot counting
  `5(n-1) ≤ 6k+5D`: `6k ≤ (5+δ)n − 11` and `7D + 6 ≤ δn`;
* **`first_stage_size` — WHAT THE BUDGET FORCES: `42|F| ≥ n((7-δ)n-1)`**, i.e. `|F| ≈ n²/6`, more
  than four times `greedy_guarantee`;
* **`leftover_frac_le`, `leftover_frac_le_of_small`** — the first stage must cover all but a
  `δ/7`-fraction of the edges; for the published `δ ≤ 1/6` that is **`≤ 1/42` of them**;
* **`greedy_gap`, `greedy_short`, `no_greedy_first_stage`** — the punchline: the greedy guarantee is
  strictly below the size every valid first stage has, and a family of size at most `nk/25` can
  never satisfy the published budget (for `δ ≤ 1/6`, `n ≥ 1`).

## §5 — what the prize hypothesis says

* **`witness_size`, `witness_leftover`** — the two theorems read off any family satisfying the
  budget: a matching of more than `n²/6` members, covering more than `41/42` of `E(K_n)`.
-/

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

namespace JSP140

attribute [local instance] Classical.propDecidable

variable {n k : ℕ}

/-! ### 0. Counting tools -/

/-- A sum over a product type is a nested sum. -/
theorem sum_univ_prod {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (f : α × β → ℕ) : ∑ g : α × β, f g = ∑ a : α, ∑ b : β, f (a, b) := by
  simp only [← Finset.univ_product_univ]
  exact Finset.sum_product' _ _ (fun a b => f (a, b))

/-- Five-fold version, for configurations. -/
theorem sum_univ_prod5 {α β γ δ ε : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    [Fintype ε] [DecidableEq α] [DecidableEq β] [DecidableEq γ] [DecidableEq δ] [DecidableEq ε]
    (f : α × β × γ × δ × ε → ℕ) :
    ∑ t : α × β × γ × δ × ε, f t
      = ∑ a : α, ∑ b : β, ∑ c : γ, ∑ d : δ, ∑ e : ε, f (a, b, c, d, e) := by
  have h2 : ∀ a : α, (∑ t : β × γ × δ × ε, f (a, t))
      = ∑ b : β, ∑ t : γ × δ × ε, f (a, b, t) := by
    intro a; exact sum_univ_prod (fun t => f (a, t))
  have h3 : ∀ a : α, ∀ b : β, (∑ t : γ × δ × ε, f (a, b, t))
      = ∑ c : γ, ∑ t : δ × ε, f (a, b, c, t) := by
    intro a b; exact sum_univ_prod (fun t => f (a, b, t))
  have h4 : ∀ a : α, ∀ b : β, ∀ c : γ, (∑ t : δ × ε, f (a, b, c, t))
      = ∑ d : δ, ∑ e : ε, f (a, b, c, d, e) := by
    intro a b c; exact sum_univ_prod (fun t => f (a, b, c, t))
  have h1 : ∑ t : α × β × γ × δ × ε, f t
      = ∑ a : α, ∑ t : β × γ × δ × ε, f (a, t) := by
    exact sum_univ_prod (fun t => f t)
  rw [h1]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [h2 a]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [h3 a b]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  exact h4 a b c

/-- The diagonal of `A ×ˢ A` has `|A|` elements. -/
theorem card_diag_of [DecidableEq α] (A : Finset α) :
    ((A ×ˢ A).filter (fun t : α × α => t.1 = t.2)).card = A.card := by
  refine (Finset.card_bij (s := A) (t := (A ×ˢ A).filter (fun t : α × α => t.1 = t.2))
    (fun a _ => (a, a)) ?_ ?_ ?_).symm
  · intro a ha; simp [ha]
  · intro a₁ _ a₂ _ h; exact Prod.ext_iff.mp h |>.1
  · intro b hb
    simp only [Finset.mem_filter, Finset.mem_product] at hb
    rcases hb with ⟨⟨h1, h2⟩, heq⟩
    exact ⟨b.1, h1, Prod.ext_iff.mpr ⟨rfl, heq⟩⟩

/-- **The number of ordered pairs of *distinct* elements of a finset.** -/
theorem card_offdiag_of [DecidableEq α] (A : Finset α) :
    ((A ×ˢ A).filter (fun t : α × α => ¬(t.1 = t.2))).card = A.card * (A.card - 1) := by
  have hfilter : (A ×ˢ A).filter (fun t : α × α => ¬(t.1 = t.2))
      = (A ×ˢ A) \ (A ×ˢ A).filter (fun t : α × α => t.1 = t.2) := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_product]
    tauto
  rw [hfilter, Finset.card_sdiff_of_subset (s := (A ×ˢ A).filter (fun t : α × α => t.1 = t.2))
      (by intro x hx; simp only [Finset.mem_filter, Finset.mem_product] at hx;
            exact Finset.mem_product.mpr hx.1)]
  rw [Finset.card_product, card_diag_of]
  simp [Nat.mul_sub_left_distrib]

/-- `∑ j : Fin k, (if i ≠ j then 1 else 0) = k - 1`. -/
theorem sum_ite_ne {k : ℕ} (i : Fin k) : (∑ j : Fin k, (if i ≠ j then 1 else 0 : ℕ)) = k - 1 := by
  have h3 : (∑ j : Fin k, (if i ≠ j then 1 else 0 : ℕ))
      = ∑ j ∈ (Finset.univ : Finset (Fin k)).filter (fun j => i ≠ j), (1 : ℕ) := by
    rw [Finset.sum_filter]
  rw [h3, Finset.sum_const]
  have h4 : (Finset.univ : Finset (Fin k)).filter (fun j => i ≠ j)
      = (Finset.univ : Finset (Fin k)).erase i := by
    ext j'; simp only [Finset.mem_filter, Finset.mem_erase]; tauto
  rw [h4, Finset.card_erase_of_mem (Finset.mem_univ i)]
  simp

/-- `∑ i : Fin k, b = k · b`. -/
theorem sum_const_fin (k b : ℕ) : (∑ _i : Fin k, b) = k * b := by
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  rfl

/-- An indicator sum is a cardinality times the value. -/
theorem sum_ite_mem_mul {α : Type*} [Fintype α] [DecidableEq α] (P : α → Prop) [DecidablePred P]
    (c : ℕ) : (∑ x : α, (if P x then c else 0 : ℕ)) = c * (Finset.univ.filter P).card := by
  have h1 : ∑ x ∈ (Finset.univ : Finset α).filter P, c = ∑ x : α, (if P x then c else 0) := by
    rw [Finset.sum_filter]
  rw [← h1, Finset.sum_const]
  simp [Nat.mul_comm]

/-- Removing one element from a finset, by a filter. -/
theorem card_filter_ne [DecidableEq α] {A : Finset α} {a : α} (ha : a ∈ A) :
    (A.filter (fun x => x ≠ a)).card = A.card - 1 := by
  have h1 : A.filter (fun x => x ≠ a) = A.erase a := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_erase]
    tauto
  rw [h1]
  exact Finset.card_erase_of_mem ha

/-- Two `ite`s with logically equal conditions are equal, whatever the `Decidable` instances. -/
theorem ite_eq_of_iff {C D : Prop} [Decidable C] [Decidable D] {x y : ℕ} (h : C ↔ D) :
    (if C then x else y) = (if D then x else y) := by
  by_cases hC : C
  · rw [if_pos hC, if_pos (h.mp hC)]
  · rw [if_neg hC, if_neg (fun hD => hC (h.mpr hD))]

/-- **The count of ordered pairs of distinct colours is `k(k-1)`, and it can be pulled out of an
outer condition.** -/
theorem sum_ite_and {k : ℕ} (C : Prop) [hC : Decidable C] :
    (∑ i : Fin k, ∑ j : Fin k, (if C ∧ (i ≠ j) then 1 else 0 : ℕ))
      = if C then k * (k - 1) else 0 := by
  by_cases hC' : C
  · rw [if_pos hC']
    simp only [hC', true_and]
    have e2 : (∑ i : Fin k, ∑ j : Fin k, (if i ≠ j then 1 else 0 : ℕ)) = ∑ i : Fin k, (k - 1) := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      exact sum_ite_ne i
    rw [e2, sum_const_fin]
  · rw [if_neg hC']
    refine Finset.sum_eq_zero (fun i _ => ?_)
    refine Finset.sum_eq_zero (fun j _ => ?_)
    simp [hC']

/-! ### 1. The auxiliary hypergraph `H` as data -/

/-- **THE EDGE SET OF THE AUXILIARY HYPERGRAPH.**  `H` of arXiv:2208.12563 §4 has hypervertices the
`(vertex, colour)` slots and hyperedges the five-slot sets of the well-formed configurations. -/
noncomputable def auxF (n k : ℕ) : Finset (Cfg n k) := (Finset.univ : Finset (Cfg n k)).filter Ok

@[simp] theorem mem_auxF {n k : ℕ} {g : Cfg n k} : g ∈ auxF n k ↔ Ok g := by
  simp [auxF]

theorem OkF_iff {n k : ℕ} {F : Fam n k} : OkF F ↔ F ⊆ auxF n k := by
  constructor
  · intro h g hg; exact mem_auxF.mpr (h g hg)
  · intro h g hg; exact mem_auxF.mp (h hg)

/-- **The number of ordered pairs of distinct vertices avoiding a given one: `(n-1)(n-2)`.** -/
theorem card_offdiag (n : ℕ) (u : Verts n) :
    (∑ t : Verts n × Verts n,
      (if ¬(u = t.1) ∧ ¬(u = t.2) ∧ ¬(t.1 = t.2) then 1 else 0 : ℕ)) = (n - 1) * (n - 2) := by
  have hset : ((Finset.univ : Finset (Verts n × Verts n)).filter
        (fun t => ¬(u = t.1) ∧ ¬(u = t.2) ∧ ¬(t.1 = t.2)))
      = (((Finset.univ : Finset (Verts n)).erase u)
          ×ˢ ((Finset.univ : Finset (Verts n)).erase u)
          |>.filter (fun t : Verts n × Verts n => ¬(t.1 = t.2))) := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_erase, Finset.mem_univ, true_and]
    tauto
  have hsum : (∑ t : Verts n × Verts n,
        (if ¬(u = t.1) ∧ ¬(u = t.2) ∧ ¬(t.1 = t.2) then 1 else 0 : ℕ))
      = ((Finset.univ : Finset (Verts n × Verts n)).filter
          (fun t => ¬(u = t.1) ∧ ¬(u = t.2) ∧ ¬(t.1 = t.2))).card := by
    have h1 : ∑ t ∈ (Finset.univ : Finset (Verts n × Verts n)).filter
          (fun t => ¬(u = t.1) ∧ ¬(u = t.2) ∧ ¬(t.1 = t.2)), (1 : ℕ)
        = ∑ t : Verts n × Verts n,
            (if ¬(u = t.1) ∧ ¬(u = t.2) ∧ ¬(t.1 = t.2) then 1 else 0) := by
      rw [Finset.sum_filter]
    rw [Finset.card_eq_sum_ones]
    exact h1.symm
  have hA : ((Finset.univ : Finset (Verts n)).erase u).card = n - 1 :=
    Finset.card_erase_of_mem (Finset.mem_univ u) |>.trans (by simp)
  rw [hsum, hset, card_offdiag_of, hA]
  congr 1

/-- **THE CENSUS OF `H`: `|E(H)| = n(n-1)(n-2)·k(k-1)`.**  Three pairwise distinct vertices, and two
distinct colours.  No colouring, no four-vertex clique, no probability. -/
theorem card_auxF (n k : ℕ) :
    (auxF n k).card = n * ((n - 1) * ((n - 2) * (k * (k - 1)))) := by
  have hOk : ∀ (u p q : Verts n) (i j : Fin k),
      ((if Ok (u, p, q, i, j) then 1 else 0) : ℕ)
        = (if u ≠ p ∧ u ≠ q ∧ p ≠ q ∧ i ≠ j then 1 else 0) := by
    intro u p q i j
    simp only [Ok, cfgU, cfgP, cfgQ, cfgI, cfgJ]
    congr 1
  have h0 : (auxF n k).card = ∑ g : Cfg n k, ((if Ok g then 1 else 0) : ℕ) := by
    rw [auxF, Finset.card_filter]
  have h1 : (∑ g : Cfg n k, ((if Ok g then 1 else 0) : ℕ))
      = ∑ u : Verts n, ∑ p : Verts n, ∑ q : Verts n, ∑ i : Fin k, ∑ j : Fin k,
        (if u ≠ p ∧ u ≠ q ∧ p ≠ q ∧ i ≠ j then 1 else 0) := by
    rw [sum_univ_prod5]
    simp_rw [hOk]
  have h2 : ∀ (u p q : Verts n),
      (∑ i : Fin k, ∑ j : Fin k, (if u ≠ p ∧ u ≠ q ∧ p ≠ q ∧ i ≠ j then 1 else 0))
        = if u ≠ p ∧ u ≠ q ∧ p ≠ q then k * (k - 1) else 0 := by
    intro u p q
    by_cases hC : u ≠ p ∧ u ≠ q ∧ p ≠ q
    · rw [if_pos hC]
      have e : (∑ i : Fin k, ∑ j : Fin k, (if u ≠ p ∧ u ≠ q ∧ p ≠ q ∧ i ≠ j then 1 else 0))
          = ∑ i : Fin k, ∑ j : Fin k, (if i ≠ j then 1 else 0) := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        refine Finset.sum_congr rfl (fun j _ => ?_)
        exact ite_eq_of_iff ⟨fun h => h.2.2.2, fun h => ⟨hC.1, hC.2.1, hC.2.2, h⟩⟩
      rw [e]
      have e2 : (∑ i : Fin k, ∑ j : Fin k, (if i ≠ j then 1 else 0 : ℕ))
          = ∑ i : Fin k, (k - 1) := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        exact sum_ite_ne i
      rw [e2, sum_const_fin]
    · rw [if_neg hC]
      refine Finset.sum_eq_zero (fun i _ => ?_)
      refine Finset.sum_eq_zero (fun j _ => ?_)
      rw [if_neg (fun h => hC ⟨h.1, h.2.1, h.2.2.1⟩)]
  have h3 : ∀ (u p : Verts n),
      (∑ q : Verts n, (if u ≠ p ∧ u ≠ q ∧ p ≠ q then k * (k - 1) else 0))
        = if u ≠ p then (n - 2) * (k * (k - 1)) else 0 := by
    intro u p
    by_cases hu : u ≠ p
    · rw [if_pos hu]
      have e : (∑ q : Verts n, (if u ≠ p ∧ u ≠ q ∧ p ≠ q then k * (k - 1) else 0))
          = ∑ q : Verts n, (if q ≠ u ∧ q ≠ p then k * (k - 1) else 0) := by
        refine Finset.sum_congr rfl (fun q _ => ?_)
        exact ite_eq_of_iff ⟨fun h => ⟨Ne.symm h.2.1, Ne.symm h.2.2⟩,
          fun h => ⟨hu, Ne.symm h.1, Ne.symm h.2⟩⟩
      rw [e]
      have e2 : (∑ q : Verts n, (if q ≠ u ∧ q ≠ p then k * (k - 1) else 0))
          = (k * (k - 1)) * ((Finset.univ : Finset (Verts n)).filter
              (fun q => q ≠ u ∧ q ≠ p)).card :=
        sum_ite_mem_mul (P := fun q => q ≠ u ∧ q ≠ p) (k * (k - 1))
      have ha : (Finset.univ : Finset (Verts n)).filter (fun q => q ≠ u ∧ q ≠ p)
          = ((Finset.univ : Finset (Verts n)).filter (fun q => q ≠ u)
              |>.filter (fun q => q ≠ p)) := by
        ext q
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have hb : ((Finset.univ : Finset (Verts n)).filter (fun q => q ≠ u)
          |>.filter (fun q => q ≠ p)).card = n - 2 := by
        rw [card_filter_ne (A := (Finset.univ : Finset (Verts n)).filter (fun q => q ≠ u))
              (a := p) (by simp [Ne.symm hu]),
            card_filter_ne (A := (Finset.univ : Finset (Verts n))) (a := u) (Finset.mem_univ u),
            Finset.card_univ, Fintype.card_fin]
        omega
      rw [e2, ha, hb]
      ring
    · rw [if_neg hu]
      refine Finset.sum_eq_zero (fun q _ => ?_)
      rw [if_neg (fun h => hu h.1)]
  have h4 : ∀ (u : Verts n),
      (∑ p : Verts n, (if u ≠ p then (n - 2) * (k * (k - 1)) else 0))
        = ∑ p : Verts n, (if p ≠ u then (n - 2) * (k * (k - 1)) else 0) := by
    intro u
    refine Finset.sum_congr rfl (fun p _ => ?_)
    exact ite_eq_of_iff ⟨fun h => Ne.symm h, fun h => Ne.symm h⟩
  have h5 : ∀ (u : Verts n),
      (∑ p : Verts n, (if p ≠ u then (n - 2) * (k * (k - 1)) else 0))
        = (n - 2) * (k * (k - 1))
          * ((Finset.univ : Finset (Verts n)).filter (fun q => q ≠ u)).card := by
    intro u
    exact sum_ite_mem_mul (P := fun p => p ≠ u) ((n - 2) * (k * (k - 1)))
  have h6 : ∀ (u : Verts n),
      ((Finset.univ : Finset (Verts n)).filter (fun q => q ≠ u)).card = n - 1 := by
    intro u
    exact (card_filter_ne (A := (Finset.univ : Finset (Verts n))) (a := u) (Finset.mem_univ u))
      |>.trans (by simp)
  rw [h0, h1]
  simp_rw [h2]
  simp_rw [h3]
  simp_rw [h4]
  simp_rw [h5]
  simp_rw [h6]
  have hb : (n - 2) * (k * (k - 1)) * (n - 1) = (n - 1) * ((n - 2) * (k * (k - 1))) := by ring
  rw [Finset.sum_congr rfl (fun _ _ => hb), Finset.sum_const]
  simp [nsmul_eq_mul, Finset.card_univ, Fintype.card_fin]

/-! ### 2. The degree of a slot -/

/-- **THE THREE COORDINATE SWAPS OF A CONFIGURATION.**  `Cfg n k` is the set of five-tuples, and
these involutions move a prescribed pair of coordinates to another one while preserving `Ok`; so the
number of hyperedges prescribing two given slots does not depend on which pair is prescribed. -/
def swapUP {n k : ℕ} (g : Cfg n k) : Cfg n k :=
  (g.2.1, g.1, g.2.2.1, g.2.2.2.1, g.2.2.2.2)

def swapPQ {n k : ℕ} (g : Cfg n k) : Cfg n k :=
  (g.1, g.2.2.1, g.2.1, g.2.2.2.1, g.2.2.2.2)

def swapIJ {n k : ℕ} (g : Cfg n k) : Cfg n k :=
  (g.1, g.2.1, g.2.2.1, g.2.2.2.2, g.2.2.2.1)

def equivSwapUP {n k : ℕ} : Cfg n k ≃ Cfg n k where
  toFun := swapUP
  invFun := swapUP
  left_inv g := by rcases g with ⟨u, p, q, i, j⟩; rfl
  right_inv g := by rcases g with ⟨u, p, q, i, j⟩; rfl

def equivSwapPQ {n k : ℕ} : Cfg n k ≃ Cfg n k where
  toFun := swapPQ
  invFun := swapPQ
  left_inv g := by rcases g with ⟨u, p, q, i, j⟩; rfl
  right_inv g := by rcases g with ⟨u, p, q, i, j⟩; rfl

def equivSwapIJ {n k : ℕ} : Cfg n k ≃ Cfg n k where
  toFun := swapIJ
  invFun := swapIJ
  left_inv g := by rcases g with ⟨u, p, q, i, j⟩; rfl
  right_inv g := by rcases g with ⟨u, p, q, i, j⟩; rfl

/-- **THE HYPEREDGES THROUGH A GIVEN SLOT.** -/
noncomputable def auxDeg (n k : ℕ) (vp : Verts n × Fin k) : Finset (Cfg n k) :=
  (auxF n k).filter (fun g => vp ∈ cfgSlots g)

theorem mem_auxDeg {n k : ℕ} {vp : Verts n × Fin k} {g : Cfg n k} :
    g ∈ auxDeg n k vp ↔ Ok g ∧ vp ∈ cfgSlots g := by
  simp [auxDeg, mem_auxF]

private theorem card_auxF_filter (n k : ℕ) (P : Cfg n k → Prop) [DecidablePred P] :
    ((auxF n k).filter P).card
      = ∑ g : Cfg n k, ((if Ok g ∧ P g then 1 else 0) : ℕ) := by
  rw [auxF, Finset.card_filter, Finset.sum_filter]
  refine Finset.sum_congr rfl (fun g _ => ?_)
  by_cases h1 : Ok g <;> by_cases h2 : P g <;> simp [h1, h2]

/-- **THE HYPEREDGES PRESCRIBING THE CENTRE SLOT.**  Their number is `(n-1)(n-2)(k-1)`: the other two
vertices are distinct from `x` and from each other, and the other colour differs from `c`. -/
theorem card_ok_centre (n k : ℕ) (x : Verts n) (c : Fin k) :
    ((auxF n k).filter (fun g => cfgU g = x ∧ cfgI g = c)).card
      = (n - 1) * ((n - 2) * (k - 1)) := by
  set W : Finset (Verts n) := (Finset.univ : Finset (Verts n)).erase x with hW
  set W' : Finset (Verts n) := (Finset.univ : Finset (Verts n)).erase x with hW'
  set C' : Finset (Fin k) := (Finset.univ : Finset (Fin k)).erase c with hC'
  set PQ : Finset (Verts n × Verts n) :=
    ((W : Finset (Verts n)) ×ˢ (W' : Finset (Verts n)))
      |>.filter (fun t : Verts n × Verts n => ¬(t.1 = t.2)) with hPQ
  set T : Finset ((Verts n × Verts n) × Fin k) := (PQ : Finset (Verts n × Verts n)) ×ˢ C' with hT
  have hcardPQ : PQ.card = (n - 1) * (n - 2) := by
    rw [hPQ, hW, card_offdiag_of, hW', Finset.card_erase_of_mem (Finset.mem_univ x),
      Finset.card_univ, Fintype.card_fin]
    have hnn : (n - 1) - 1 = n - 2 := by omega
    rw [hnn]
  have hcardW : W.card = n - 1 := by
    rw [hW, hW']
    exact (Finset.card_erase_of_mem (Finset.mem_univ x)).trans (by simp)
  have hcardC : C'.card = k - 1 := by
    rw [hC']
    exact (Finset.card_erase_of_mem (Finset.mem_univ c)).trans (by simp)
  have hcardT : T.card = (n - 1) * ((n - 2) * (k - 1)) := by
    rw [hT, Finset.card_product, hcardPQ, hcardC]
    ring
  refine (Finset.card_bij (s := T) (t := (auxF n k).filter (fun g => cfgU g = x ∧ cfgI g = c))
    (fun t _ => (x, t.1.1, t.1.2, c, t.2)) ?_ ?_ ?_).symm.trans hcardT
  · intro t ht
    rw [hT, hPQ, hW, hW', hC'] at ht
    have h12 := Finset.mem_product.mp ht
    have hf := Finset.mem_filter.mp h12.1
    have h1 := Finset.mem_product.mp hf.1
    have h2 := hf.2
    have h3 := Finset.mem_erase.mp h1.1
    have h4 := Finset.mem_erase.mp h1.2
    have h5 := Finset.mem_erase.mp h12.2
    simp only [mem_auxF, Finset.mem_filter]
    exact ⟨⟨Ne.symm h3.1, Ne.symm h4.1, h2, Ne.symm h5.1⟩, rfl, rfl⟩
  · intro t₁ _ t₂ _ he
    have hp := congrArg (fun w : Cfg n k => (w.2.1 : Verts n)) he
    have hq := congrArg (fun w : Cfg n k => (w.2.2.1 : Verts n)) he
    have hj := congrArg (fun w : Cfg n k => ((w.2.2.2).2 : Fin k)) he
    apply Prod.ext
    · exact Prod.ext hp hq
    · exact hj
  · intro g hg
    rcases g with ⟨u, p, q, i, j⟩
    simp only [mem_auxF, Finset.mem_filter] at hg
    rcases hg with ⟨hOk, hu, hi⟩
    have hu' : x = u := by simpa [cfgU] using hu.symm
    have hi' : c = i := by simpa [cfgI] using hi.symm
    subst hu'
    subst hi'
    have hd := Ok_def hOk
    have hd1 : p ≠ x := by simpa [cfgU, cfgP] using Ne.symm hd.1
    have hd2 : q ≠ x := by simpa [cfgU, cfgQ] using Ne.symm hd.2.1
    have hd3 : p ≠ q := by simpa [cfgP, cfgQ] using hd.2.2.1
    have hd4 : j ≠ c := by simpa [cfgI, cfgJ] using Ne.symm hd.2.2.2
    refine ⟨((p, q), j), ?_, rfl⟩
    rw [hT, hPQ, hW, hW', hC']
    exact Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨Finset.mem_erase.mpr ⟨hd1, Finset.mem_univ p⟩,
        Finset.mem_erase.mpr ⟨hd2, Finset.mem_univ q⟩⟩, hd3⟩,
      Finset.mem_erase.mpr ⟨hd4, Finset.mem_univ j⟩⟩

/-- The centre slot and the first leaf slot are interchangeable in the count: `swapUP` sends the
second coordinate to the first and preserves `Ok`. -/
theorem card_ok_leafP (n k : ℕ) (x : Verts n) (c : Fin k) :
    ((auxF n k).filter (fun g => cfgP g = x ∧ cfgI g = c)).card
      = ((auxF n k).filter (fun g => cfgU g = x ∧ cfgI g = c)).card := by
  have h0 := Equiv.sum_comp (equivSwapUP (n := n) (k := k))
    (fun g : Cfg n k => (if Ok g ∧ cfgP g = x ∧ cfgI g = c then 1 else 0 : ℕ))
  have h : (∑ g : Cfg n k, ((if Ok g ∧ cfgP g = x ∧ cfgI g = c then 1 else 0) : ℕ))
      = ∑ g : Cfg n k, ((if Ok g ∧ cfgU g = x ∧ cfgI g = c then 1 else 0) : ℕ) := by
    rw [← h0]
    refine Finset.sum_congr rfl (fun g _ => ?_)
    rcases g with ⟨u, p, q, i, j⟩
    simp [equivSwapUP, swapUP, Ok, cfgU, cfgP, cfgQ, cfgI, cfgJ, ne_comm, and_comm,
      and_left_comm, and_assoc]
  rw [card_auxF_filter, card_auxF_filter, h]

/-- The two leaf slots are interchangeable in the count: `swapPQ` exchanges them. -/
theorem card_ok_leafQ (n k : ℕ) (x : Verts n) (c : Fin k) :
    ((auxF n k).filter (fun g => cfgQ g = x ∧ cfgI g = c)).card
      = ((auxF n k).filter (fun g => cfgP g = x ∧ cfgI g = c)).card := by
  have h0 := Equiv.sum_comp (equivSwapPQ (n := n) (k := k))
    (fun g : Cfg n k => (if Ok g ∧ cfgP g = x ∧ cfgI g = c then 1 else 0 : ℕ))
  have h : (∑ g : Cfg n k, ((if Ok g ∧ cfgQ g = x ∧ cfgI g = c then 1 else 0) : ℕ))
      = ∑ g : Cfg n k, ((if Ok g ∧ cfgP g = x ∧ cfgI g = c then 1 else 0) : ℕ) := by
    rw [← h0]
    refine Finset.sum_congr rfl (fun g _ => ?_)
    rcases g with ⟨u, p, q, i, j⟩
    simp [equivSwapPQ, swapPQ, Ok, cfgU, cfgP, cfgQ, cfgI, cfgJ, ne_comm, and_comm,
      and_left_comm, and_assoc]
  rw [card_auxF_filter, card_auxF_filter, h]

/-- The two colours are interchangeable in the count: `swapIJ` exchanges them. -/
theorem card_ok_leafPJ (n k : ℕ) (x : Verts n) (c : Fin k) :
    ((auxF n k).filter (fun g => cfgP g = x ∧ cfgJ g = c)).card
      = ((auxF n k).filter (fun g => cfgP g = x ∧ cfgI g = c)).card := by
  have h0 := Equiv.sum_comp (equivSwapIJ (n := n) (k := k))
    (fun g : Cfg n k => (if Ok g ∧ cfgP g = x ∧ cfgI g = c then 1 else 0 : ℕ))
  have h : (∑ g : Cfg n k, ((if Ok g ∧ cfgP g = x ∧ cfgJ g = c then 1 else 0) : ℕ))
      = ∑ g : Cfg n k, ((if Ok g ∧ cfgP g = x ∧ cfgI g = c then 1 else 0) : ℕ) := by
    rw [← h0]
    refine Finset.sum_congr rfl (fun g _ => ?_)
    rcases g with ⟨u, p, q, i, j⟩
    simp [equivSwapIJ, swapIJ, Ok, cfgU, cfgP, cfgQ, cfgI, cfgJ, ne_comm, and_comm,
      and_left_comm, and_assoc]
  rw [card_auxF_filter, card_auxF_filter, h]

theorem card_ok_leafQJ (n k : ℕ) (x : Verts n) (c : Fin k) :
    ((auxF n k).filter (fun g => cfgQ g = x ∧ cfgJ g = c)).card
      = ((auxF n k).filter (fun g => cfgQ g = x ∧ cfgI g = c)).card := by
  have h0 := Equiv.sum_comp (equivSwapIJ (n := n) (k := k))
    (fun g : Cfg n k => (if Ok g ∧ cfgQ g = x ∧ cfgI g = c then 1 else 0 : ℕ))
  have h : (∑ g : Cfg n k, ((if Ok g ∧ cfgQ g = x ∧ cfgJ g = c then 1 else 0) : ℕ))
      = ∑ g : Cfg n k, ((if Ok g ∧ cfgQ g = x ∧ cfgI g = c then 1 else 0) : ℕ) := by
    rw [← h0]
    refine Finset.sum_congr rfl (fun g _ => ?_)
    rcases g with ⟨u, p, q, i, j⟩
    simp [equivSwapIJ, swapIJ, Ok, cfgU, cfgP, cfgQ, cfgI, cfgJ, ne_comm, and_comm,
      and_left_comm, and_assoc]
  rw [card_auxF_filter, card_auxF_filter, h]

/-- **THE DEGREE OF A HYPERVERTEX OF `H`: `5(n-1)(n-2)(k-1)`.**  The five slots of a configuration are
used at three vertices, one at the centre and two at each leaf, so a slot is prescribed by one vertex
and one colour, and the five possibilities are counted by the transfer lemmas above. -/
theorem card_auxDeg_le (vp : Verts n × Fin k) :
    (auxDeg n k vp).card ≤ 5 * ((n - 1) * ((n - 2) * (k - 1))) := by
  rcases vp with ⟨x, c⟩
  set S₁ : Finset (Cfg n k) := (auxF n k).filter (fun g => cfgU g = x ∧ cfgI g = c) with hS₁
  set S₂ : Finset (Cfg n k) := (auxF n k).filter (fun g => cfgP g = x ∧ cfgI g = c) with hS₂
  set S₃ : Finset (Cfg n k) := (auxF n k).filter (fun g => cfgQ g = x ∧ cfgI g = c) with hS₃
  set S₄ : Finset (Cfg n k) := (auxF n k).filter (fun g => cfgP g = x ∧ cfgJ g = c) with hS₄
  set S₅ : Finset (Cfg n k) := (auxF n k).filter (fun g => cfgQ g = x ∧ cfgJ g = c) with hS₅
  have hsub : auxDeg n k (x, c) ⊆ S₁ ∪ (S₂ ∪ (S₃ ∪ (S₄ ∪ S₅))) := by
    intro g hg
    have hg' := mem_auxDeg.mp hg
    have hok : g ∈ auxF n k := mem_auxF.mpr hg'.1
    have hs : (c = cfgI g ∧ (x = cfgU g ∨ x = cfgP g ∨ x = cfgQ g))
        ∨ (c = cfgJ g ∧ (x = cfgP g ∨ x = cfgQ g)) := (mem_cfgSlots (g := g)).mp hg'.2
    rcases hs with ⟨hi, hu⟩ | ⟨hj, hu⟩
    · rcases hu with hu | hu | hu
      · refine Finset.mem_union.mpr (Or.inl ?_)
        show g ∈ S₁
        exact Finset.mem_filter.mpr ⟨hok, ⟨hu.symm, hi.symm⟩⟩
      · refine Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inl ?_)))
        show g ∈ S₂
        exact Finset.mem_filter.mpr ⟨hok, ⟨hu.symm, hi.symm⟩⟩
      · refine Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr
          (Or.inr (Finset.mem_union.mpr (Or.inl ?_)))))
        show g ∈ S₃
        exact Finset.mem_filter.mpr ⟨hok, ⟨hu.symm, hi.symm⟩⟩
    · rcases hu with hu | hu
      · refine Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inr
          (Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inl ?_)))))))
        show g ∈ S₄
        exact Finset.mem_filter.mpr ⟨hok, ⟨hu.symm, hj.symm⟩⟩
      · refine Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inr
          (Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inr ?_)))))))
        show g ∈ S₅
        exact Finset.mem_filter.mpr ⟨hok, ⟨hu.symm, hj.symm⟩⟩
  have hcard1 : S₁.card = (n - 1) * ((n - 2) * (k - 1)) := by
    rw [hS₁]; exact card_ok_centre n k x c
  have hcard2 : S₂.card = S₁.card := by rw [hS₂, hS₁]; exact card_ok_leafP n k x c
  have hcard3 : S₃.card = S₁.card := by
    rw [hS₃, hS₁]; exact (card_ok_leafQ n k x c).trans (card_ok_leafP n k x c)
  have hcard4 : S₄.card = S₁.card := by
    rw [hS₄, hS₁]; exact (card_ok_leafPJ n k x c).trans (card_ok_leafP n k x c)
  have hcard5 : S₅.card = S₁.card := by
    rw [hS₅, hS₁]
    exact ((card_ok_leafQJ n k x c).trans (card_ok_leafQ n k x c)).trans (card_ok_leafP n k x c)
  have hcardU : (S₁ ∪ (S₂ ∪ (S₃ ∪ (S₄ ∪ S₅)))).card
      ≤ 5 * ((n - 1) * ((n - 2) * (k - 1))) := by
    calc (S₁ ∪ (S₂ ∪ (S₃ ∪ (S₄ ∪ S₅)))).card
        ≤ S₁.card + (S₂ ∪ (S₃ ∪ (S₄ ∪ S₅))).card := Finset.card_union_le _ _
      _ ≤ S₁.card + (S₂.card + (S₃ ∪ (S₄ ∪ S₅)).card) :=
          Nat.add_le_add_left (Finset.card_union_le _ _) _
      _ ≤ S₁.card + (S₂.card + (S₃.card + (S₄ ∪ S₅).card)) :=
          Nat.add_le_add_left (Nat.add_le_add_left (Finset.card_union_le _ _) _) _
      _ ≤ S₁.card + (S₂.card + (S₃.card + (S₄.card + S₅.card))) :=
          Nat.add_le_add_left (Nat.add_le_add_left (Nat.add_le_add_left
            (Finset.card_union_le _ _) _) _) _
      _ = 5 * ((n - 1) * ((n - 2) * (k - 1))) := by
        simp only [hcard1, hcard2, hcard3, hcard4, hcard5]
        ring
  calc (auxDeg n k (x, c)).card ≤ (S₁ ∪ (S₂ ∪ (S₃ ∪ (S₄ ∪ S₅)))).card :=
        Finset.card_le_card hsub
    _ ≤ 5 * ((n - 1) * ((n - 2) * (k - 1))) := hcardU

/-! ### 3. The greedy (maximal-matching) analysis -/

/-- **A FAMILY IS MAXIMAL** if no hyperedge of `H` outside it is slot-disjoint from it: this is
exactly the output of a greedy hypergraph-matching algorithm (add a hyperedge whenever all five of
its hypervertices are unused). -/
def SlotMaximal {n k : ℕ} (F : Fam n k) : Prop :=
  ∀ g : Cfg n k, g ∈ auxF n k → g ∉ F →
    ∃ g' : Cfg n k, g' ∈ F ∧ ∃ vp : Verts n × Fin k, vp ∈ cfgSlots g ∧ vp ∈ cfgSlots g'

/-- **THE HYPEREDGES BLOCKED BY A FIXED MEMBER OF A FAMILY:** those sharing a slot with it. -/
noncomputable def blockedF {n k : ℕ} (F : Fam n k) (g' : Cfg n k) : Finset (Cfg n k) :=
  (cfgSlots g').biUnion fun vp => auxDeg n k vp

theorem mem_blockedF {n k : ℕ} {F : Fam n k} {g' : Cfg n k} {g : Cfg n k} (hg : g ∈ auxF n k)
    (hb : ∃ vp : Verts n × Fin k, vp ∈ cfgSlots g ∧ vp ∈ cfgSlots g') : g ∈ blockedF F g' := by
  obtain ⟨vp, h1, h2⟩ := hb
  exact Finset.mem_biUnion.mpr ⟨vp, h2, (mem_auxDeg).mpr ⟨mem_auxF.mp hg, h1⟩⟩

/-- **AT MOST `25(n-1)(n-2)(k-1)` HYPEREDGES SHARE A SLOT WITH A GIVEN ONE:** its five slots, and
through each of them at most `5(n-1)(n-2)(k-1)` hyperedges (`card_auxDeg_le`). -/
theorem blocked_card_le {n k : ℕ} {F : Fam n k} {g' : Cfg n k} (hg' : Ok g') :
    (blockedF F g').card ≤ 25 * ((n - 1) * ((n - 2) * (k - 1))) := by
  have h1 : (blockedF F g').card ≤ ∑ vp ∈ (cfgSlots g'), (auxDeg n k vp).card := by
    rw [blockedF]
    exact Finset.card_biUnion_le
  have h2 : ∑ vp ∈ (cfgSlots g'), (auxDeg n k vp).card
      ≤ ∑ vp ∈ (cfgSlots g'), 5 * ((n - 1) * ((n - 2) * (k - 1))) :=
    Finset.sum_le_sum fun vp _ => card_auxDeg_le vp
  have h3 : (∑ vp ∈ (cfgSlots g'), 5 * ((n - 1) * ((n - 2) * (k - 1))))
      = (cfgSlots g').card * (5 * ((n - 1) * ((n - 2) * (k - 1)))) := by
    have hx := Finset.sum_const (s := cfgSlots g') (5 * ((n - 1) * ((n - 2) * (k - 1))))
    simpa [nsmul_eq_mul] using hx
  have h4 : (cfgSlots g').card * (5 * ((n - 1) * ((n - 2) * (k - 1))))
      ≤ 25 * ((n - 1) * ((n - 2) * (k - 1))) := by
    have hx := card_cfgSlots (g := g') hg'
    rw [hx]
    nlinarith
  calc (blockedF F g').card ≤ ∑ vp ∈ (cfgSlots g'), (auxDeg n k vp).card := h1
    _ ≤ ∑ vp ∈ (cfgSlots g'), 5 * ((n - 1) * ((n - 2) * (k - 1))) := h2
    _ = (cfgSlots g').card * (5 * ((n - 1) * ((n - 2) * (k - 1)))) := h3
    _ ≤ 25 * ((n - 1) * ((n - 2) * (k - 1))) := h4

/-- **THE DOUBLE COUNT: EVERY HYPEREDGE OF `H` IS BLOCKED BY ONE OF THE SLOTS OF `F`.**  This is
the whole of the trivial (nibble-free) argument. -/
theorem card_auxF_le_of_maximal {n k : ℕ} {F : Fam n k} (hmax : SlotMaximal F) (hok : OkF F)
    (hS : SlotFree F) :
    (auxF n k).card ≤ (SlotsF F).card * (5 * ((n - 1) * ((n - 2) * (k - 1)))) := by
  have h1 : (auxF n k).card ≤ ((SlotsF F).biUnion fun vp => auxDeg n k vp).card := by
    refine Finset.card_le_card fun g hg => ?_
    by_cases hgF : g ∈ F
    · refine Finset.mem_biUnion.mpr ⟨(cfgU g, cfgI g), ?_, ?_⟩
      · refine Finset.mem_biUnion.mpr ⟨g, hgF, (mem_cfgSlots (g := g)).mpr
          (Or.inl ⟨rfl, Or.inl rfl⟩)⟩
      · exact (mem_auxDeg).mpr ⟨mem_auxF.mp hg, (mem_cfgSlots (g := g)).mpr
          (Or.inl ⟨rfl, Or.inl rfl⟩)⟩
    · obtain ⟨g', hg'F, vp, h1', h2'⟩ := hmax g hg hgF
      exact Finset.mem_biUnion.mpr ⟨vp, Finset.mem_biUnion.mpr ⟨g', hg'F, h2'⟩,
        (mem_auxDeg).mpr ⟨mem_auxF.mp hg, h1'⟩⟩
  have h2 : ((SlotsF F).biUnion fun vp => auxDeg n k vp).card
      ≤ ∑ vp ∈ (SlotsF F), (auxDeg n k vp).card := Finset.card_biUnion_le
  have h3 : (∑ vp ∈ (SlotsF F), (auxDeg n k vp).card)
      ≤ ∑ vp ∈ (SlotsF F), 5 * ((n - 1) * ((n - 2) * (k - 1))) :=
    Finset.sum_le_sum fun vp _ => card_auxDeg_le vp
  have h4 : (∑ vp ∈ (SlotsF F), 5 * ((n - 1) * ((n - 2) * (k - 1))))
      = (SlotsF F).card * (5 * ((n - 1) * ((n - 2) * (k - 1)))) := by
    have hx := Finset.sum_const (s := SlotsF F) (5 * ((n - 1) * ((n - 2) * (k - 1))))
    simpa [nsmul_eq_mul] using hx
  calc (auxF n k).card ≤ ((SlotsF F).biUnion fun vp => auxDeg n k vp).card := h1
    _ ≤ ∑ vp ∈ (SlotsF F), (auxDeg n k vp).card := h2
    _ ≤ ∑ vp ∈ (SlotsF F), 5 * ((n - 1) * ((n - 2) * (k - 1))) := h3
    _ = (SlotsF F).card * (5 * ((n - 1) * ((n - 2) * (k - 1)))) := h4

/-- **WHAT THE TRIVIAL ARGUMENT PROVES: `25|F| ≥ n·k`, i.e. `|F| ≥ nk/25`.**  This is the entire
content of the greedy (nibble-free) argument in the auxiliary hypergraph: a maximal matching covers
at least `3nk/25` edges of `K_n`, about a fifth of them.  The published construction needs more
than five times that (`greedy_gap`, §4). -/
theorem greedy_guarantee {n k : ℕ} {F : Fam n k} (hmax : SlotMaximal F) (hok : OkF F) (hS : SlotFree F)
    (hn : 3 ≤ n) (hk : 2 ≤ k) : 25 * F.card ≥ n * k := by
  have h1 := card_auxF_le_of_maximal hmax hok hS
  have h2 := card_auxF n k
  have h3 := card_SlotsF hok hS
  have hpos : 0 < (n - 1) * (n - 2) * (k - 1) := by
    have h1' : 0 < n - 1 := by omega
    have h2' : 0 < n - 2 := by omega
    have h3' : 0 < k - 1 := by omega
    exact Nat.mul_pos (Nat.mul_pos h1' h2') h3'
  have key : (n * k) * ((n - 1) * (n - 2) * (k - 1))
      ≤ (25 * F.card) * ((n - 1) * (n - 2) * (k - 1)) := by
    have hh : (auxF n k).card ≤ 5 * F.card * (5 * ((n - 1) * ((n - 2) * (k - 1)))) := by
      have hx := h1
      rw [h3] at hx
      exact hx
    rw [h2] at hh
    have e1 : n * ((n - 1) * ((n - 2) * (k * (k - 1))))
        = (n * k) * ((n - 1) * (n - 2) * (k - 1)) := by ring
    have e2 : 5 * F.card * (5 * ((n - 1) * ((n - 2) * (k - 1))))
        = (25 * F.card) * ((n - 1) * (n - 2) * (k - 1)) := by ring
    rw [e1, e2] at hh
    exact hh
  exact (Nat.mul_le_mul_right_iff hpos).mp key

/-! ### 4. What the budget demands, and the gap -/

/-- `↑(n-1) = n-1` in reals, for `n ≥ 1`. -/
theorem cast_sub_one {n : ℕ} (hn : 1 ≤ n) : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  push_cast
  ring

/-- `|E(K_n)|` in real numbers. -/
theorem card_edges_real (n : ℕ) :
    ((edgeFinset (Finset.univ : Finset (Verts n))).card : ℝ)
      = (n : ℝ) * ((n - 1 : ℕ) : ℝ) / 2 := by
  have h := congrArg (fun x : ℕ => (x : ℝ)) (edge_count_two_mul n)
  push_cast at h
  nlinarith

/-- The catalog budget, in canonical real form. -/
theorem cast_budget {n k D : ℕ} (δ : ℝ)
    (hbudget : (6 : ℝ) * ((k + 2 * D + 1 : ℕ) : ℝ) ≤ 5 * ((n - 1 : ℕ) : ℝ) + δ * (n : ℝ)) :
    (6 : ℝ) * ((k : ℝ) + 2 * (D : ℝ) + 1) ≤ 5 * ((n - 1 : ℕ) : ℝ) + δ * (n : ℝ) := by
  push_cast at hbudget
  exact hbudget

theorem cast_count' {n k D : ℕ} (hdeg : FirstStageCounting n k D) :
    (6 : ℝ) * ((k : ℝ)) + 5 * ((D : ℝ)) ≥ 5 * ((n - 1 : ℕ) : ℝ) :=
  cast_count hdeg

theorem edgeCoverF' {n k : ℕ} {F : Fam n k} (hok : OkF F) (hL : LinF F) :
    ((edgeFinset (Finset.univ : Finset (Verts n))).card : ℝ)
      = (3 : ℝ) * ((F.card : ℕ) : ℝ) + ((leftoverF F).card : ℝ) := by
  have h := congrArg (fun x : ℕ => (x : ℝ)) (edgeCoverF hok hL)
  push_cast at h
  exact h

theorem handshakeF' {n k D : ℕ} {F : Fam n k} (hD : SparseL (leftoverF F) D) :
    (2 : ℝ) * ((leftoverF F).card : ℝ) ≤ (n : ℝ) * ((D : ℝ)) := by
  exact_mod_cast (handshakeF hD)

/-- **THE BUDGET FORCES `6k ≤ (5+δ)n - 11`:** the greedy second stage's `2D+1` colours are not
free. -/
theorem budget_k_le {n k D : ℕ} (δ : ℝ)
    (hbudget : (6 : ℝ) * ((k + 2 * D + 1 : ℕ) : ℝ) ≤ 5 * ((n - 1 : ℕ) : ℝ) + δ * (n : ℝ)) :
    (6 : ℝ) * ((k : ℝ)) ≤ 5 * ((n - 1 : ℕ) : ℝ) + δ * (n : ℝ) - 6 := by
  have h := cast_budget δ hbudget
  have h2 : (0 : ℝ) ≤ 2 * (D : ℝ) := by positivity
  linarith

/-- **THE BUDGET AND THE SLOT COUNTING TOGETHER FORCE `7D + 6 ≤ δn`** — the converse direction of
`First.proper_fits`, and the quantitative form of "the leftover must be sparse". -/
theorem budget_le_D {n k D : ℕ} (δ : ℝ) (hdeg : FirstStageCounting n k D)
    (hbudget : (6 : ℝ) * ((k + 2 * D + 1 : ℕ) : ℝ) ≤ 5 * ((n - 1 : ℕ) : ℝ) + δ * (n : ℝ)) :
    (7 : ℝ) * ((D : ℝ)) + 6 ≤ δ * (n : ℝ) := by
  have h1 := cast_count' hdeg
  have h2 := cast_budget δ hbudget
  linarith

/-- **WHAT THE BUDGET FORCES OF THE FIRST STAGE: `42|F| ≥ n((7-δ)n-1)`.**  Together with
`edgeCoverF` and `handshakeF` this says that a matching which pays the catalog budget must have
`|F| ≈ n²/6` members — more than five times what the greedy argument of §3 delivers. -/
theorem first_stage_size {n k D : ℕ} {F : Fam n k} (hn : 1 ≤ n) (hok : OkF F) (hL : LinF F)
    (hS : SlotFree F) (hD : SparseL (leftoverF F) D)
    (hbudget : (6 : ℝ) * ((k + 2 * D + 1 : ℕ) : ℝ) ≤ 5 * ((n - 1 : ℕ) : ℝ) + δ * (n : ℝ)) :
    ((42 : ℝ)) * ((F.card : ℕ) : ℝ) ≥ (n : ℝ) * (((7 : ℝ) - δ) * (n : ℝ) - 1) := by
  have h1 := cast_count' (count_lowerF hok hL hS hD)
  have h2 := cast_budget δ hbudget
  have h3 := edgeCoverF' hok hL
  have h4 := handshakeF' hD
  have h5 := card_edges_real n
  have h6 := cast_sub_one hn
  rw [h6] at h1 h2 h5
  have hnn : (0 : ℝ) ≤ (n : ℝ) := by positivity
  nlinarith

/-- **AND THE LEFTOVER IS AT MOST A `δ/7`-FRACTION OF THE EDGES** (i.e. `14|L| ≤ (δn-6)n`; the
`δ/7` fraction of `|E| = n(n-1)/2` is `(δn-6)n/14`). -/
theorem leftover_frac_le {n k D : ℕ} {F : Fam n k} (hn : 1 ≤ n) (hok : OkF F) (hL : LinF F)
    (hS : SlotFree F) (hD : SparseL (leftoverF F) D)
    (hbudget : (6 : ℝ) * ((k + 2 * D + 1 : ℕ) : ℝ) ≤ 5 * ((n - 1 : ℕ) : ℝ) + δ * (n : ℝ)) :
    ((14 : ℝ)) * ((leftoverF F).card : ℝ) ≤ (δ * (n : ℝ) - 6) * (n : ℝ) := by
  have h7 := budget_le_D δ (count_lowerF hok hL hS hD) hbudget
  have h3 := edgeCoverF' hok hL
  have h4 := handshakeF' hD
  have h5 := card_edges_real n
  have h6 := cast_sub_one hn
  rw [h6] at h5
  have hnn : (0 : ℝ) ≤ (n : ℝ) := by positivity
  nlinarith

/-- **THE `δ ≤ 1/6` BOUND, MULTIPLIED BY `n²`.**  Provided because `nlinarith` cannot multiply a
hypothesis by a variable. -/
theorem delta_sq_bound {δ : ℝ} (hδ2 : δ ≤ 1 / 6) (n : ℕ) :
    (δ : ℝ) * (n : ℝ) * (n : ℝ) ≤ ((1 : ℝ) / 6) * (n : ℝ) * (n : ℝ) := by
  have hnn : (0 : ℝ) ≤ (n : ℝ) := by positivity
  have h1 : δ * (n : ℝ) ≤ (1 / 6) * (n : ℝ) := by nlinarith
  have h2 := mul_le_mul_of_nonneg_right h1 hnn
  nlinarith

/-- **AT THE PUBLISHED PARAMETERS (`δ ≤ 1/6`) THE FIRST STAGE COVERS MORE THAN `41/42` OF `E(K_n)`:**
`42|L| ≤ |E(K_n)|`.  This is what the papers' nibble provides and what no maximality argument can. -/
theorem leftover_frac_le_of_small {n k D : ℕ} {F : Fam n k} (hok : OkF F) (hL : LinF F)
    (hS : SlotFree F) (hD : SparseL (leftoverF F) D) (hδ2 : δ ≤ 1 / 6) (hn : 1 ≤ n)
    (hbudget : (6 : ℝ) * ((k + 2 * D + 1 : ℕ) : ℝ) ≤ 5 * ((n - 1 : ℕ) : ℝ) + δ * (n : ℝ)) :
    ((42 : ℝ)) * ((leftoverF F).card : ℝ)
      ≤ ((edgeFinset (Finset.univ : Finset (Verts n))).card : ℝ) := by
  have h1 := leftover_frac_le hn hok hL hS hD hbudget
  have h5 := card_edges_real n
  have h6 := cast_sub_one hn
  rw [h6] at h5
  have hnn : (0 : ℝ) ≤ (n : ℝ) := by positivity
  have hδn := delta_sq_bound hδ2 n
  nlinarith

/-- **THE GAP: THE GREEDY GUARANTEE `nk/25` IS STRICTLY BELOW WHAT THE BUDGET FORCES.**  Stated
cross-multiplied (`42nk < 25n((7-δ)n-1)`, i.e. `nk/25 < n((7-δ)n-1)/42`): for `δ ≤ 1/6` and
`n ≥ 1` the guaranteed size is strictly below the size of every valid first stage, by a factor
`42(5+δ)/(25(7-δ)) > 4`.  **The Rödl nibble / random triangle removal of arXiv:2208.12563 §4 =
arXiv:2207.02920 Phase 1 is genuinely necessary, and not an artifact of the analysis.** -/
theorem greedy_gap {n k D : ℕ} (hδ2 : δ ≤ 1 / 6) (hn : 1 ≤ n)
    (hbudget : (6 : ℝ) * ((k + 2 * D + 1 : ℕ) : ℝ) ≤ 5 * ((n - 1 : ℕ) : ℝ) + δ * (n : ℝ)) :
    (42 : ℝ) * ((n : ℝ) * ((k : ℝ))) < (25 : ℝ) * ((n : ℝ) * (((7 : ℝ) - δ) * (n : ℝ) - 1)) := by
  have h := budget_k_le δ hbudget
  have h6 := cast_sub_one (by omega)
  rw [h6] at h
  have hnn : (0 : ℝ) ≤ (n : ℝ) := by positivity
  have hδn := delta_sq_bound hδ2 n
  nlinarith

/-- **EVERY VALID FIRST STAGE IS STRICTLY LARGER THAN THE GREEDY GUARANTEE:** it has more than
`nk/25` members, while `greedy_guarantee` guarantees exactly that much. -/
theorem greedy_short {n k D : ℕ} {F : Fam n k} (hok : OkF F) (hL : LinF F) (hS : SlotFree F)
    (hD : SparseL (leftoverF F) D) (hδ2 : δ ≤ 1 / 6) (hn : 1 ≤ n)
    (hbudget : (6 : ℝ) * ((k + 2 * D + 1 : ℕ) : ℝ) ≤ 5 * ((n - 1 : ℕ) : ℝ) + δ * (n : ℝ)) :
    (25 : ℝ) * ((F.card : ℕ) : ℝ) > (n : ℝ) * ((k : ℝ)) := by
  have h1 := first_stage_size hn hok hL hS hD hbudget
  have h2 := greedy_gap (δ := δ) (n := n) (k := k) (D := D) hδ2 hn hbudget
  have hnn : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  nlinarith

/-- **NO FAMILY OF SIZE AT MOST THE GREEDY GUARANTEE SATISFIES THE PUBLISHED BUDGET.**  This is the
negative form: the cheapest deterministic construction of a matching in `H` cannot pay for the
catalog budget. -/
theorem no_greedy_first_stage {n k D : ℕ} {F : Fam n k} (hok : OkF F) (hL : LinF F) (hS : SlotFree F)
    (hD : SparseL (leftoverF F) D) (hδ2 : δ ≤ 1 / 6) (hn : 1 ≤ n)
    (hbudget : (6 : ℝ) * ((k + 2 * D + 1 : ℕ) : ℝ) ≤ 5 * ((n - 1 : ℕ) : ℝ) + δ * (n : ℝ))
    (hsmall : (25 : ℝ) * ((F.card : ℕ) : ℝ) ≤ (n : ℝ) * ((k : ℝ))) : False :=
  absurd (greedy_short hok hL hS hD hδ2 hn hbudget) (by linarith)

/-! ### 5. What the prize hypothesis says about its witness -/

/-- **THE PRIZE HYPOTHESIS IS STRONG: its witness is a matching of more than `n²/6` members,
covering more than `41/42` of the edges of `K_n`.**  So the object of arXiv:2208.12563 §4 is a
*near-perfect* hypergraph matching — not something a greedy argument can produce. -/
theorem witness_size {n k D : ℕ} {F : Fam n k} (hok : OkF F) (hL : LinF F) (hS : SlotFree F)
    (hD : SparseL (leftoverF F) D) (hδ2 : δ ≤ 1 / 6) (hn : 1 ≤ n)
    (hbudget : (6 : ℝ) * ((k + 2 * D + 1 : ℕ) : ℝ) ≤ 5 * ((n - 1 : ℕ) : ℝ) + δ * (n : ℝ)) :
    ((42 : ℝ)) * ((F.card : ℕ) : ℝ) ≥ (n : ℝ) * (((7 : ℝ) - δ) * (n : ℝ) - 1) ∧
      ((42 : ℝ)) * ((leftoverF F).card : ℝ)
        ≤ ((edgeFinset (Finset.univ : Finset (Verts n))).card : ℝ) :=
  ⟨first_stage_size hn hok hL hS hD hbudget,
    leftover_frac_le_of_small hok hL hS hD hδ2 hn hbudget⟩

end JSP140
