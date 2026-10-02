import JSPProblem.Hyper

/-!
# JSP-000140 — round 41: the **first-moment counting of the local conditions** of arXiv:2208.12563
# §4, in the matching world

Round 40 built the auxiliary `8`-uniform hypergraph `H` of arXiv:2208.12563 §4 as data
(`Hyper.auxF`, its census `card_auxF`, its hypervertex degrees `card_auxDeg_le`) and then ran the
*whole* of the greedy / maximal-matching argument on it, concluding (`Hyper.greedy_gap`) that a
maximal matching is short of the catalog budget by a factor of more than four.

The papers do not use a maximal matching.  They use a **partial** one, chosen so as to avoid the
hyperedges that would create a *bad four-set*, and they estimate the number of those **spoiled**
hyperedges by a first moment.  That estimate is the input of the differential-equation method of
§4, and it is a **finite counting statement about `H`** — no probability, no nibble, no local
lemma.  This file computes it.

## §1 — the four-set census

* **`card_fours_sup` — EXACTLY `n - 3` OF THE `K₄`s CONTAIN A GIVEN THREE-ELEMENT VERTEX SET**;
  in particular **`card_fours_tri`: a configuration of `H` lies in exactly `n - 3` four-sets.**
  This is the ingredient that converts a set of bad four-sets into a set of spoiled hyperedges.
* **`card_auxF_four` — THE FOUR-SET CENSUS OF `H`: EXACTLY `24·k(k-1)` HYPEREDGES OF `H` HAVE THEIR
  THREE VERTICES IN A GIVEN FOUR-SET.**  This is the exact local bound the first moment needs:
  one bad four-set spoils at most `24k(k-1)` hyperedges, whatever "bad" means.

## §2 — spoiled hyperedges

* **`spoilF (k := k) B`** — the hyperedges of `H` lying inside one of the four-sets of `B`.
* **`card_spoilF_le`, `card_spoilF_ge`, `spoil_squeeze` — THE TWO SIDES OF THE FIRST MOMENT:**
  `24·k(k-1)·|B| ≤ (n-3)·|spoilF (k := k) B| ≤ 24·k(k-1)·|B|`.  Bad four-sets and spoiled hyperedges are
  equivalent up to a factor `n-3`, and the estimate is exact in the four-set direction.

## §3 — the avoidance rule, and its price

* **`SlotFresh`, `AvoidClosed`** — the rule "add a hyperedge whenever it shares no slot with the
  family and is not spoiled", and its fixed point.
* **`closed_census` — THE CENSUS OF A CLOSED FAMILY: `|E(H)| ≤ 25(n-1)(n-2)(k-1)·|F| + |spoilF|`.**
  Every hyperedge of `H` is either in `F`, or blocked by a slot of `F` (round 40's count), or
  spoiled.
* **`avoid_first_moment` — WHAT THE RULE DELIVERS:** with the census `closed_census` and
  `card_spoilF_le`, `n(n-1)(n-2)·k(k-1) ≤ 25(n-1)(n-2)(k-1)·|F| + 24·k(k-1)·|B|`.
* **`avoid_certify` — and, after dividing, `25·|F| + n ≥ n·k` as soon as `24k|B| ≤ n(n-1)(n-2)`:**
  a four-set condition costing `o(n²)` four-sets costs the rule at most `n` slots.
* **`avoid_gap` — THE PRICE, AS A THEOREM:** with the budget `6k ≤ (5+δ)n − 11` at `δ ≤ 1/6`, the
  guarantee `n(k-1)/25` is *strictly* below the size every valid first stage must have,
  `n((7−δ)n−1)/42`.  So **maximality-with-avoidance cannot certify the budget, for any choice of
  the bad four-sets**: the Rödl nibble is needed for the matching itself, not for the local
  conditions.
* **`badFours`, `badFours_eq_empty_iff`, `spoilF_empty_of_badFours`** — the bridge back to the
  catalog condition: `Admissible c ↔ badFours c = ∅`, and an admissible colouring spoils nothing.
-/

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

namespace JSP140

attribute [local instance] Classical.propDecidable

variable {n k : ℕ}

/-! ### 0. Counting tools -/

/-- **The indicator of a predicate, summed over the ambient type, is the cardinality of the
corresponding filter.** -/
theorem sum_ite_mem_card {α : Type*} [Fintype α] [DecidableEq α] (Q : α → Prop)
    [DecidablePred Q] : (∑ x : α, ((if Q x then 1 else 0 : ℕ))) = (Finset.univ.filter Q).card := by
  rw [← Finset.sum_filter (Q) (fun _ => (1 : ℕ))]
  exact (Finset.card_eq_sum_ones _).symm

/-- **The indicator of "in `s` and satisfying `P`", summed over the ambient type, is the
cardinality of `s.filter P`.** -/
theorem sum_ite_filter_card {α : Type*} [Fintype α] [DecidableEq α] (s : Finset α) (P : α → Prop)
    [DecidablePred P] : (∑ x : α, ((if x ∈ s ∧ P x then 1 else 0 : ℕ))) = (s.filter P).card := by
  have h1 : (∑ x : α, ((if x ∈ s ∧ P x then 1 else 0 : ℕ)))
      = (∑ x : α, ((if (fun y : α => y ∈ s ∧ P y) x then 1 else 0 : ℕ))) := rfl
  rw [h1, sum_ite_mem_card]
  have h2 : (Finset.univ : Finset α).filter (fun y : α => y ∈ s ∧ P y) = s.filter P := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [h2]

/-! ### 1. Four-sets: how many of them pass through a given vertex set -/

@[simp] theorem mem_fourSets {n : ℕ} {S : Finset (Verts n)} : S ∈ fourSets n ↔ S.card = 4 := by
  simp [fourSets]

/-- **THE FOUR-SET CENSUS FROM THE OTHER SIDE: EXACTLY `n - 3` OF THE `K₄`s OF THE DEVELOPMENT
CONTAIN A GIVEN THREE-ELEMENT VERTEX SET.**  This is the other half of the census of §4, and it is
what turns a set of bad four-sets into a set of spoiled hyperedges: each spoiled hyperedge lies in
at most `n - 3` four-sets. -/
theorem card_fours_sup {n : ℕ} (T : Finset (Verts n)) (hT : T.card = 3) (hn : 4 ≤ n) :
    ((fourSets n).filter (fun S => T ⊆ S)).card = n - 3 := by
  have hDs : (Finset.univ : Finset (Verts n)).filter (fun x => ¬ (x ∈ T))
      = (Finset.univ : Finset (Verts n)) \ T := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and]
  have hDcard : ((Finset.univ : Finset (Verts n)).filter (fun x => ¬ (x ∈ T))).card = n - 3 := by
    rw [hDs, Finset.card_sdiff_of_subset (Finset.subset_univ T), Finset.card_univ, Fintype.card_fin,
      hT]
  apply (Finset.card_bij
      (s := (Finset.univ : Finset (Verts n)).filter (fun x => ¬ (x ∈ T)))
      (t := (fourSets n).filter (fun S => T ⊆ S)) (fun x _ => insert x T) ?_ ?_ ?_).symm.trans
    hDcard
  · intro x hx
    have hx' : ¬ (x ∈ T) := (Finset.mem_filter.mp hx).2
    have hcard : (insert x T : Finset (Verts n)).card = 4 := by
      rw [Finset.card_insert_of_notMem hx', hT]
    exact Finset.mem_filter.mpr ⟨mem_fourSets.mpr hcard, Finset.subset_insert x T⟩
  · intro x₁ hx₁ x₂ hx₂ heq
    by_cases h1 : x₁ = x₂
    · exact h1
    · exfalso
      have h2 : x₂ ∉ insert x₁ T := by
        rw [Finset.mem_insert]
        intro hmem
        rcases hmem with hmem | hmem
        · exact h1 hmem.symm
        · exact (Finset.mem_filter.mp hx₂).2 hmem
      have h3 : x₂ ∈ insert x₁ T := by
        rw [heq]
        exact Finset.mem_insert_self _ _
      exact h2 h3
  · intro b hb
    obtain ⟨hbc, hsub⟩ : b.card = 4 ∧ T ⊆ b := by
      simpa only [Finset.mem_filter, mem_fourSets] using hb
    have hne : (b \ T).card = 1 := by
      have h1 : (b \ T).card = b.card - (T ∩ b).card := Finset.card_sdiff
      have h2 : T ∩ b = T := by
        apply Finset.ext
        intro y
        simp only [Finset.mem_inter]
        constructor
        · intro h
          exact h.1
        · intro h
          exact ⟨h, hsub h⟩
      rw [hbc, h2, hT] at h1
      omega
    obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hne
    have hmemx : x ∈ b \ T := by
      rw [hx]
      exact Finset.mem_singleton.mpr rfl
    have hxT : ¬ (x ∈ T) := Finset.mem_sdiff.mp hmemx |>.2
    have hxB : x ∈ b := Finset.mem_sdiff.mp hmemx |>.1
    refine ⟨x, ?_, ?_⟩
    · rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ x, hxT⟩
    · ext y
      constructor
      · intro hy
        rw [Finset.mem_insert] at hy
        rcases hy with rfl | hy
        · exact hxB
        · exact hsub hy
      · intro hy
        by_cases h1 : y ∈ T
        · exact Finset.mem_insert.mpr (Or.inr h1)
        · have hmem : y ∈ b \ T := Finset.mem_sdiff.mpr ⟨hy, h1⟩
          have hy2 : y ∈ {x} := hx ▸ hmem
          exact Finset.mem_insert.mpr (Or.inl (Finset.mem_singleton.mp hy2))

/-- **A CONFIGURATION OF `H` LIES IN EXACTLY `n - 3` FOUR-SETS.** -/
theorem card_fours_tri {n k : ℕ} {g : Cfg n k} (hg : Ok g) (hn : 4 ≤ n) :
    ((fourSets n).filter (fun S => cfgVerts g ⊆ S)).card = n - 3 :=
  card_fours_sup (cfgVerts g) (card_cfgVerts hg) hn

/-- The three vertices of a configuration are in a four-set iff each of them is. -/
theorem cfgVerts_sub_iff {n k : ℕ} (g : Cfg n k) (S : Finset (Verts n)) :
    cfgVerts g ⊆ S ↔ cfgU g ∈ S ∧ cfgP g ∈ S ∧ cfgQ g ∈ S := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · exact h (by simp [cfgVerts, triVerts])
    · exact h (by simp [cfgVerts, triVerts])
    · exact h (by simp [cfgVerts, triVerts])
  · intro h z hz
    have hz' : z = cfgU g ∨ z = cfgP g ∨ z = cfgQ g := by
      simpa [cfgVerts, triVerts] using hz
    rcases hz' with rfl | rfl | rfl
    · exact h.1
    · exact h.2.1
    · exact h.2.2

/-- **THE FOUR-SET CENSUS OF `H`: EXACTLY `24·k(k-1)` HYPEREDGES OF `H` HAVE THEIR THREE VERTICES
IN A GIVEN FOUR-SET.**  Twelve ordered triples of distinct vertices out of the four, and `k(k-1)`
ordered pairs of distinct colours.  This is the exact local bound of the first-moment estimate of
§4: one bad four-set spoils at most this many hyperedges, whatever "bad" means. -/
theorem card_auxF_four {n k : ℕ} (S : Finset (Verts n)) (hS : S.card = 4) :
    ((auxF n k).filter (fun g => cfgVerts g ⊆ S)).card = 24 * (k * (k - 1)) := by
  have hcard2 : ∀ (a b : Verts n), a ∈ S → b ∈ S → a ≠ b →
      (S.filter (fun q => q ∈ S ∧ q ≠ a ∧ q ≠ b)).card = S.card - 2 := by
    intro a b ha hb hab
    have hA : S.filter (fun q => q ∈ S ∧ q ≠ a ∧ q ≠ b)
        = S.filter (fun q => q ≠ a ∧ q ≠ b) := by
      ext q
      simp only [Finset.mem_filter]
      tauto
    have hB : S.filter (fun q => q ≠ a ∧ q ≠ b)
        = (S.filter (fun q => q ≠ a)).filter (fun q => q ≠ b) := by
      rw [← Finset.filter_filter]
    have h1 : S.filter (fun q => q ∈ S ∧ q ≠ a ∧ q ≠ b)
        = (S.filter (fun q => q ≠ a)).filter (fun q => q ≠ b) := hA.trans hB
    rw [h1, card_filter_ne (A := S.filter (fun q => q ≠ a)) (a := b)
      (Finset.mem_filter.mpr ⟨hb, Ne.symm hab⟩), card_filter_ne (A := S) (a := a) ha]
    omega
  have h0 : ((auxF n k).filter (fun g => cfgVerts g ⊆ S)).card
      = ∑ g : Cfg n k, ((if Ok g ∧ cfgVerts g ⊆ S then 1 else 0) : ℕ) := by
    rw [← sum_ite_filter_card (s := auxF n k) (P := fun g : Cfg n k => cfgVerts g ⊆ S)]
    refine Finset.sum_congr rfl (fun g _ => ?_)
    exact ite_eq_of_iff
      ⟨fun h => ⟨mem_auxF.mp h.1, h.2⟩, fun h => ⟨mem_auxF.mpr h.1, h.2⟩⟩
  have h1 : (∑ g : Cfg n k, ((if Ok g ∧ cfgVerts g ⊆ S then 1 else 0) : ℕ))
      = ∑ u : Verts n, ∑ p : Verts n, ∑ q : Verts n, ∑ i : Fin k, ∑ j : Fin k,
        (if ((u ∈ S ∧ p ∈ S ∧ u ≠ p) ∧ (q ∈ S ∧ u ≠ q ∧ p ≠ q)) ∧ (i ≠ j) then 1 else 0) := by
    rw [sum_univ_prod5]
    refine Finset.sum_congr rfl (fun u _ => ?_)
    refine Finset.sum_congr rfl (fun p _ => ?_)
    refine Finset.sum_congr rfl (fun q _ => ?_)
    refine Finset.sum_congr rfl (fun i _ => ?_)
    refine Finset.sum_congr rfl (fun j _ => ?_)
    have hOk : Ok (u, p, q, i, j) ↔ u ≠ p ∧ u ≠ q ∧ p ≠ q ∧ i ≠ j := by
      simp only [Ok, cfgU, cfgP, cfgQ, cfgI, cfgJ]
    have hcond : Ok (u, p, q, i, j) ∧ cfgVerts (u, p, q, i, j) ⊆ S
        ↔ ((u ∈ S ∧ p ∈ S ∧ u ≠ p) ∧ (q ∈ S ∧ u ≠ q ∧ p ≠ q)) ∧ (i ≠ j) := by
      rw [hOk, cfgVerts_sub_iff (u, p, q, i, j) S]
      tauto
    exact ite_eq_of_iff hcond
  have h2 : ∀ (u p q : Verts n),
      (∑ i : Fin k, ∑ j : Fin k,
        (if ((u ∈ S ∧ p ∈ S ∧ u ≠ p) ∧ (q ∈ S ∧ u ≠ q ∧ p ≠ q)) ∧ (i ≠ j) then 1 else 0))
        = if (u ∈ S ∧ p ∈ S ∧ u ≠ p) ∧ (q ∈ S ∧ u ≠ q ∧ p ≠ q) then k * (k - 1) else 0 := by
    intro u p q
    rw [sum_ite_and]
  have h3 : ∀ (u p : Verts n),
      (∑ q : Verts n,
        (if (u ∈ S ∧ p ∈ S ∧ u ≠ p) ∧ (q ∈ S ∧ u ≠ q ∧ p ≠ q) then k * (k - 1) else 0))
        = if u ∈ S ∧ p ∈ S ∧ u ≠ p then (S.card - 2) * (k * (k - 1)) else 0 := by
    intro u p
    by_cases hC : u ∈ S ∧ p ∈ S ∧ u ≠ p
    · rw [if_pos hC]
      have hiff : ∀ x : Verts n, (x ∈ S ∧ u ≠ x ∧ p ≠ x) ↔ (x ∈ S ∧ x ≠ u ∧ x ≠ p) := by
        intro x
        constructor
        · rintro ⟨h1, h2, h3⟩
          exact ⟨h1, Ne.symm h2, Ne.symm h3⟩
        · rintro ⟨h1, h2, h3⟩
          exact ⟨h1, Ne.symm h2, Ne.symm h3⟩
      have e : (∑ q : Verts n,
          (if (u ∈ S ∧ p ∈ S ∧ u ≠ p) ∧ (q ∈ S ∧ u ≠ q ∧ p ≠ q) then k * (k - 1) else 0))
          = ∑ q : Verts n, (if q ∈ S ∧ q ≠ u ∧ q ≠ p then k * (k - 1) else 0) := by
        refine Finset.sum_congr rfl (fun q _ => ?_)
        exact ite_eq_of_iff
          ⟨fun h => (hiff q).mp h.2,
            fun h => ⟨And.intro hC.1 (And.intro hC.2.1 hC.2.2), (hiff q).mpr h⟩⟩
      rw [e]
      have hq : S.filter (fun q => q ∈ S ∧ q ≠ u ∧ q ≠ p)
          = (Finset.univ : Finset (Verts n)).filter (fun q => q ∈ S ∧ q ≠ u ∧ q ≠ p) := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        tauto
      have e2 : (∑ q : Verts n, (if q ∈ S ∧ q ≠ u ∧ q ≠ p then k * (k - 1) else 0))
          = (k * (k - 1)) * (S.filter (fun q => q ∈ S ∧ q ≠ u ∧ q ≠ p)).card := by
        rw [hq]
        exact sum_ite_mem_mul (P := fun q => q ∈ S ∧ q ≠ u ∧ q ≠ p) (k * (k - 1))
      rw [e2, hcard2 u p hC.1 hC.2.1 hC.2.2]
      ring
    · rw [if_neg hC]
      refine Finset.sum_eq_zero (fun q _ => ?_)
      rw [if_neg (fun h => hC h.1)]
  have h4 : ∀ (u : Verts n),
      (∑ p : Verts n,
        (if u ∈ S ∧ p ∈ S ∧ u ≠ p then (S.card - 2) * (k * (k - 1)) else 0))
        = if u ∈ S then (S.card - 1) * ((S.card - 2) * (k * (k - 1))) else 0 := by
    intro u
    by_cases hu : u ∈ S
    · rw [if_pos hu]
      have hiff : ∀ x : Verts n, (u ∈ S ∧ x ∈ S ∧ u ≠ x) ↔ (x ∈ S ∧ x ≠ u) := by
        intro x
        constructor
        · rintro ⟨h1, h2, h3⟩
          exact ⟨h2, Ne.symm h3⟩
        · rintro ⟨h1, h2⟩
          exact And.intro hu (And.intro h1 (Ne.symm h2))
      have e : (∑ p : Verts n,
          (if u ∈ S ∧ p ∈ S ∧ u ≠ p then (S.card - 2) * (k * (k - 1)) else 0))
          = ∑ p : Verts n, (if p ∈ S ∧ p ≠ u then (S.card - 2) * (k * (k - 1)) else 0) := by
        refine Finset.sum_congr rfl (fun p _ => ?_)
        exact ite_eq_of_iff (hiff p)
      rw [e]
      have hp : S.filter (fun p => p ∈ S ∧ p ≠ u)
          = (Finset.univ : Finset (Verts n)).filter (fun p => p ∈ S ∧ p ≠ u) := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        tauto
      have e2 : (∑ p : Verts n, (if p ∈ S ∧ p ≠ u then (S.card - 2) * (k * (k - 1)) else 0))
          = ((S.card - 2) * (k * (k - 1))) * (S.filter (fun p => p ∈ S ∧ p ≠ u)).card := by
        rw [hp]
        exact sum_ite_mem_mul (P := fun p => p ∈ S ∧ p ≠ u) ((S.card - 2) * (k * (k - 1)))
      have hcard1 : (S.filter (fun p => p ∈ S ∧ p ≠ u)).card = S.card - 1 := by
        have h1 : S.filter (fun p => p ∈ S ∧ p ≠ u) = S.filter (fun p => p ≠ u) := by
          ext x
          simp only [Finset.mem_filter]
          tauto
        rw [h1, card_filter_ne (A := S) (a := u) hu]
      rw [e2, hcard1]
      ring
    · rw [if_neg hu]
      refine Finset.sum_eq_zero (fun p _ => ?_)
      rw [if_neg (fun h => hu h.1)]
  have h5 : (∑ u : Verts n,
      (if u ∈ S then (S.card - 1) * ((S.card - 2) * (k * (k - 1))) else 0))
      = S.card * ((S.card - 1) * ((S.card - 2) * (k * (k - 1)))) := by
    have hu : (Finset.univ : Finset (Verts n)).filter (fun u => u ∈ S) = S := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have e : (∑ u : Verts n,
        (if u ∈ S then (S.card - 1) * ((S.card - 2) * (k * (k - 1))) else 0))
        = ((S.card - 1) * ((S.card - 2) * (k * (k - 1))))
            * ((Finset.univ : Finset (Verts n)).filter (fun u => u ∈ S)).card := by
      exact sum_ite_mem_mul (P := fun u => u ∈ S) ((S.card - 1) * ((S.card - 2) * (k * (k - 1))))
    rw [e, hu]
    ring
  rw [h0, h1]
  simp_rw [h2]
  simp_rw [h3]
  simp_rw [h4]
  simp_rw [h5]
  rw [hS]
  ring

/-- **IMPOSING A STRONGER PREDICATE INSIDE A FILTER CANNOT INCREASE THE CARDINALITY.** -/
theorem card_filter_le {α : Type*} (s : Finset α) (P Q : α → Prop) [DecidablePred P]
    [DecidablePred Q] (h : ∀ x ∈ s, P x → Q x) : (s.filter P).card ≤ (s.filter Q).card := by
  have e1 : (s.filter P).card = ∑ i ∈ s, ((if P i then 1 else 0 : ℕ)) :=
    Finset.card_filter (p := P) (s)
  have e2 : (s.filter Q).card = ∑ i ∈ s, ((if Q i then 1 else 0 : ℕ)) :=
    Finset.card_filter (p := Q) (s)
  rw [e1, e2]
  refine Finset.sum_le_sum fun x _ => ?_
  have hx : x ∈ s := by assumption
  by_cases hP : P x
  · by_cases hQ : Q x
    · rw [if_pos hP, if_pos hQ]
    · rw [if_pos hP, if_neg hQ]
      exact (hQ (h x hx hP)).elim
  · rw [if_neg hP]
    simp

/-! ### 2. Spoiled hyperedges: the two sides of the first moment -/

/-- **THE SPOILED HYPEREDGES OF `H`:** those lying inside one of the four-sets of `B`.  In §4 of
arXiv:2208.12563 these are the hyperedges which, if added to the first stage, would create a bad
four-set; the first moment bounds their number. -/
noncomputable def spoilF {n k : ℕ} (B : Finset (Finset (Verts n))) : Finset (Cfg n k) :=
  (auxF n k).filter (fun g => ∃ S, S.card = 4 ∧ S ∈ B ∧ cfgVerts g ⊆ S)

theorem mem_spoilF {n k : ℕ} {B : Finset (Finset (Verts n))} {g : Cfg n k} :
    g ∈ spoilF (k := k) B ↔ g ∈ auxF n k ∧ ∃ S, S.card = 4 ∧ S ∈ B ∧ cfgVerts g ⊆ S := by
  rw [spoilF, Finset.mem_filter]

/-- **THE DOUBLE COUNT OF §2: the pairs `(hyperedge of H, four-set of B containing its vertices)`,
counted from either side.** -/
theorem spoil_double {n k : ℕ} (B : Finset (Finset (Verts n))) :
    (∑ g : Cfg n k, ((fourSets n).filter
        (fun S => S ∈ B ∧ g ∈ auxF n k ∧ cfgVerts g ⊆ S)).card)
      = (∑ S ∈ fourSets n,
          ((if S ∈ B then ((auxF n k).filter (fun g => cfgVerts g ⊆ S)).card else 0) : ℕ)) := by
  have hL : (∑ g : Cfg n k, ((fourSets n).filter
        (fun S => S ∈ B ∧ g ∈ auxF n k ∧ cfgVerts g ⊆ S)).card)
      = ∑ g : Cfg n k, ∑ S ∈ fourSets n,
        ((if S ∈ B ∧ g ∈ auxF n k ∧ cfgVerts g ⊆ S then 1 else 0) : ℕ) := by
    refine Finset.sum_congr rfl (fun g _ => ?_)
    have hh : ((fourSets n).filter
        (fun S : Finset (Verts n) => S ∈ B ∧ g ∈ auxF n k ∧ cfgVerts g ⊆ S)).card
        = ∑ i ∈ fourSets n, ((if i ∈ B ∧ g ∈ auxF n k ∧ cfgVerts g ⊆ i then 1 else 0) : ℕ) :=
      Finset.card_filter (p := fun S : Finset (Verts n) => S ∈ B ∧ g ∈ auxF n k
        ∧ cfgVerts g ⊆ S) (fourSets n)
    rw [hh]
  have hM : (∑ g : Cfg n k, ∑ S ∈ fourSets n,
        (if S ∈ B ∧ g ∈ auxF n k ∧ cfgVerts g ⊆ S then 1 else 0))
      = ∑ S ∈ fourSets n, ∑ g : Cfg n k,
        (if S ∈ B ∧ g ∈ auxF n k ∧ cfgVerts g ⊆ S then 1 else 0) :=
    Finset.sum_comm
  have hR : (∑ S ∈ fourSets n, ∑ g : Cfg n k,
        (if S ∈ B ∧ g ∈ auxF n k ∧ cfgVerts g ⊆ S then 1 else 0))
      = ∑ S ∈ fourSets n,
        ((if S ∈ B then ((auxF n k).filter (fun g => cfgVerts g ⊆ S)).card else 0) : ℕ) := by
    refine Finset.sum_congr rfl (fun S _ => ?_)
    by_cases hS : S ∈ B
    · rw [if_pos hS]
      have hiff : ∀ g : Cfg n k, (S ∈ B ∧ g ∈ auxF n k ∧ cfgVerts g ⊆ S)
          ↔ (g ∈ auxF n k ∧ cfgVerts g ⊆ S) := by
        intro g
        constructor
        · rintro ⟨h1, h2, h3⟩
          exact ⟨h2, h3⟩
        · rintro ⟨h2, h3⟩
          exact ⟨hS, h2, h3⟩
      calc (∑ g : Cfg n k, (if S ∈ B ∧ g ∈ auxF n k ∧ cfgVerts g ⊆ S then 1 else 0))
          = ∑ g : Cfg n k, (if g ∈ auxF n k ∧ cfgVerts g ⊆ S then 1 else 0) := by
            refine Finset.sum_congr rfl (fun g _ => ?_)
            exact ite_eq_of_iff (hiff g)
        _ = ((auxF n k).filter (fun g => cfgVerts g ⊆ S)).card :=
          sum_ite_filter_card (P := fun g : Cfg n k => cfgVerts g ⊆ S) (auxF n k)
    · rw [if_neg hS]
      refine Finset.sum_eq_zero (fun g _ => ?_)
      rw [if_neg (fun h => hS h.1)]
  rw [hL, hM, hR]

/-- **THE FIRST MOMENT, UPPER SIDE: `|B|` bad four-sets spoil at most `24·k(k-1)·|B|` hyperedges of
`H`.**  This is the estimate the first-moment argument of §4 needs, and it is *exact* in the
four-set direction (`card_auxF_four`): one bad four-set spoils exactly `24k(k-1)` hyperedges. -/
theorem card_spoilF_le {n k : ℕ} {B : Finset (Finset (Verts n))} (hB : ∀ S ∈ B, S.card = 4) :
    (spoilF (k := k) B).card ≤ 24 * (k * (k - 1)) * B.card := by
  have hsub : spoilF (k := k) B
      ⊆ B.biUnion (fun S => (auxF n k).filter (fun g => cfgVerts g ⊆ S)) := by
    intro g hg
    rw [mem_spoilF] at hg
    obtain ⟨hgA, S, _, hSB, hP⟩ := hg
    exact Finset.mem_biUnion.mpr ⟨S, hSB, Finset.mem_filter.mpr ⟨hgA, hP⟩⟩
  have hsum : (∑ S ∈ B, ((auxF n k).filter (fun g => cfgVerts g ⊆ S)).card)
      = 24 * (k * (k - 1)) * B.card := by
    have e1 : (∑ S ∈ B, ((auxF n k).filter (fun g => cfgVerts g ⊆ S)).card)
        = ∑ S ∈ B, 24 * (k * (k - 1)) := by
      refine Finset.sum_congr rfl (fun S hS => ?_)
      exact card_auxF_four S (hB S hS)
    rw [e1]
    have hx := Finset.sum_const (s := B) (24 * (k * (k - 1)))
    simpa [nsmul_eq_mul, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hx
  calc (spoilF (k := k) B).card
      ≤ (B.biUnion (fun S => (auxF n k).filter (fun g => cfgVerts g ⊆ S))).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ S ∈ B, ((auxF n k).filter (fun g => cfgVerts g ⊆ S)).card := Finset.card_biUnion_le
    _ = 24 * (k * (k - 1)) * B.card := hsum

/-- **THE FIRST MOMENT, LOWER SIDE: `|B|` bad four-sets spoil AT LEAST `24·k(k-1)·|B|` hyperedges
`n-3` times over**, because a hyperedge of `H` lies in at most `n-3` four-sets
(`card_fours_tri`).  Together with `card_spoilF_le` this is the whole estimate of §4: bad four-sets
and spoiled hyperedges are equivalent up to a factor `n-3`. -/
theorem card_spoilF_ge {n k : ℕ} {B : Finset (Finset (Verts n))} (hB : ∀ S ∈ B, S.card = 4)
    (hn : 4 ≤ n) : 24 * (k * (k - 1)) * B.card ≤ (n - 3) * (spoilF (k := k) B).card := by
  have hLo : (∑ S ∈ fourSets n,
        ((if S ∈ B then ((auxF n k).filter (fun g => cfgVerts g ⊆ S)).card else 0) : ℕ))
      = 24 * (k * (k - 1)) * B.card := by
    have e1 : (∑ S ∈ fourSets n,
        (if S ∈ B then ((auxF n k).filter (fun g => cfgVerts g ⊆ S)).card else 0))
        = ∑ S ∈ fourSets n, (if S ∈ B then 24 * (k * (k - 1)) else 0) := by
      refine Finset.sum_congr rfl (fun S hS => ?_)
      by_cases h2 : S ∈ B
      · simp only [h2, ite_true, card_auxF_four S (hB S h2)]
      · simp only [h2, ite_false]
    rw [e1]
    have e2 : (∑ S ∈ fourSets n, (if S ∈ B then 24 * (k * (k - 1)) else 0))
        = 24 * (k * (k - 1)) * ((fourSets n).filter (fun S => S ∈ B)).card := by
      rw [← Finset.sum_filter (s := fourSets n) (p := fun S : Finset (Verts n) => S ∈ B)
        (f := fun _ => 24 * (k * (k - 1)))]
      have hx := Finset.sum_const (s := (fourSets n).filter (fun S => S ∈ B)) (24 * (k * (k - 1)))
      simpa [nsmul_eq_mul, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hx
    have hfil : (fourSets n).filter (fun S => S ∈ B) = B := by
      ext S
      simp only [Finset.mem_filter, mem_fourSets]
      constructor
      · rintro ⟨_, h2⟩
        exact h2
      · rintro h2
        exact ⟨hB S h2, h2⟩
    rw [e2, hfil]
  have hUp : (∑ g : Cfg n k, ((fourSets n).filter
        (fun S => S ∈ B ∧ g ∈ auxF n k ∧ cfgVerts g ⊆ S)).card)
      ≤ (n - 3) * (spoilF (k := k) B).card := by
    have h1 : ∀ g : Cfg n k,
        ((fourSets n).filter (fun S => S ∈ B ∧ g ∈ auxF n k ∧ cfgVerts g ⊆ S)).card
          ≤ (n - 3) * ((if g ∈ spoilF (k := k) B then 1 else 0) : ℕ) := by
      intro g
      by_cases hg : g ∈ auxF n k
      · by_cases hsp : g ∈ spoilF (k := k) B
        · rw [if_pos hsp]
          have h2 : ((fourSets n).filter (fun S => S ∈ B ∧ g ∈ auxF n k ∧ cfgVerts g ⊆ S)).card
              ≤ ((fourSets n).filter (fun S => cfgVerts g ⊆ S)).card :=
            card_filter_le (s := fourSets n) (P := fun S : Finset (Verts n) => S ∈ B
              ∧ g ∈ auxF n k ∧ cfgVerts g ⊆ S) (Q := fun S : Finset (Verts n) => cfgVerts g ⊆ S)
              (fun _ hS hP => by
                rcases hP with ⟨h1, h2, h3⟩
                exact h3)
          have h3 := card_fours_tri (mem_auxF.mp hg) hn
          omega
        · have h2 : ((fourSets n).filter
              (fun S => S ∈ B ∧ g ∈ auxF n k ∧ cfgVerts g ⊆ S)).card ≤ 0 := by
            have e : ((fourSets n).filter
                (fun S => S ∈ B ∧ g ∈ auxF n k ∧ cfgVerts g ⊆ S)).card
                = ∑ S ∈ fourSets n, ((if S ∈ B ∧ g ∈ auxF n k ∧ cfgVerts g ⊆ S then 1
                    else 0) : ℕ) :=
              Finset.card_filter (p := fun S : Finset (Verts n) => S ∈ B ∧ g ∈ auxF n k
                ∧ cfgVerts g ⊆ S) (fourSets n)
            rw [e]
            have e0 : (∑ S ∈ fourSets n,
                ((if S ∈ B ∧ g ∈ auxF n k ∧ cfgVerts g ⊆ S then 1 else 0) : ℕ)) = 0 := by
              refine Finset.sum_eq_zero (fun S hS => ?_)
              by_cases h1 : S ∈ B ∧ g ∈ auxF n k ∧ cfgVerts g ⊆ S
              · rw [if_pos h1]
                have hmem : g ∈ spoilF (k := k) B := by
                  refine mem_spoilF.mpr ⟨hg, S, mem_fourSets.mp hS, h1.1, ?_⟩
                  exact h1.2.2
                exact (hsp hmem).elim
              · rw [if_neg h1]
            omega
          rw [if_neg hsp]
          omega
      · have hsp : g ∉ spoilF (k := k) B := by
          rw [mem_spoilF]
          exact fun h => hg h.1
        have h2 : ((fourSets n).filter
            (fun S => S ∈ B ∧ g ∈ auxF n k ∧ cfgVerts g ⊆ S)).card ≤ 0 := by
          have e : ((fourSets n).filter
              (fun S => S ∈ B ∧ g ∈ auxF n k ∧ cfgVerts g ⊆ S)).card
              = ∑ S ∈ fourSets n, ((if S ∈ B ∧ g ∈ auxF n k ∧ cfgVerts g ⊆ S then 1
                  else 0) : ℕ) :=
            Finset.card_filter (p := fun S : Finset (Verts n) => S ∈ B ∧ g ∈ auxF n k
              ∧ cfgVerts g ⊆ S) (fourSets n)
          rw [e]
          have e0 : (∑ S ∈ fourSets n,
              ((if S ∈ B ∧ g ∈ auxF n k ∧ cfgVerts g ⊆ S then 1 else 0) : ℕ)) = 0 := by
            refine Finset.sum_eq_zero (fun S _ => ?_)
            by_cases h1 : S ∈ B ∧ g ∈ auxF n k ∧ cfgVerts g ⊆ S
            · rw [if_pos h1]
              exact (hg h1.2.1).elim
            · rw [if_neg h1]
          omega
        rw [if_neg hsp]
        omega
    have hsum : (∑ g : Cfg n k, ((fourSets n).filter
          (fun S => S ∈ B ∧ g ∈ auxF n k ∧ cfgVerts g ⊆ S)).card)
        ≤ ∑ g : Cfg n k, ((n - 3) * ((if g ∈ spoilF (k := k) B then 1 else 0) : ℕ)) := by
      exact Finset.sum_le_sum fun g _ => h1 g
    have htot : (∑ g : Cfg n k, ((n - 3) * ((if g ∈ spoilF (k := k) B then 1 else 0) : ℕ)))
        = (n - 3) * (spoilF (k := k) B).card := by
      calc (∑ g : Cfg n k, ((n - 3) * ((if g ∈ spoilF (k := k) B then 1 else 0) : ℕ)))
          = ∑ g : Cfg n k, ((if g ∈ spoilF (k := k) B then (n - 3) else 0) : ℕ) := by
            refine Finset.sum_congr rfl (fun g _ => ?_)
            by_cases hP : g ∈ spoilF (k := k) B <;> simp [hP]
        _ = (n - 3) * (spoilF (k := k) B).card := by
          rw [sum_ite_mem_mul (P := fun g : Cfg n k => g ∈ spoilF (k := k) B) (n - 3)]
          have heq : (Finset.univ : Finset (Cfg n k)).filter
              (fun g : Cfg n k => g ∈ spoilF (k := k) B) = spoilF (k := k) B := by
            ext g
            simp
          rw [heq]
    omega
  have hD := spoil_double (k := k) B
  omega

/-- **THE TWO SIDES TOGETHER: THE SPOILED SET OF `H` HAS THE SIZE OF THE SET OF BAD FOUR-SETS, UP TO
THE FACTOR `n-3`.**  This is the exact content of the first moment of §4, and it is a *finite
counting statement*: no probability, no nibble, no local lemma. -/
theorem spoil_squeeze {n k : ℕ} {B : Finset (Finset (Verts n))} (hB : ∀ S ∈ B, S.card = 4)
    (hn : 4 ≤ n) : 24 * (k * (k - 1)) * B.card ≤ (n - 3) * (spoilF (k := k) B).card
      ∧ (spoilF (k := k) B).card ≤ 24 * (k * (k - 1)) * B.card :=
  ⟨card_spoilF_ge hB hn, card_spoilF_le hB⟩

/- PART3 -/
/-! ### 3. The avoidance rule, and its price -/

/-- A hyperedge of `H` is **fresh** for a family if it shares none of its five slots with it. -/
def SlotFresh {n k : ℕ} (F : Fam n k) (g : Cfg n k) : Prop :=
  ∀ vp : Verts n × Fin k, vp ∈ cfgSlots g → vp ∉ SlotsF F

/-- **THE AVOIDANCE RULE OF §4 AT ITS FIXED POINT.**  Every hyperedge of `H` which is outside `F`,
shares no slot with `F` and is not spoiled by `B` does not exist: the rule "add a hyperedge
whenever it is unblocked and unspoiled" has finished.  This is the deterministic procedure the
differential-equation method of §4 improves upon. -/
def AvoidClosed {n k : ℕ} (B : Finset (Finset (Verts n))) (F : Fam n k) : Prop :=
  ∀ g : Cfg n k, g ∈ auxF n k → g ∉ F → SlotFresh F g → g ∈ spoilF (k := k) B

/-- **THE HYPEREDGES BLOCKED BY THE SLOTS OF A FAMILY: at most `25(n-1)(n-2)(k-1)·|F|`.** -/
theorem card_blocked_le {n k : ℕ} {F : Fam n k} (hok : OkF F) (hS : SlotFree F) :
    ((SlotsF F).biUnion (fun vp => auxDeg n k vp)).card
      ≤ 25 * ((n - 1) * ((n - 2) * (k - 1))) * F.card := by
  have h1 : ((SlotsF F).biUnion (fun vp => auxDeg n k vp)).card
      ≤ ∑ vp ∈ (SlotsF F), (auxDeg n k vp).card := Finset.card_biUnion_le
  have h2 : (∑ vp ∈ (SlotsF F), (auxDeg n k vp).card)
      ≤ ∑ vp ∈ (SlotsF F), 5 * ((n - 1) * ((n - 2) * (k - 1))) := by
    exact Finset.sum_le_sum fun vp _ => card_auxDeg_le vp
  have h3 : (∑ vp ∈ (SlotsF F), 5 * ((n - 1) * ((n - 2) * (k - 1))))
      = (SlotsF F).card * (5 * ((n - 1) * ((n - 2) * (k - 1)))) := by
    have hx := Finset.sum_const (s := SlotsF F) (5 * ((n - 1) * ((n - 2) * (k - 1))))
    simpa [nsmul_eq_mul] using hx
  have h4 : (SlotsF F).card = 5 * F.card := card_SlotsF hok hS
  calc ((SlotsF F).biUnion (fun vp => auxDeg n k vp)).card
      ≤ ∑ vp ∈ (SlotsF F), (auxDeg n k vp).card := h1
    _ ≤ ∑ vp ∈ (SlotsF F), 5 * ((n - 1) * ((n - 2) * (k - 1))) := h2
    _ = (SlotsF F).card * (5 * ((n - 1) * ((n - 2) * (k - 1)))) := h3
    _ = 25 * ((n - 1) * ((n - 2) * (k - 1))) * F.card := by rw [h4]; ring

/-- **THE CENSUS OF A CLOSED FAMILY: `|E(H)| ≤ 25(n-1)(n-2)(k-1)·|F| + |spoiled|`.**  Every hyperedge
of `H` is either blocked by one of the `5|F|` slots of `F` (round 40's count — a member of `F`
blocks itself), or is unblocked and hence spoiled, since the avoidance rule has finished.  Compare
`Hyper.card_auxF_le_of_maximal`, which is the same statement with no spoiled hyperedges at all. -/
theorem closed_census {n k : ℕ} {B : Finset (Finset (Verts n))} {F : Fam n k}
    (hok : OkF F) (hS : SlotFree F) (hC : AvoidClosed B F) :
    (auxF n k).card ≤ 25 * ((n - 1) * ((n - 2) * (k - 1))) * F.card + (spoilF (k := k) B).card := by
  have h1 : auxF n k
      ⊆ (SlotsF F).biUnion (fun vp => auxDeg n k vp) ∪ spoilF (k := k) B := by
    intro g hg
    simp only [Finset.mem_union]
    by_cases hgF : g ∈ F
    · refine Or.inl (Finset.mem_biUnion.mpr ⟨(cfgU g, cfgI g), ?_, ?_⟩)
      · exact Finset.mem_biUnion.mpr ⟨g, hgF,
          (mem_cfgSlots (g := g)).mpr (Or.inl ⟨rfl, Or.inl rfl⟩)⟩
      · exact (mem_auxDeg).mpr ⟨mem_auxF.mp hg,
          (mem_cfgSlots (g := g)).mpr (Or.inl ⟨rfl, Or.inl rfl⟩)⟩
    · by_cases hblk : ∃ vp : Verts n × Fin k, vp ∈ cfgSlots g ∧ vp ∈ SlotsF F
      · obtain ⟨vp, h1', h2'⟩ := hblk
        exact Or.inl (Finset.mem_biUnion.mpr ⟨vp, h2', (mem_auxDeg).mpr ⟨mem_auxF.mp hg, h1'⟩⟩)
      · exact Or.inr (hC g hg hgF (fun vp hvp hvF => hblk ⟨vp, hvp, hvF⟩))
  have h2 : (auxF n k).card
      ≤ ((SlotsF F).biUnion (fun vp => auxDeg n k vp) ∪ spoilF (k := k) B).card :=
    Finset.card_le_card h1
  have h3 : ((SlotsF F).biUnion (fun vp => auxDeg n k vp) ∪ spoilF (k := k) B).card
      ≤ ((SlotsF F).biUnion (fun vp => auxDeg n k vp)).card + (spoilF (k := k) B).card :=
    Finset.card_union_le _ _
  have h4 := card_blocked_le hok hS
  calc (auxF n k).card
      ≤ ((SlotsF F).biUnion (fun vp => auxDeg n k vp) ∪ spoilF (k := k) B).card := h2
    _ ≤ ((SlotsF F).biUnion (fun vp => auxDeg n k vp)).card + (spoilF (k := k) B).card := h3
    _ ≤ 25 * ((n - 1) * ((n - 2) * (k - 1))) * F.card + (spoilF (k := k) B).card := by omega

/-- **WHAT THE AVOIDANCE RULE DELIVERS — THE FIRST-MOMENT GUARANTEE OF §4:**
`n(n-1)(n-2)·k(k-1) ≤ 25(n-1)(n-2)(k-1)·|F| + 24·k(k-1)·|B|`, i.e. the census of `H` is paid for
by the members of `F` and by the bad four-sets, `24k(k-1)` hyperedges at a time. -/
theorem avoid_first_moment {n k : ℕ} {B : Finset (Finset (Verts n))} {F : Fam n k}
    (hB : ∀ S ∈ B, S.card = 4) (hok : OkF F) (hS : SlotFree F) (hC : AvoidClosed B F) :
    n * ((n - 1) * ((n - 2) * (k * (k - 1))))
      ≤ 25 * ((n - 1) * ((n - 2) * (k - 1))) * F.card + 24 * (k * (k - 1)) * B.card := by
  have h1 := closed_census hok hS hC
  have h2 := card_spoilF_le (k := k) hB
  have h3 := card_auxF n k
  have hh : (auxF n k).card ≤ 25 * ((n - 1) * ((n - 2) * (k - 1))) * F.card
      + 24 * (k * (k - 1)) * B.card := by omega
  omega

/-- **THE PRICE OF THE FOUR-SET CONDITIONS IN THE AVOIDANCE RULE: `25·|F| + n ≥ n·k` AS SOON AS
`24k·|B| ≤ n(n-1)(n-2)`.**  In words: a four-set condition which fails on `o(n²)` four-sets costs
the rule at most `n` slots out of `n·k`. -/
theorem avoid_certify {n k : ℕ} {B : Finset (Finset (Verts n))} {F : Fam n k}
    (hB : ∀ S ∈ B, S.card = 4) (hok : OkF F) (hS : SlotFree F) (hC : AvoidClosed B F)
    (h24 : 24 * k * B.card ≤ n * ((n - 1) * (n - 2))) (hn : 3 ≤ n) (hk : 2 ≤ k) :
    25 * F.card + n ≥ n * k := by
  have hpos2 : 0 < (n - 1) * (n - 2) := by
    have hx1 : 0 < n - 1 := by omega
    have hx2 : 0 < n - 2 := by omega
    exact Nat.mul_pos hx1 hx2
  have h1 := avoid_first_moment hB hok hS hC
  have h2 : n * ((n - 1) * ((n - 2) * (k * (k - 1))))
      = n * ((n - 1) * (n - 2)) * (k * (k - 1)) := by ring
  have h3 : 25 * ((n - 1) * ((n - 2) * (k - 1))) * F.card
      = 25 * (n - 1) * (n - 2) * F.card * (k - 1) := by ring
  have h4 : 24 * (k * (k - 1)) * B.card = (24 * k * B.card) * (k - 1) := by ring
  rw [h2] at h1
  rw [h3] at h1
  rw [h4] at h1
  have hpos : 0 < k - 1 := by omega
  have h6 : (n * ((n - 1) * (n - 2)) * k) * (k - 1)
      ≤ (25 * (n - 1) * (n - 2) * F.card + 24 * k * B.card) * (k - 1) := by
    convert h1 using 1 <;> ring
  have h7 : n * ((n - 1) * (n - 2)) * k
      ≤ 25 * (n - 1) * (n - 2) * F.card + 24 * k * B.card :=
    (Nat.mul_le_mul_right_iff hpos).mp h6
  have h7' : n * (n - 1) * (n - 2) * k
      ≤ 25 * (n - 1) * (n - 2) * F.card + 24 * k * B.card := by
    convert h7 using 1 <;> ring
  have h24' : 24 * k * B.card ≤ n * (n - 1) * (n - 2) := by
    convert h24 using 1 <;> ring
  have hstep : n * (n - 1) * (n - 2) * k
      = n * (n - 1) * (n - 2) * (k - 1) + n * (n - 1) * (n - 2) := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
    simp only [Nat.succ_sub_one, Nat.succ_eq_add_one]
    ring
  rw [hstep] at h7'
  have hc : n * (n - 1) * (n - 2) * (k - 1) + n * (n - 1) * (n - 2)
      ≤ 25 * (n - 1) * (n - 2) * F.card + n * (n - 1) * (n - 2) :=
    le_trans h7' (Nat.add_le_add_left h24' _)
  have h8 : n * (n - 1) * (n - 2) * (k - 1) ≤ 25 * (n - 1) * (n - 2) * F.card := by
    exact Nat.le_of_add_le_add_right hc
  have h8' : (n * (k - 1)) * ((n - 1) * (n - 2)) ≤ (25 * F.card) * ((n - 1) * (n - 2)) := by
    convert h8 using 1 <;> ring
  have h9 : n * (k - 1) ≤ 25 * F.card :=
    (Nat.mul_le_mul_right_iff hpos2).mp h8'
  have hstep2 : n * k = n * (k - 1) + n := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
    simp only [Nat.succ_sub_one, Nat.succ_eq_add_one]
    ring
  omega

/-- **THE PRICE OF THE AVOIDANCE RULE, IN REAL ARITHMETIC: at `δ ≤ 1/6`, the number
`n((5+δ)n-17)/150` — the best size the rule can certify when the budget `6k ≤ (5+δ)n − 11` holds —
is strictly below `n((7-δ)n-1)/42`, the size every valid first stage must have
(`Hyper.first_stage_size`).** -/
theorem avoid_gap (δ : ℝ) (hδ2 : δ ≤ 1 / 6) (n : ℕ) (hn : 1 ≤ n) :
    7 * ((5 + δ) * (n : ℝ) - 17) < 25 * ((7 - δ) * (n : ℝ) - 1) := by
  have h1 : (δ : ℝ) * (n : ℝ) ≤ (1 / 6) * (n : ℝ) :=
    mul_le_mul_of_nonneg_right hδ2 (by positivity)
  have h2 : (0 : ℝ) ≤ n := by positivity
  nlinarith

/-- **THE SAME, WITH THE CATALOG BUDGET SUBSTITUTED.**  If the budget `6k ≤ (5+δ)n − 11` holds at
`δ ≤ 1/6`, then the guarantee `n(k-1)/25` of `avoid_certify` is at most `n((5+δ)n-17)/150`, and that
is *strictly* below the size every valid first stage must have.  So **maximality-with-avoidance
cannot certify the budget, whatever the four-set conditions are**: the Rödl nibble is needed for
the matching itself, not for the local conditions. -/
theorem avoid_gap_of_budget {n k : ℕ} (δ : ℝ) (hδ2 : δ ≤ 1 / 6) (hn : 2 ≤ n) (hk : 2 ≤ k)
    (hbudget : 6 * (k : ℝ) ≤ (5 + δ) * (n : ℝ) - 11) :
    (n : ℝ) * ((5 + δ) * (n : ℝ) - 17) / 150 < (n : ℝ) * ((7 - δ) * (n : ℝ) - 1) / 42 := by
  have h1 : 6 * ((k : ℝ) - 1) ≤ (5 + δ) * (n : ℝ) - 17 := by linarith
  have h2 : (7 * ((5 + δ) * (n : ℝ) - 17)) * (n : ℝ)
      < (25 * ((7 - δ) * (n : ℝ) - 1)) * (n : ℝ) :=
    mul_lt_mul_of_pos_right (avoid_gap δ hδ2 n (by omega)) (by positivity)
  have h3 : (7 * ((5 + δ) * (n : ℝ) - 17)) * (n : ℝ) / 1050
      < (25 * ((7 - δ) * (n : ℝ) - 1)) * (n : ℝ) / 1050 :=
    div_lt_div_of_pos_right h2 (by norm_num)
  convert h3 using 1 <;> ring

/-- **THE PRICE, ASSEMBLED: a closed family of the avoidance rule, at `δ ≤ 1/6`, is certified to
have `25·|F| + n ≥ n·k` (as soon as its four-set condition is cheap), and the number
`n((5+δ)n-17)/150` is an upper bound on what the rule can certify, while `n((7−δ)n−1)/42` is a
lower bound on what it must have.** -/
theorem avoid_price {n k : ℕ} {B : Finset (Finset (Verts n))} {F : Fam n k} (δ : ℝ)
    (hB : ∀ S ∈ B, S.card = 4) (hok : OkF F) (hS : SlotFree F) (hC : AvoidClosed B F)
    (hδ2 : δ ≤ 1 / 6) (hn : 3 ≤ n) (hk : 2 ≤ k)
    (h24 : 24 * k * B.card ≤ n * ((n - 1) * (n - 2)))
    (hbudget : 6 * (k : ℝ) ≤ (5 + δ) * (n : ℝ) - 11) :
    25 * (F.card : ℝ) + (n : ℝ) ≥ (n : ℝ) * (k : ℝ)
      ∧ (n : ℝ) * ((5 + δ) * (n : ℝ) - 17) / 150 < (n : ℝ) * ((7 - δ) * (n : ℝ) - 1) / 42 := by
  have h1 := avoid_certify hB hok hS hC h24 hn hk
  exact ⟨(by exact_mod_cast h1), avoid_gap_of_budget δ hδ2 (by omega) hk hbudget⟩

/-! ### 4. The bridge back to the catalog condition -/

/-- **THE FOUR-SETS ON WHICH A COLOURING FAILS THE CATALOG CONDITION.** -/
noncomputable def badFours {n k : ℕ} (c : Col n k) : Finset (Finset (Verts n)) :=
  (fourSets n).filter (fun S => ¬ (5 ≤ (colorsOn c S).card))

theorem mem_badFours {n k : ℕ} {c : Col n k} {S : Finset (Verts n)} :
    S ∈ badFours c ↔ S.card = 4 ∧ ¬ (5 ≤ (colorsOn c S).card) := by
  simp [badFours]

/-- **A COLOURING SPANS AT LEAST FIVE COLOURS ON EVERY FOUR-SET EXACTLY WHEN IT HAS NO BAD
FOUR-SET.** -/
theorem badFours_eq_empty_iff {n k : ℕ} {c : Col n k} : badFours c = ∅ ↔ Admissible c := by
  constructor
  · intro h S hS
    by_contra hc
    have hmem : S ∈ badFours c := (mem_badFours.mpr ⟨hS, hc⟩)
    have : S ∈ (∅ : Finset (Finset (Verts n))) := by simpa [h] using hmem
    exact False.elim (by simpa using this)
  · intro h
    have hsub : badFours c ⊆ (∅ : Finset (Finset (Verts n))) := by
      intro S hmem
      obtain ⟨h1, h2⟩ := mem_badFours.mp hmem
      exact (h2 (h S h1)).elim
    have h1 : (badFours c).card = 0 := by
      have hx := Finset.card_le_card hsub
      rw [Finset.card_empty] at hx
      omega
    exact Finset.card_eq_zero.mp h1

/-- **AN ADMISSIBLE COLOURING SPOILS NOTHING: the four-set conditions of §4 are exactly the filter
of the avoidance rule.** -/
theorem spoilF_empty_of_admissible {n k : ℕ} {c : Col n k} (h : Admissible c) :
    spoilF (k := k) (badFours c) = ∅ := by
  have h1 : badFours c = ∅ := badFours_eq_empty_iff.mpr h
  have hsub : spoilF (k := k) (badFours c) ⊆ (∅ : Finset (Cfg n k)) := by
    intro g hg
    rw [mem_spoilF] at hg
    obtain ⟨hgA, S, hS4, hSB, hP⟩ := hg
    have hmem : S ∈ (∅ : Finset (Finset (Verts n))) := by simpa [h1] using hSB
    exact (by simpa using hmem : False).elim
  have h2 : (spoilF (k := k) (badFours c)).card = 0 := by
    have hx := Finset.card_le_card hsub
    rw [Finset.card_empty] at hx
    omega
  exact Finset.card_eq_zero.mp h2

end JSP140
