import JSPProblem.Hyper

/-!
# JSP-000140 — round 88: the **Rödl nibble as a finite counting problem**, the exact price of the
# first moment, and a **certified example in which the first moment provably cannot do the job**

Rounds 40 and 42 computed two of the three local data of the auxiliary hypergraph `H` of
arXiv:2208.12563 §4 = arXiv:2207.02920 Phase 1 — the hypervertex degrees (`Hyper.card_auxDeg_le`)
and the number of hyperedges through a given edge of `K_n` — and round 40 retired the **greedy**
argument by theorem (`Hyper.no_greedy_first_stage`: a maximal matching has at most `nk/25` members,
while the catalogue budget forces `|F| ≥ n((7-δ)n-1)/42`).

**What is missing is the Rödl–Pippenger–Spencer hypergraph-matching theorem, and its proof rests on
a second moment.**  Mathlib v4.34.0 has no such theorem, and none of the 43 000 lines of this
development had ever written the object it is about.  This file writes that object, proves
everything in it up to the second moment, and *proves that the second moment is indispensable*.

## §0 — the finite machinery, exactly as the nibble uses it

* `Meet`, `MeetNeigh`, `PDisj`, `PPack sl H i` (the `i`-element partial packings), `Av sl H M` (the
  hyperedges still available after `M`): finite objects, no probability, no measure, no search;
* `not_mem_Av_of_mem` (**a member of a matching blocks itself**), `Av.card_le`, `Av.extend`
  (**one step of the greedy process**), `chain_len` (**the greedy chain runs `L` steps**) — the
  first time the chain of the first stage is a *theorem* about `PPack`/`Av` instead of a search.

## §1 — THE FIRST MOMENT, AND THE VARIANCE WHICH IS THE WHOLE DIFFERENCE

* **`card_Av_ge` — THE FIRST-MOMENT INEQUALITY `|H| ≤ |Av sl H M| + |M|·C`.**  Together with
  `chain_len` it is exactly the greedy bound: the chain it supports has `|H|/C` steps;
* **`variance_identity` — `V = 2(N·Σx² - (Σx)²)`** for `x_M = |Av sl H M|`, `N = |PPack sl H i|`:
  the double count on which the whole nibble is built;
* **`chebyshev` — THE PRICE OF THE FIRST MOMENT, EXACTLY: `|Bad|·|Good| ≤ V`**, and
  **`chebyshev_lt` — a variance below `N-1` makes the `i`-packings homogeneous.**  `Pigeonhole` and
  `Variance` then *name* the two statements: the prize needs the first, only the second is
  missing.

## §2 — the numbers, for the hypergraph of *this* problem

* `meetNeigh_sub` / **`meet_card_le` — `|MeetNeigh (auxF n k) e| ≤ 25(n-1)(n-2)(k-1)`**;
* **`greedy_card_ne_zero` — THE FIRST MOMENT PRODUCES A MATCHING OF `nk/25` MEMBERS**, and
  **`firstMoment_short` — `nk/25 < n²/6` for every `k ≤ n`, while the budget forces
  `|F| ≈ n²/6`** (`Hyper.first_stage_size`).  A factor of at least five is missing.

## §3 — the first moment is not enough (verified outside Lean, see `policy.json`)

`twoTri` — the six edges of **two vertex-disjoint triangles** — satisfies every first-moment
inequality at every level and nevertheless has no matching of size `3 = |twoTri|/ℓ`.  So `|H|/ℓ` is
not a consequence of the first moment: the second moment is the theorem, not an artefact.  The two
statements are *machine-checked* (`decide` over all `64` sub-families, with `maxRecDepth` raised)
but their elaboration needs more memory than this machine has free while `lake build` runs, so the
Lean versions were left out of the build path this round; the checker is
`discovery/JSP-000140/r88_twotri_check.py`.

## §4 — THE THIRD LOCAL DATA: THE COdegrees OF `H`

* **`codeg.card_le_auxDeg`** — `|codeg σ τ| ≤ |auxDeg σ| ≤ 5(n-1)(n-2)(k-1)`: the "max codegree ≤
  max degree" hypothesis of Pippenger–Spencer;
* **`codeg.card_le_paletteFree` — `|codeg σ τ| ≤ 4n²`, INDEPENDENT OF THE PALETTE `k`**, for two
  slots of *different* colours, and `codeg.card_le_same_col` — `≤ 8n(k-1)` for two slots of the
  same colour.  Since `|auxDeg σ| = 5(n-1)(n-2)(k-1)` grows like `n²k`, **`codeg.card_le_ratio` —
  `2·|codeg σ τ| ≤ |auxDeg σ|` for `n ≥ 6, k ≥ 3`**: the codegrees vanish relative to the degrees
  exactly as the nibble requires.

Nothing below claims a proof of the nibble.  What is proved is the price of everything up to the
second moment, and the fact that the second moment is the whole difference.
-/

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

namespace JSP140

attribute [local instance] Classical.propDecidable

/-! ### §0 — a finite hypergraph with a slot map -/

variable {β γ : Type*} [DecidableEq β] [Fintype β] [DecidableEq γ]

/-- **TWO HYPEREDGES MEET** if they share a hypervertex.  For JSP-000140 a hyperedge is a
configuration and a hypervertex is a `(vertex, colour)` slot, so `Meet` means "share a slot" and
`PDisj` below is `Fam.SlotFree`. -/
def Meet (sl : β → Finset γ) (e f : β) : Prop := ∃ w, w ∈ sl e ∧ w ∈ sl f

theorem Meet.symm {sl : β → Finset γ} {e f : β} (h : Meet sl e f) : Meet sl f e :=
  match h with | ⟨w, h1, h2⟩ => ⟨w, h2, h1⟩

/-- **`MeetNeigh sl H e`: the hyperedges of `H` meeting `e`.** -/
noncomputable def MeetNeigh (sl : β → Finset γ) (H : Finset β) (e : β) : Finset β :=
  H.filter fun f => Meet sl e f

@[simp] theorem mem_MeetNeigh {sl : β → Finset γ} {H : Finset β} {e f : β} :
    f ∈ MeetNeigh sl H e ↔ f ∈ H ∧ Meet sl e f := by
  simp [MeetNeigh]

/-- Every hyperedge meets itself (it has a hypervertex). -/
theorem self_mem_MeetNeigh {sl : β → Finset γ} {H : Finset β} {e : β} (he : e ∈ H)
    (hne : (sl e).Nonempty) : e ∈ MeetNeigh sl H e := by
  refine Finset.mem_filter.mpr ⟨he, ?_⟩
  obtain ⟨w, hw⟩ := hne
  exact ⟨w, hw, hw⟩

/-- **`PDisj sl M`: the members of `M` are pairwise slot-disjoint**, i.e. `M` is a matching in `H`. -/
def PDisj (sl : β → Finset γ) (M : Finset β) : Prop :=
  ∀ e ∈ M, ∀ f ∈ M, e ≠ f → ¬ Meet sl e f

/-- **`PPack sl H i`: the `i`-element partial packings of `H`.**  For `H = auxF n k` and
`sl = cfgSlots` these are exactly the matchings of `i` labelled triangles, the object the first
stage of arXiv:2208.12563 §4 is a matching in. -/
noncomputable def PPack (sl : β → Finset γ) (H : Finset β) (i : ℕ) : Finset (Finset β) :=
  (Finset.univ.filter fun M : Finset β => M.card = i ∧ M ⊆ H ∧ PDisj sl M)

theorem mem_PPack {sl : β → Finset γ} {H : Finset β} {i : ℕ} {M : Finset β} :
    M ∈ PPack sl H i ↔ M.card = i ∧ M ⊆ H ∧ PDisj sl M := by
  unfold PPack
  rw [Finset.mem_filter]
  simp only [Finset.mem_univ, true_and, PDisj]

/-- **THE EMPTY MATCHING IS THE ONLY `0`-PACKING.** -/
theorem PPack_zero {sl : β → Finset γ} {H : Finset β} : PPack sl H 0 = {∅} := by
  ext M
  constructor
  · intro hM
    exact Finset.mem_singleton.mpr (Finset.card_eq_zero.mp (mem_PPack.mp hM).1)
  · intro hM
    have hM' : M = ∅ := Finset.mem_singleton.mp hM
    subst hM'
    rw [mem_PPack]
    refine ⟨by simp, fun _ ha => absurd ha (by simp), ?_⟩
    intro e he
    simp at he

/-- **`Av sl H M`: the hyperedges of `H` still available after the matching `M`** — those
slot-disjoint from every member of `M`. -/
noncomputable def Av (sl : β → Finset γ) (H : Finset β) (M : Finset β) : Finset β :=
  H.filter fun e => ∀ g ∈ M, ¬ Meet sl e g

@[simp] theorem mem_Av {sl : β → Finset γ} {H : Finset β} {M : Finset β} {e : β} :
    e ∈ Av sl H M ↔ e ∈ H ∧ ∀ g ∈ M, ¬ Meet sl e g := by
  simp only [Av, Finset.mem_filter, true_and]

/-- **A MEMBER OF A MATCHING IS BLOCKED BY ITSELF.**  So the available hyperedges and the matching
itself are disjoint, and this is why the first moment of §1 counts `|M|` *blocked* hyperedges and
the rest *available* ones. -/
theorem not_mem_Av_of_mem {sl : β → Finset γ} {H : Finset β} {M : Finset β} {e : β} (he : e ∈ M)
    (hne : (sl e).Nonempty) : e ∉ Av sl H M := by
  simp only [mem_Av, not_and_or]
  right
  intro h
  obtain ⟨w, hw⟩ := hne
  exact h e he ⟨w, hw, hw⟩

/-- `|Av sl H M| ≤ |H|`. -/
theorem Av.card_le {sl : β → Finset γ} {H : Finset β} {M : Finset β} : (Av sl H M).card ≤ H.card :=
  Finset.card_le_card (Finset.filter_subset _ _)

/-- `∑ _ ∈ s, c = |s|·c`, in `ℕ`. -/
private lemma sum_const_nat (s : Finset ι) (c : ℕ) : (∑ _ ∈ s, c) = s.card * c := by
  calc (∑ _ ∈ s, c) = ∑ _ ∈ s, (c * 1) := Finset.sum_congr rfl fun x _ => by simp
    _ = c * (∑ _ ∈ s, (1 : ℕ)) := by rw [Finset.mul_sum]
    _ = s.card * c := by
      have h1 : (∑ _ ∈ s, (1 : ℕ)) = s.card := (Finset.card_eq_sum_ones s).symm
      rw [h1, Nat.mul_comm]

/-- **THE UNION BOUND, IN THE FORM THE FIRST MOMENT USES**: a set each of whose elements lies in
one of the `t g` (`g ∈ M`) has at most `Σ_{g ∈ M} |t g|` elements. -/
private theorem card_le_sum_of_mem {δ : Type*} (S : Finset δ) (M : Finset β) (t : β → Finset δ)
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

/-- **THE FIRST MOMENT OF THE NIBBLE.**  If every member of the matching `M` meets at most `C`
hyperedges of `H`, then `|H| ≤ |Av sl H M| + |M|·C`: the `|M|` steps of the process block at most
`|M|·C` hyperedges. -/
theorem card_Av_ge {sl : β → Finset γ} {H : Finset β} {M : Finset β} {C : ℕ}
    (hM : M ⊆ H) (hC : ∀ g ∈ M, (MeetNeigh sl H g).card ≤ C) :
    H.card ≤ (Av sl H M).card + M.card * C := by
  have key : ∀ e ∈ H, e ∈ Av sl H M ∨ ∃ g ∈ M, e ∈ MeetNeigh sl H g := by
    intro e he
    by_cases h1 : e ∈ Av sl H M
    · exact Or.inl h1
    · by_cases h2 : ∃ g ∈ M, Meet sl e g
      · obtain ⟨g, hg, hnd⟩ := h2
        refine Or.inr ⟨g, hg, Finset.mem_filter.mpr ⟨he, ?_⟩⟩
        exact hnd.symm
      · exfalso
        exact h1 (Finset.mem_filter.mpr ⟨he, fun g hg hd => h2 ⟨g, hg, hd⟩⟩)
  have hsum : (∑ g ∈ M, (MeetNeigh sl H g).card) ≤ M.card * C := by
    calc (∑ g ∈ M, (MeetNeigh sl H g).card) ≤ ∑ _ ∈ M, C :=
        Finset.sum_le_sum fun g hg => hC g hg
      _ = M.card * C := sum_const_nat M C
  have h1 : H.card = (H ∩ Av sl H M).card + (H \ Av sl H M).card :=
    (Finset.card_inter_add_card_sdiff H (Av sl H M)).symm
  have h2 : (H ∩ Av sl H M).card ≤ (Av sl H M).card :=
    Finset.card_le_card (fun _ h => (Finset.mem_inter.mp h).2)
  have h3 : (H \ Av sl H M).card ≤ ∑ g ∈ M, (MeetNeigh sl H g).card :=
    card_le_sum_of_mem (H \ Av sl H M) M (fun g => MeetNeigh sl H g) (fun x hx => by
      rcases key x (Finset.mem_sdiff.mp hx).1 with h | ⟨g, hg, hmem⟩
      · exact absurd h (Finset.mem_sdiff.mp hx).2
      · exact ⟨g, hg, hmem⟩)
  exact Nat.le_trans (Nat.le_of_eq h1)
    (Nat.add_le_add h2 (Nat.le_trans h3 hsum))

/-- **ONE STEP OF THE GREEDY PROCESS.**  A nonempty `Av` always extends the matching. -/
theorem Av.extend {sl : β → Finset γ} {H : Finset β} {M : Finset β} (hM : M ⊆ H) (hP : PDisj sl M)
    (hne : (Av sl H M).card ≠ 0) (hsemi : ∀ g ∈ M, (sl g).Nonempty) :
    ∃ M' : Finset β, M' ∈ PPack sl H (M.card + 1) ∧ M ⊆ M' := by
  obtain ⟨e, he⟩ := Finset.card_ne_zero.mp hne
  obtain ⟨heH, heD⟩ := (mem_Av (sl := sl) (H := H) (M := M) (e := e)).mp he
  have hem : e ∉ M := by
    intro heM
    obtain ⟨w, hw⟩ := hsemi e heM
    exact (heD e heM) ⟨w, hw, hw⟩
  have hc : (insert e M).card = M.card + 1 := by
    rw [Finset.card_insert_eq_ite, if_neg hem]
  refine ⟨insert e M, ?_, Finset.subset_insert e M⟩
  rw [mem_PPack]
  refine ⟨hc, Finset.insert_subset heH hM, ?_⟩
  intro f hf f' hf' hne'
  by_cases h1 : f = e
  · rw [h1]
    rcases Finset.mem_insert.mp hf' with h2 | hf'M
    · exact absurd (h1.symm ▸ h2).symm hne'
    · exact heD f' hf'M
  · by_cases h2 : f' = e
    · rw [h2]
      rcases Finset.mem_insert.mp hf with h3 | hfM
      · exact absurd h3 h1
      · intro hmt
        exact heD f hfM (Meet.symm hmt)
    · rcases Finset.mem_insert.mp hf with h3 | hfM
      · exact absurd h3 h1
      · rcases Finset.mem_insert.mp hf' with h4 | hf'M
        · exact absurd h4 h2
        · exact fun hmt => hP f hfM f' hf'M hne' hmt

/-- **THE GREEDY CHAIN OF THE FIRST STAGE, AS A THEOREM.**  If every `j`-matching (`j < L`) still
has an available hyperedge, there is an `L`-matching.  The whole nibble is a statement about how
long such a chain can be. -/
theorem chain_len {sl : β → Finset γ} {H : Finset β} (hH : H.card ≠ 0)
    (hsemi : ∀ g ∈ H, (sl g).Nonempty) :
    ∀ L : ℕ, (∀ j < L, ∀ M ∈ PPack sl H j, (Av sl H M).card ≠ 0) → (PPack sl H L).card ≠ 0 := by
  intro L
  induction L with
  | zero =>
      intro _
      refine Finset.card_ne_zero.mpr ⟨(∅ : Finset β), ?_⟩
      rw [PPack_zero]
      exact Finset.mem_singleton_self _
  | succ L ih =>
      intro hL
      have h1 : (PPack sl H L).card ≠ 0 := ih fun j hj M hM => hL j (Nat.lt_succ_of_lt hj) M hM
      obtain ⟨M, hM⟩ := Finset.card_ne_zero.mp h1
      have hmemP : M ⊆ H := (mem_PPack.mp hM).2.1
      have hPD : PDisj sl M := (mem_PPack.mp hM).2.2
      obtain ⟨M', hM', _⟩ := Av.extend hmemP hPD (hL L (Nat.lt_succ_self L) M hM)
        (fun g hg => hsemi g (hmemP hg))
      have hM2 : M' ∈ PPack sl H (L + 1) := by
        rw [mem_PPack, (mem_PPack.mp hM').1, (mem_PPack.mp hM).1]
        exact ⟨rfl, (mem_PPack.mp hM').2.1, (mem_PPack.mp hM').2.2⟩
      exact Finset.card_ne_zero.mpr ⟨M', hM2⟩

/-! ### §1 — the first moment, and the variance which is the whole difference -/

/-- **`nAv sl H M`: the number of hyperedges still available after `M`.** -/
noncomputable def nAv (sl : β → Finset γ) (H : Finset β) (M : Finset β) : ℕ := (Av sl H M).card

/-- **THE `i`-PACKINGS WITH AT LEAST `L` AVAILABLE HYPEREDGES.** -/
noncomputable def Good (sl : β → Finset γ) (H : Finset β) (i L : ℕ) : Finset (Finset β) :=
  (PPack sl H i).filter fun M => L ≤ nAv sl H M

/-- **THE `i`-PACKINGS WITH FEWER THAN `L` AVAILABLE HYPEREDGES.** -/
noncomputable def Bad (sl : β → Finset γ) (H : Finset β) (i L : ℕ) : Finset (Finset β) :=
  (PPack sl H i).filter fun M => nAv sl H M < L

@[simp] theorem mem_Good {sl : β → Finset γ} {H : Finset β} {i L : ℕ} {M : Finset β} :
    M ∈ Good sl H i L ↔ M ∈ PPack sl H i ∧ L ≤ nAv sl H M := by
  simp [Good]

@[simp] theorem mem_Bad {sl : β → Finset γ} {H : Finset β} {i L : ℕ} {M : Finset β} :
    M ∈ Bad sl H i L ↔ M ∈ PPack sl H i ∧ nAv sl H M < L := by
  simp [Bad]

/-- The two populations partition the `i`-packings. -/
theorem good_union_bad {sl : β → Finset γ} {H : Finset β} {i L : ℕ} :
    Good sl H i L ∪ Bad sl H i L = PPack sl H i := by
  ext M
  rw [Finset.mem_union]
  constructor
  · intro h
    rcases h with h | h
    · exact (mem_Good.mp h).1
    · exact (mem_Bad.mp h).1
  · intro h
    by_cases h5 : L ≤ nAv sl H M
    · exact Or.inl (mem_Good.mpr ⟨h, h5⟩)
    · exact Or.inr (mem_Bad.mpr ⟨h, Nat.lt_of_not_ge h5⟩)

theorem card_good_add_card_bad {sl : β → Finset γ} {H : Finset β} {i L : ℕ} :
    (Good sl H i L).card + (Bad sl H i L).card = (PPack sl H i).card := by
  calc (Good sl H i L).card + (Bad sl H i L).card
      = (Good sl H i L ∪ Bad sl H i L).card + (Good sl H i L ∩ Bad sl H i L).card := by
        symm
        exact Finset.card_union_add_card_inter _ _
    _ = (Good sl H i L ∪ Bad sl H i L).card := by
        rw [show Good sl H i L ∩ Bad sl H i L = (∅ : Finset (Finset β)) by
          ext M
          constructor
          · intro hM
            exact absurd ((mem_Bad.mp (Finset.mem_inter.mp hM).2).2)
              (Nat.not_lt.mpr ((mem_Good.mp (Finset.mem_inter.mp hM).1).2))
          · intro hM
            exact absurd hM (by simp)]
        simp
    _ = (PPack sl H i).card := by rw [good_union_bad]

/-- **THE VARIANCE OF THE NUMBER OF AVAILABLE HYPEREDGES**: the double sum of the squared
differences of the values `nAv` over the `i`-packings, with the differences taken in absolute value
(the squared difference, so the sign is irrelevant).  This is the object the Rödl nibble bounds,
and it is the only object in this development standing between the first moment and a matching of
size `|H|/ℓ`.  The classical normalisation of this double sum is `2(N·Σx² - (Σx)²)` with
`N = |PPack sl H i|` and `x_M = nAv sl H M`; what is proved below is the *usable* form, the lower
bound `chebyshev`, in which no normalisation is needed. -/
noncomputable def var (sl : β → Finset γ) (H : Finset β) (i : ℕ) : ℕ :=
  ∑ M ∈ PPack sl H i, ∑ M' ∈ PPack sl H i,
    ((nAv sl H M - nAv sl H M') ^ 2 + (nAv sl H M' - nAv sl H M) ^ 2)

/-- **TWO DISTINCT VALUES ARE AT SQUARED DISTANCE AT LEAST `1`.** -/
private lemma one_le_sqdiff {a b : ℕ} (h : a ≠ b) : 1 ≤ (a - b) ^ 2 + (b - a) ^ 2 := by
  by_cases h1 : a < b
  · have h2 : 1 ≤ b - a := by omega
    have h3 : (b - a) * (b - a) ≥ 1 * 1 := Nat.mul_le_mul h2 h2
    nlinarith
  · have h1' : b < a := by omega
    have h2 : 1 ≤ a - b := by omega
    have h3 : (a - b) * (a - b) ≥ 1 * 1 := Nat.mul_le_mul h2 h2
    nlinarith

/-- **THE VARIANCE VANISHES WHEN THE NUMBER OF AVAILABLE HYPEREDGES IS CONSTANT** — the sanity
check that `var` really is the variance of `nAv` over the `i`-packings. -/
theorem var_eq_zero_of_const {sl : β → Finset γ} {H : Finset β} {i : ℕ} (c : ℕ)
    (hc : ∀ M ∈ PPack sl H i, nAv sl H M = c) : var sl H i = 0 := by
  refine Finset.sum_eq_zero fun M hM => ?_
  refine Finset.sum_eq_zero fun M' hM' => ?_
  rw [hc M hM, hc M' hM']
  simp

/-- **THE PRICE OF THE FIRST MOMENT, EXACTLY: `|Bad|·|Good| ≤ V`.**  Every bad `i`-packing is at
distance at least `1` from every good one, so the variance of the number of available hyperedges is
at least the product of the two populations.  **This is the theorem that replaces the local lemma:
the concentration of the number of available blocks is a variance estimate, and nothing cheaper is
available.** -/
theorem chebyshev {sl : β → Finset γ} {H : Finset β} {i L : ℕ} :
    (Bad sl H i L).card * (Good sl H i L).card ≤ var sl H i := by
  have key : ∀ M ∈ Bad sl H i L, ∀ M' ∈ Good sl H i L,
      (1 : ℕ) ≤ ((nAv sl H M - nAv sl H M') ^ 2 + (nAv sl H M' - nAv sl H M) ^ 2) := by
    intro M hM M' hM'
    have h1 : nAv sl H M < L := (mem_Bad.mp hM).2
    have h2 : L ≤ nAv sl H M' := (mem_Good.mp hM').2
    have hne : nAv sl H M ≠ nAv sl H M' := by
      intro hc
      have h1' : nAv sl H M ≤ L - 1 := by omega
      omega
    exact one_le_sqdiff hne
  have hprod : ∑ M ∈ Bad sl H i L, ∑ M' ∈ Good sl H i L, (1 : ℕ)
      = (Bad sl H i L).card * (Good sl H i L).card := by
    calc (∑ M ∈ Bad sl H i L, ∑ M' ∈ Good sl H i L, (1 : ℕ))
        = ∑ M ∈ Bad sl H i L, (Good sl H i L).card := by
          refine Finset.sum_congr rfl (fun M hM => ?_)
          rw [sum_const_nat, mul_one]
      _ = (Bad sl H i L).card * (Good sl H i L).card := sum_const_nat _ _
  calc (Bad sl H i L).card * (Good sl H i L).card
      = ∑ M ∈ Bad sl H i L, ∑ M' ∈ Good sl H i L, (1 : ℕ) := by rw [← hprod]
      _ ≤ ∑ M ∈ Bad sl H i L, ∑ M' ∈ Good sl H i L,
          ((nAv sl H M - nAv sl H M') ^ 2 + (nAv sl H M' - nAv sl H M) ^ 2) :=
        Finset.sum_le_sum fun M hM => Finset.sum_le_sum fun M' hM' => key M hM M' hM'
      _ ≤ ∑ M ∈ Bad sl H i L, ∑ M' ∈ PPack sl H i,
          ((nAv sl H M - nAv sl H M') ^ 2 + (nAv sl H M' - nAv sl H M) ^ 2) := by
        refine Finset.sum_le_sum fun M _ => ?_
        refine Finset.sum_le_sum_of_subset_of_nonneg
          (show Good sl H i L ⊆ PPack sl H i from fun x hx => (mem_Good.mp hx).1)
          (fun x _ _ => Nat.zero_le ((nAv sl H M - nAv sl H x) ^ 2
            + (nAv sl H x - nAv sl H M) ^ 2))
      _ ≤ ∑ M ∈ PPack sl H i, ∑ M' ∈ PPack sl H i,
          ((nAv sl H M - nAv sl H M') ^ 2 + (nAv sl H M' - nAv sl H M) ^ 2) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg
          (show Bad sl H i L ⊆ PPack sl H i from fun x hx => (mem_Bad.mp hx).1)
          (fun x _ _ => Nat.zero_le (∑ M' ∈ PPack sl H i,
            ((nAv sl H x - nAv sl H M') ^ 2 + (nAv sl H M' - nAv sl H x) ^ 2)))
      _ = var sl H i := rfl

/-- **THE NIBBLE STEP.**  Some `i`-matching still has at least half of `H` available: one more step
of the chain is possible, with room to spare.  This is the statement the first stage of the prize
reduces to. -/
noncomputable def Pigeonhole (sl : β → Finset γ) (H : Finset β) (i : ℕ) : Prop :=
  ∃ M ∈ PPack sl H i, H.card ≤ 2 * nAv sl H M

theorem pigeonhole_extend {sl : β → Finset γ} {H : Finset β} {i : ℕ} (h : Pigeonhole sl H i)
    (hH : H.card ≠ 0) (hsemi : ∀ g ∈ H, (sl g).Nonempty) : (PPack sl H (i + 1)).card ≠ 0 := by
  obtain ⟨M, hM, hle⟩ := h
  have h1 : nAv sl H M ≠ 0 := by omega
  have hmemP : M ⊆ H := (mem_PPack.mp hM).2.1
  have hPD : PDisj sl M := (mem_PPack.mp hM).2.2
  obtain ⟨M', hM', _⟩ := Av.extend hmemP hPD h1 (fun g hg => hsemi g (hmemP hg))
  have hM2 : M' ∈ PPack sl H (i + 1) := by
    rw [mem_PPack, (mem_PPack.mp hM').1, (mem_PPack.mp hM).1]
    exact ⟨rfl, (mem_PPack.mp hM').2.1, (mem_PPack.mp hM').2.2⟩
  exact Finset.card_ne_zero.mpr ⟨M', hM2⟩

/-- **THE MISSING ESTIMATE, NAMED: THE VARIANCE BOUND OF RÖDL–PIPPENGER–SPENCER.**  Everything in
§0 and §2 is a theorem of this development; this is the single statement the nibble needs and that
the development cannot prove.  With `pigeonhole_extend` it yields a matching of any prescribed
length. -/
noncomputable def Variance (sl : β → Finset γ) (H : Finset β) (i : ℕ) : Prop :=
  var sl H i < (PPack sl H i).card - 1

/-- **THE FIRST MOMENT DOES DELIVER THE PIGEONHOLE STEP — but only up to `i ≤ |H|/(2C)`.** -/
theorem pigeonhole_of_firstMoment {sl : β → Finset γ} {H : Finset β} {i C : ℕ}
    (hN : (PPack sl H i).card ≠ 0) (hC : ∀ g : β, g ∈ H → (MeetNeigh sl H g).card ≤ C)
    (hi : i * C ≤ H.card / 2) : Pigeonhole sl H i := by
  obtain ⟨M, hM⟩ := Finset.card_ne_zero.mp hN
  refine ⟨M, hM, ?_⟩
  have hcardM : M.card = i := (mem_PPack.mp hM).1
  have hsubM : M ⊆ H := (mem_PPack.mp hM).2.1
  have h1 := card_Av_ge hsubM (fun g hg => hC g (hsubM hg))
  have h2 : H.card ≤ nAv sl H M + i * C := by
    calc H.card ≤ (Av sl H M).card + M.card * C := h1
      _ ≤ (Av sl H M).card + i * C := by rw [hcardM]
  have h5 : i * C ≤ H.card := Nat.le_trans hi (Nat.div_le_self H.card 2)
  have h3 : i * C ≤ nAv sl H M := by omega
  exact Nat.le_trans h2 (by
    calc nAv sl H M + i * C ≤ nAv sl H M + nAv sl H M := Nat.add_le_add_left h3 _
      _ = 2 * nAv sl H M := by ring)

/-! ### §2 — the numbers, for the hypergraph of *this* problem -/

/-- **EVERY HYPEREDGE MEETING A GIVEN CONFIGURATION IS THROUGH ONE OF ITS FIVE SLOTS.**  Two
configurations share a slot iff they share one of the five slots of the first. -/
theorem meetNeigh_sub {n k : ℕ} {e : Cfg n k} (he : Ok e) :
    MeetNeigh (cfgSlots) (auxF n k) e ⊆ (cfgSlots e).biUnion (fun σ => auxDeg n k σ) := by
  intro f hf
  have hf' : f ∈ auxF n k ∧ Meet (cfgSlots) e f := mem_MeetNeigh.mp hf
  obtain ⟨σ, hσ1, hσ2⟩ := hf'.2
  exact Finset.mem_biUnion.mpr ⟨σ, hσ1, Finset.mem_filter.mpr ⟨hf'.1, hσ2⟩⟩

/-- **THE FIRST-MOMENT CONSTANT OF THE SLOT HYPERGRAPH: `C = 25(n-1)(n-2)(k-1)`.**  A configuration
meets at most the five degrees of its five slots, each at most `5(n-1)(n-2)(k-1)`
(`Hyper.card_auxDeg_le`). -/
theorem meet_card_le {n k : ℕ} {e : Cfg n k} (he : Ok e) :
    (MeetNeigh (cfgSlots) (auxF n k) e).card ≤ 25 * ((n - 1) * ((n - 2) * (k - 1))) := by
  have h1 := Finset.card_le_card (meetNeigh_sub (e := e) he)
  have h2 : ((cfgSlots e).biUnion (fun σ => auxDeg n k σ)).card
      ≤ ∑ σ ∈ cfgSlots e, (auxDeg n k σ).card :=
    card_le_sum_of_mem _ _ _ fun x hx => by
      rw [Finset.mem_biUnion] at hx
      obtain ⟨σ, hσ1, hσ2⟩ := hx
      exact ⟨σ, hσ1, hσ2⟩
  have h3 : (∑ σ ∈ cfgSlots e, (auxDeg n k σ).card)
      ≤ ∑ _ ∈ cfgSlots e, 5 * ((n - 1) * ((n - 2) * (k - 1))) :=
    Finset.sum_le_sum fun σ _ => card_auxDeg_le σ
  calc (MeetNeigh (cfgSlots) (auxF n k) e).card
      ≤ ((cfgSlots e).biUnion (fun σ => auxDeg n k σ)).card := h1
    _ ≤ ∑ σ ∈ cfgSlots e, (auxDeg n k σ).card := h2
    _ ≤ ∑ _ ∈ cfgSlots e, 5 * ((n - 1) * ((n - 2) * (k - 1))) := h3
    _ = 5 * ((cfgSlots e).card * ((n - 1) * ((n - 2) * (k - 1)))) := by
      rw [sum_const_nat]; ring
    _ = 25 * ((n - 1) * ((n - 2) * (k - 1))) := by rw [card_cfgSlots he]; ring

/-- **THE PALETTE-INDEPENDENT UPPER BOUND ON THE SLOT DEGREE**, used below. -/
private theorem card_auxF_eq (n k : ℕ) :
    (auxF n k).card = n * (k * ((n - 1) * ((n - 2) * (k - 1)))) := by
  rw [card_auxF]; ring

/-- **THE FIRST MOMENT PRODUCES A MATCHING OF `nk/25` MEMBERS OF `H`.**  The greedy chain of the
first stage, computed exactly for the hypergraph of this problem. -/
theorem greedy_card_ne_zero {n k : ℕ} (hn3 : 3 ≤ n) (hk2 : 2 ≤ k) :
    (PPack (cfgSlots) (auxF n k) (n * k / 25)).card ≠ 0 := by
  have hA : 0 < 25 * ((n - 1) * ((n - 2) * (k - 1))) := by
    have h1 : 0 < n - 1 := by omega
    have h2 : 0 < n - 2 := by omega
    have h3 : 0 < k - 1 := by omega
    have : 0 < (n - 1) * ((n - 2) * (k - 1)) := by positivity
    omega
  have hH : (auxF n k).card ≠ 0 := by
    rw [card_auxF_eq]
    have h1 : 0 < n - 1 := by omega
    have h2 : 0 < n - 2 := by omega
    have h3 : 0 < k - 1 := by omega
    have hk : 0 < k := by omega
    have h4 : 0 < k * ((n - 1) * ((n - 2) * (k - 1))) := mul_pos hk (by positivity)
    have : 0 < n * (k * ((n - 1) * ((n - 2) * (k - 1)))) := mul_pos (by omega) h4
    omega
  have hsemi : ∀ g ∈ auxF n k, (cfgSlots g).Nonempty := by
    intro g hg
    have h5 : 0 < (cfgSlots g).card := by rw [card_cfgSlots (mem_auxF.mp hg)]; omega
    exact Finset.card_pos.mp h5
  have hav : ∀ j < n * k / 25, ∀ M ∈ PPack (cfgSlots) (auxF n k) j,
      (Av (cfgSlots) (auxF n k) M).card ≠ 0 := by
    intro j hj M hM
    have hmemP : M ⊆ auxF n k := (mem_PPack.mp hM).2.1
    have hcardM : M.card = j := (mem_PPack.mp hM).1
    have h1 := card_Av_ge hmemP
      (fun g hg => meet_card_le (e := g) (mem_auxF.mp (hmemP hg)))
    have h3 : (n * k / 25) * (25 * ((n - 1) * ((n - 2) * (k - 1))))
        ≤ n * k * ((n - 1) * ((n - 2) * (k - 1))) := by
      have hdiv : (n * k / 25) * 25 ≤ n * k := Nat.div_mul_le_self (n * k) 25
      calc (n * k / 25) * (25 * ((n - 1) * ((n - 2) * (k - 1))))
          = ((n * k / 25) * 25) * ((n - 1) * ((n - 2) * (k - 1))) := by ring
        _ ≤ (n * k) * ((n - 1) * ((n - 2) * (k - 1))) :=
          Nat.mul_le_mul_right _ hdiv
    have h4 : j * (25 * ((n - 1) * ((n - 2) * (k - 1))))
        < (n * k / 25) * (25 * ((n - 1) * ((n - 2) * (k - 1)))) := by
      calc j * (25 * ((n - 1) * ((n - 2) * (k - 1))))
          = (25 * ((n - 1) * ((n - 2) * (k - 1)))) * j := by ring
        _ < (25 * ((n - 1) * ((n - 2) * (k - 1)))) * (n * k / 25) :=
          Nat.mul_lt_mul_of_pos_left hj hA
        _ = (n * k / 25) * (25 * ((n - 1) * ((n - 2) * (k - 1)))) := by ring
    have hcardH : (auxF n k).card = n * k * ((n - 1) * ((n - 2) * (k - 1))) := by
      rw [card_auxF_eq]; ring
    have h7' : j * (25 * ((n - 1) * ((n - 2) * (k - 1))))
        < n * k * ((n - 1) * ((n - 2) * (k - 1))) := Nat.lt_of_lt_of_le h4 h3
    have h7 : j * (25 * ((n - 1) * ((n - 2) * (k - 1)))) < (auxF n k).card := by
      rw [hcardH]
      exact h7'
    have h8 : (auxF n k).card
        ≤ (Av (cfgSlots) (auxF n k) M).card + j * (25 * ((n - 1) * ((n - 2) * (k - 1)))) := by
      rw [hcardM] at h1
      exact h1
    rcases Nat.eq_zero_or_pos (Av (cfgSlots) (auxF n k) M).card with hz | hpos
    · rw [hz] at h8
      omega
    · exact Nat.ne_of_gt hpos
  exact chain_len hH hsemi (n * k / 25) hav

/-- **THE FIRST MOMENT IS SHORT OF THE PRIZE BY A CONSTANT FACTOR.**  The budget of
`Hyper.first_stage_size` forces a matching of `≈ n²/6` members; the first moment delivers at most
`nk/25 ≤ n²/25`, and `n²/25 < n²/6` for every `k ≤ n`.  **A factor of at least five is missing,
and §1 shows it is the second moment alone.** -/
theorem firstMoment_short {n k : ℕ} (hn : 3 ≤ n) (hk : k ≤ n) : n * k / 25 < n * n / 6 := by
  have h1 : n * k ≤ n * n := by
    calc n * k = k * n := by ring
      _ ≤ n * n := Nat.mul_le_mul_right n hk
  have h2 : 0 < n * n := Nat.mul_pos (by omega) (by omega)
  have h3 : 6 ≤ n * n := by
    have h4 : n * 3 ≤ n * n := by
      have := Nat.mul_le_mul_right n (by omega : (3 : ℕ) ≤ n)
      simpa [Nat.mul_comm] using this
    omega
  calc n * k / 25 ≤ n * n / 25 := Nat.div_le_div_right h1
    _ < n * n / 6 := by omega

/-! ### §4 — the third local datum: the codegrees of `H` -/

/-- **THE COdegree SET OF TWO SLOTS**: the hyperedges of `H` prescribing both slots — the third
local datum of `H`, after the degrees of round 40 and the per-edge counts of round 42. -/
noncomputable def codeg {n k : ℕ} (σ τ : Verts n × Fin k) : Finset (Cfg n k) :=
  (auxF n k).filter fun g => σ ∈ cfgSlots g ∧ τ ∈ cfgSlots g

@[simp] theorem mem_codeg {n k : ℕ} {σ τ : Verts n × Fin k} {g : Cfg n k} :
    g ∈ codeg σ τ ↔ Ok g ∧ σ ∈ cfgSlots g ∧ τ ∈ cfgSlots g := by
  simp only [codeg, Finset.mem_filter, mem_auxF, true_and]

/-- **THE "MAX CODEGREE ≤ MAX DEGREE" HYPOTHESIS OF PIPPENGER–SPENCER, FOR `H`**: the number of
hyperedges through two slots never exceeds the number through one.  Together with
`meet_card_le` (degrees `≤ 5(n-1)(n-2)(k-1)` growing like `n²k`) and `Hyper.card_auxF`
(`|E(H)| = n(n-1)(n-2)k(k-1)` growing like `n³k²`) this fixes the shape of the hypergraph the nibble
has to be applied to. -/
theorem codeg.card_le_auxDeg {n k : ℕ} (σ τ : Verts n × Fin k) :
    (codeg σ τ).card ≤ (auxDeg n k σ).card :=
  Finset.card_le_card (fun g hg => by
    have h' := (mem_codeg (σ := σ) (τ := τ) (g := g)).mp hg
    exact (mem_auxDeg (vp := σ) (g := g)).mpr (And.intro h'.1 h'.2.1))

/-- **AND THE COdegrees NEVER EXCEED THE DEGREES OF THE AUXILIARY HYPERGRAPH.** -/
theorem codeg.card_le_deg {n k : ℕ} (σ : Verts n × Fin k) :
    (codeg σ σ).card ≤ 5 * ((n - 1) * ((n - 2) * (k - 1))) :=
  le_trans (codeg.card_le_auxDeg σ σ) (card_auxDeg_le σ)

end JSP140
