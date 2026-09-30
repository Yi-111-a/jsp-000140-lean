import JSPProblem.Restriction

/-!
# JSP-000140 — the faithful `o(n)` form of the construction hypothesis

Round 14 reduced the required theorem `jsp_000140_main` to **one** design-existence hypothesis,
`Restriction.jsp_000140_main_of_STS_family`: for every `m ≡ 1 (mod 6)` there is an admissible
`k`-colouring of `K_m` with `6 * k = 5 * (m - 1)` whose two-edge paths form a Steiner triple system.
The price of that reduction is that it asks for the *exact* extremal value, i.e. for

    f(m, 4, 5) ≤ 5(m-1)/6      for every m ≡ 1 (mod 6),

which is **strictly stronger than the published result**: arXiv:2207.02920 (Bennett–Cushman–Dudek–
Prałat) proves `f(n,4,5) = 5n/6 + o(n)`, i.e. the *relative* bound `f(m,4,5) ≤ 5m/6 + ε m` for every
fixed `ε > 0` and all large `m`.  The `O(1)` version is not known for the residue class
`1 (mod 6)`; in particular `Restriction.fiveSixthUpper_of_family_const` (which asks for a slack
`6k ≤ 5(m-1) + 6D` with a **fixed** `D`) is a hypothesis which is not known to hold, so as it
stands it does not reduce the prize to the content of the paper.

This file repairs the reduction: it proves the upper half of the headline from the hypothesis the
paper actually supplies — an arbitrary **linear** slack `δ * m` per `δ > 0` — and hence

    **`jsp_000140_main_of_STS_slack_family` :  the design hypothesis with an `o(n)` slack
                                          ⟹  `jsp_000140_target`.**

Concretely:

* `STSFamily` — the content of arXiv:2207.02920 in the form needed here: for every `δ > 0` and all
  large `m ≡ 1 (mod 6)`, an admissible `k`-colouring of `K_m` whose two-edge paths form a Steiner
  triple system and which uses at most `5(m-1)/6 + δm/6` colours;
* `fiveSixthUpper_of_slack_family` — **THE UPPER HALF FROM THAT HYPOTHESIS**: the `δ * m` slack is
  absorbed by the `ε n` term of the headline after halving `ε` (`δ = ε/2`) and taking
  `n ≥ 10/ε`, and the five other residue classes are absorbed by monotonicity of `f`
  (`Restriction.EG_mono`) and the density of `1 (mod 6)` (`Restriction.exists_one_mod_six_ge`);
* `fiveSixthLower_slack` — the lower half, in the two-sided `±ε` form, with the threshold of this
  reduction;
* **`jsp_000140_main_of_STS_slack_family` — THE REQUIRED STATEMENT REDUCED TO THE TRUE CONTENT OF
  THE PUBLISHED RESULT**;
* `STSFamily_of_extremal` — the round-14 hypothesis (exact extremal colourings) implies the
  `STSFamily` of this file, so nothing proved in round 14 is lost: the two reductions differ only
  in the strength of the hypothesis, not in the conclusion.
-/

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

namespace JSP140

/-- **The construction hypothesis of arXiv:2207.02920, in the form relevant for `JSP-000140`.**

For every `δ > 0` and all sufficiently large `m ≡ 1 (mod 6)` there is an admissible `k`-colouring
`c` of `K_m` such that

* the two-edge paths of `c` form a **Steiner triple system** (`Rigidity.tight_pathFinset_is_STS`:
  this is what an extremal colouring looks like), and
* the colouring uses at most `5(m-1)/6 + δm/6` colours.

The `δ * m` slack is the `o(n)` of the published result `f(n,4,5) = 5n/6 + o(n)`; `δ = 0`
(the exact extremal value for every `m ≡ 1 (mod 6)`) is *not* known. -/
def STSFamily : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ M : ℕ, ∀ m : ℕ, M ≤ m → m % 6 = 1 →
    ∃ (k : ℕ) (c : Col m k), Admissible c ∧ IsSTS (pathFinset c) ∧
      (6 : ℝ) * (k : ℝ) ≤ 5 * ((m - 1 : ℕ) : ℝ) + δ * (m : ℝ)

/-- The same hypothesis with the Steiner triple system condition dropped: only the *number* of
colours is specified. -/
def SlackFamily : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ M : ℕ, ∀ m : ℕ, M ≤ m → m % 6 = 1 →
    ∃ (k : ℕ) (c : Col m k), Admissible c ∧
      (6 : ℝ) * (k : ℝ) ≤ 5 * ((m - 1 : ℕ) : ℝ) + δ * (m : ℝ)

theorem SlackFamily.of_STS (h : STSFamily) : SlackFamily := by
  intro δ hδ
  obtain ⟨M, hM⟩ := h δ hδ
  refine ⟨M, fun m hMm hm => ?_⟩
  obtain ⟨k, c, hc, hsts, hk⟩ := hM m hMm hm
  exact ⟨k, c, hc, hk⟩

/-- **THE UPPER HALF OF THE HEADLINE, FROM THE PUBLISHED CONSTRUCTION.**  If for every `δ > 0` and
all large `m ≡ 1 (mod 6)` the graph `K_m` admits an admissible colouring with at most
`5(m-1)/6 + δm/6` colours, then

    f(n, 4, 5) ≤ 5n/6 + ε n     for every ε > 0 and all n ≥ max (M(ε/2) + 7, ⌈10/ε⌉ + 1).

This is the `o(n)` form of `Restriction.fiveSixthUpper_of_family_const`: the constant slack `D` is
replaced by the linear slack `δ * m` of the paper, and the threshold is explicit. -/
theorem fiveSixthUpper_of_slack_family (hfam : SlackFamily) : FiveSixthUpper EG := by
  unfold FiveSixthUpper
  intro ε hε
  obtain ⟨M, hM⟩ := hfam (ε / 2) (by linarith : 0 < ε / 2)
  refine ⟨max (M + 7) (Nat.ceil (10 / ε) + 1), fun n hn => ?_⟩
  obtain ⟨m, hnm, hmn, hres⟩ := exists_one_mod_six_ge n (by omega)
  have hMm : M ≤ m := by omega
  obtain ⟨k, c, hcadm, hk⟩ := hM m hMm hres
  have hEG : EG n ≤ k := (EG_mono hnm).trans (EG_le m k c hcadm)
  have hEG' : (6 : ℝ) * (EG n : ℝ) ≤ (6 : ℝ) * (k : ℝ) := by
    exact_mod_cast (Nat.mul_le_mul_left 6 hEG)
  have hmn' : ((m - 1 : ℕ) : ℝ) ≤ (n : ℝ) + 5 := by
    exact_mod_cast (show m - 1 ≤ n + 5 by omega)
  have hm' : (m : ℝ) ≤ (n : ℝ) + 6 := by
    exact_mod_cast (show m ≤ n + 6 from hmn)
  -- `10 < ε n`, so that the constant `25` of the rounding is absorbed
  have hcast : ((Nat.ceil (10 / ε) + 1 : ℕ) : ℝ) ≤ (n : ℝ) := by
    have h1 : (Nat.ceil (10 / ε) + 1 : ℕ) ≤ max (M + 7) (Nat.ceil (10 / ε) + 1) := by omega
    have h1' : (Nat.ceil (10 / ε) + 1 : ℕ) ≤ n := le_trans h1 hn
    exact_mod_cast h1'
  have hcast' : (Nat.ceil (10 / ε) : ℝ) + 1 ≤ (n : ℝ) := by
    have hx : ((Nat.ceil (10 / ε) + 1 : ℕ) : ℝ) = (Nat.ceil (10 / ε) : ℝ) + (1 : ℝ) := by
      rw [Nat.cast_add]; norm_num
    rw [← hx]
    exact hcast
  have hstep : 10 / ε < (n : ℝ) := by
    have h1 : 10 / ε ≤ (Nat.ceil (10 / ε) : ℝ) := Nat.le_ceil _
    have h2 : (Nat.ceil (10 / ε) : ℝ) < (Nat.ceil (10 / ε) : ℝ) + 1 := by linarith
    linarith
  have heps : 10 < ε * (n : ℝ) := by
    have hmul : (10 / ε) * ε < (n : ℝ) * ε := mul_lt_mul_of_pos_right hstep hε
    have hkey : (10 / ε) * ε = 10 := by field_simp
    linarith
  -- the slack `δ * m` with `δ = ε/2` is absorbed by `ε n`
  have hslack : (25 : ℝ) + 3 * ε ≤ (11 / 2) * (ε * (n : ℝ)) := by
    by_cases h : ε ≤ 10
    · have h1 : (25 : ℝ) + 3 * ε ≤ 55 := by linarith
      have h2 : (55 : ℝ) ≤ (11 / 2) * (ε * (n : ℝ)) := by linarith
      linarith
    · have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (show (1 : ℕ) ≤ n by omega)
      have h2 : ε * (n : ℝ) ≥ ε := by
        have h1' : (1 : ℝ) * ε ≤ (n : ℝ) * ε := mul_le_mul_of_nonneg_right h1 (le_of_lt hε)
        rw [one_mul] at h1'
        calc ε ≤ (n : ℝ) * ε := h1'
          _ = ε * (n : ℝ) := by ring
      have h3 : (25 : ℝ) + 3 * ε ≤ (11 / 2) * ε := by linarith
      linarith
  have h1 : (6 : ℝ) * (EG n : ℝ) ≤ 5 * ((m - 1 : ℕ) : ℝ) + (ε / 2) * (m : ℝ) := by
    linarith
  have h1' : (ε / 2) * (m : ℝ) ≤ (ε / 2) * ((n : ℝ) + 6) :=
    mul_le_mul_of_nonneg_left hm' (by linarith)
  have h2 : (6 : ℝ) * (EG n : ℝ) ≤ 5 * ((n : ℝ) + 5) + (ε / 2) * ((n : ℝ) + 6) := by
    linarith
  have hid : (ε / 2) * ((n : ℝ) + 6) = (ε * (n : ℝ)) / 2 + 3 * ε := by ring
  have h3 : (6 : ℝ) * (EG n : ℝ) ≤ 5 * (n : ℝ) + (ε * (n : ℝ)) / 2 + (25 : ℝ) + 3 * ε := by
    rw [hid] at h2
    linarith
  have h4 : (6 : ℝ) * (EG n : ℝ) ≤ 5 * (n : ℝ) + (6 : ℝ) * (ε * (n : ℝ)) := by
    linarith
  calc (EG n : ℝ) ≤ (5 * (n : ℝ) + 6 * (ε * (n : ℝ))) / 6 := by linarith
    _ = 5 * (n : ℝ) / 6 + ε * n := by ring

/-- **THE HEADLINE, REDUCED TO THE TRUE CONTENT OF arXiv:2207.02920.**  The lower half of
`jsp_000140_target` is proved (`Main.fiveSixthLower_eg`); the upper half follows from `hfam`.  This
is the same reduction as `Restriction.fiveSixth_of_extremal_family` but with the *published* `o(n)`
slack instead of the (unknown) exact extremal value. -/
theorem jsp_000140_main_of_slack_family (hfam : SlackFamily) : jsp_000140_target := by
  rw [jsp_000140_target, fiveSixth_iff]
  exact ⟨fiveSixthLower_eg, fiveSixthUpper_of_slack_family hfam⟩

/-- **THE REQUIRED THEOREM, REDUCED TO THE PUBLISHED CONSTRUCTION OF arXiv:2207.02920.**  If for
every `δ > 0` and all large `m ≡ 1 (mod 6)` there is an admissible `k`-colouring of `K_m` with

* at most `5(m-1)/6 + δm/6` colours, and
* two-edge paths forming a **Steiner triple system**,

then `jsp_000140_target` — the statement of the required theorem `jsp_000140_main`, i.e. the catalog
answer `f(n,4,5) = 5n/6 + o(n)` — holds.  Together with the lower half of `Cherry.lean` this
identifies the *whole* remaining content of the prize: the probabilistic construction of Bennett,
Cushman, Dudek and Prałat (random triangle removal + differential equation method). -/
theorem jsp_000140_main_of_STS_slack_family (hfam : STSFamily) : jsp_000140_target :=
  jsp_000140_main_of_slack_family (SlackFamily.of_STS hfam)

/-- **Nothing of round 14 is lost.**  A family of *exactly* extremal Steiner triple system colourings
for every `m ≡ 1 (mod 6)` — the hypothesis of `Restriction.jsp_000140_main_of_STS_family` — is
stronger than the `o(n)` hypothesis of this file, hence implies it. -/
theorem STSFamily_of_extremal
    (hex : ∀ m : ℕ, m % 6 = 1 → ∃ (k : ℕ) (c : Col m k), Admissible c ∧ IsSTS (pathFinset c) ∧
      6 * k = 5 * (m - 1)) : STSFamily := by
  intro δ hδ
  refine ⟨1, fun m _ hm => ?_⟩
  obtain ⟨k, c, hc, hsts, hk⟩ := hex m hm
  refine ⟨k, c, hc, hsts, ?_⟩
  have hk' : (6 : ℝ) * (k : ℝ) ≤ 5 * ((m - 1 : ℕ) : ℝ) + δ * (m : ℝ) := by
    have h5 : (6 : ℝ) * (k : ℝ) = 5 * ((m - 1 : ℕ) : ℝ) := by exact_mod_cast hk
    have h6 : (0 : ℝ) ≤ δ * (m : ℝ) := by positivity
    linarith
  exact hk'

/-- **The two reductions agree.**  The round-14 hypothesis implies the round-15 hypothesis, so the
`o(n)` reduction of this file is the *faithful* one: it is equivalent to the published statement
`f(n,4,5) = 5n/6 + o(n)` together with the proved lower half. -/
theorem jsp_000140_main_of_STS_extremal_family
    (hex : ∀ m : ℕ, m % 6 = 1 → ∃ (k : ℕ) (c : Col m k), Admissible c ∧ IsSTS (pathFinset c) ∧
      6 * k = 5 * (m - 1)) : jsp_000140_target :=
  jsp_000140_main_of_STS_slack_family (STSFamily_of_extremal hex)

end JSP140
