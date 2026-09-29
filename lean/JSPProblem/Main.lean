import JSPProblem.Definitions
import JSPProblem.ColorClass
import JSPProblem.Counting

/-!
# JSP-000140 — the headline statement

**Catalog statement** (`awards/problems/catalog-0101-0200.md`, record `JSP-000140`):

> **JSP-000140 · How many edge colors are necessary if every four-vertex clique must contain
> at least five colors?**
>
> Graph theory; no later than 1997; current status **Solved**; Lean proof in the catalog: No.
> `[BCDP22]` S. Banerjee, P. Bradshaw, S. Letzter, A. Pokrovskiy, *The Erdős–Gyárfás function
> `f(n,4,5) = 5n/6 + o(n)` — so Gyárfás was right*, arXiv:2207.02920 (2022).

The quantity asked for is the **Erdős–Gyárfás function** `f(n, p, q)` — the least number of
colours in an edge-colouring of `K_n` in which every `K_p` spans at least `q` colours —
specialised to `f(n, 4, 5)`, i.e. `JSP140.EG n` of `Definitions.lean`.

## What this file contains

* `jsp_000140_target` — the *exact* statement of the required theorem `jsp_000140_main`, as a
  `def` (not yet a proved theorem; see `blockers` in `discovery/JSP-000140/policy.json`):
  `FiveSixth EG`, i.e. `f(n,4,5) = 5n/6 + o(n)` in ε-form.
* `fiveSixth_colouring_iff` / `fiveSixth_number_iff` — a *reduction* of the headline
  statement to two purely combinatorial statements, one for each direction.  These are proved
  and identify exactly what still has to be proved for the prize.
* Proved partial results: the **local structure theorem** (`Definitions.lean`,
  `ColorClass.lean`, `Counting.lean`), the **classical bound** `f(n,4,5) ≥ 3(n-1)/4`
  (`Counting.classical_lower_bound`, `Counting.EG_ge_classical`) and the upper bound
  `f(n,4,5) ≤ n²` (`Definitions.EG_le_sq`).

## Status of the headline (round 2)

* **Lower half, for `ε ≥ 1/8`**: proved (`fiveSixthLower_at_eighth`), on the strength of the
  classical counting bound `f(n,4,5) ≥ 3(n-1)/4` of `Counting.classical_lower_bound`.
* **Lower half, for `0 < ε < 1/8`**: open.  This is exactly the sharpening of the counting
  constant `3/4` to `5/6` (BCDP22); in the framework of `Counting.lean` it says that at least
  two thirds of the edges lie in single-edge components of their colour class, i.e.
  `|{two-edge paths}| ≤ n²/6 + o(n²)`.
* **Upper half**: open.  Even the two-sided `O(n)`-shape bound is missing, because no linear
  construction is formalised yet (the best upper bound in this development is
  `f(n,4,5) ≤ n²`, `EG_le_sq`).  The missing ingredient is a round-robin / 1-factorisation
  colouring with `n` (odd) or `n-1` (even) colours.
-/

namespace JSP140

variable {n k : ℕ}

/-- **The target of the required theorem** `jsp_000140_main`:
`f(n,4,5) = 5n/6 + o(n)`, i.e. `|f(n,4,5) - 5n/6| ≤ ε n` for all large `n`, for every
`ε > 0`.  (BCDP22, arXiv:2207.02920.) -/
def jsp_000140_target : Prop := FiveSixth EG

/-- The lower half of the headline statement, phrased for *colourings*: for every `ε > 0` and
all large `n`, **every** admissible `k`-colouring of `K_n` satisfies `k ≥ 5n/6 - ε n`.  This
is the difficult content of the lower bound of BCDP22. -/
def AdmissibleLower (ε : ℝ) : Prop :=
  ∀ ε' : ℝ, 0 < ε' → ∃ N : ℕ, ∀ m : ℕ, N ≤ m → ∀ (j : ℕ) (c : Col m j), Admissible c →
    5 * (m : ℝ) / 6 - ε' * m ≤ j

/-- The upper half of the headline statement, phrased for *colourings*: for every `ε > 0` and
all large `n` there is an admissible `k`-colouring of `K_n` with `k ≤ 5n/6 + ε n`.  This is
the content of the construction in BCDP22. -/
def AdmissibleUpper (ε : ℝ) : Prop :=
  ∀ ε' : ℝ, 0 < ε' → ∃ N : ℕ, ∀ m : ℕ, N ≤ m → ∃ (j : ℕ) (c : Col m j), Admissible c ∧
    (j : ℝ) ≤ 5 * (m : ℝ) / 6 + ε' * m

/-- **The lower bound of the headline theorem, reformulated.**  `EG` is the minimum number of
colours, so the numerical lower bound `f(n,4,5) ≥ 5n/6 - ε n` is exactly the statement that
*every* admissible colouring uses that many colours. -/
theorem fiveSixthLower_iff (ε : ℝ) : FiveSixthLower EG ↔ AdmissibleLower ε := by
  constructor
  · intro h
    intro ε' hε'
    obtain ⟨N, hN⟩ := h ε' hε'
    refine ⟨N, fun m hm j c hc => ?_⟩
    exact le_trans (by simpa using hN m hm) (by simpa using EG_le m j c hc)
  · intro h
    intro ε' hε'
    obtain ⟨N, hN⟩ := h ε' hε'
    refine ⟨N, fun m hm => ?_⟩
    obtain ⟨c, hc⟩ := EG_admissible m
    exact hN m hm (EG m) c hc

/-- **The upper bound of the headline theorem, reformulated.** -/
theorem fiveSixthUpper_iff (ε : ℝ) : FiveSixthUpper EG ↔ AdmissibleUpper ε := by
  constructor
  · intro h
    intro ε' hε'
    obtain ⟨N, hN⟩ := h ε' hε'
    refine ⟨N, fun m hm => ?_⟩
    obtain ⟨c, hc⟩ := EG_admissible m
    exact ⟨EG m, c, hc, by simpa using hN m hm⟩
  · intro h
    intro ε' hε'
    obtain ⟨N, hN⟩ := h ε' hε'
    refine ⟨N, fun m hm => ?_⟩
    obtain ⟨j, c, hc, hj⟩ := hN m hm
    exact le_trans (by simpa using EG_le m j c hc) hj

/-- The headline theorem is exactly the conjunction of the two combinatorial bounds. -/
theorem jsp_000140_target_iff : jsp_000140_target ↔ AdmissibleLower 1 ∧ AdmissibleUpper 1 := by
  rw [jsp_000140_target, fiveSixth_iff, fiveSixthLower_iff, fiveSixthUpper_iff]

/-! ### Proved partial results -/

/-- The upper bound proved in this development: `f(n,4,5) ≤ n²` (the injective colouring). -/
theorem upper_bound_sq (n : ℕ) : EG n ≤ n * n := EG_le_sq n

/-- **The classical lower bound in real form** (Erdős–Gyárfás 1977): for `n ≥ 4`,
`f(n,4,5) ≥ 3(n-1)/4`.  This is the bound which the paper of Banerjee–Bradshaw–Letzter–
Pokrovskiy (arXiv:2207.02920) sharpens to `5n/6 - o(n)`. -/
theorem EG_ge_classical_real (n : ℕ) (hn : 4 ≤ n) :
    (3 : ℝ) * ((n - 1 : ℕ) : ℝ) / 4 ≤ (EG n : ℝ) := by
  have h := EG_ge_classical n hn
  have h' : (3 : ℝ) * ((n - 1 : ℕ) : ℝ) ≤ 4 * (EG n : ℝ) := by exact_mod_cast h
  linarith

/-- A numerical consequence of the classical bound: `f(n,4,5) ≥ n/3` for `n ≥ 4`. -/
theorem EG_ge_third (n : ℕ) (hn : 4 ≤ n) : (EG n : ℝ) ≥ (n : ℝ) / 3 := by
  have h := EG_ge_classical_real n hn
  rw [Nat.cast_sub (by omega : (1 : ℕ) ≤ n)] at h
  norm_num at h
  have h4 : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  nlinarith

/-- **How far the classical bound gets towards the headline.**  The lower half of
`jsp_000140_target` asks for `5n/6 - ε n ≤ f(n,4,5)` for every `ε > 0` and all large `n`.  The
classical bound `3(n-1)/4 ≤ f(n,4,5)` proves exactly this for every `ε ≥ 1/8` and all `n ≥ 18`,
because `5n/6 - n/8 = 17n/24 ≥ 3(n-1)/4` as soon as `n ≥ 18`.  So the missing content of the
headline is sharply localised: the range `0 < ε < 1/8`, i.e. the passage from the constant
`3/4` to the constant `5/6` that is the content of the paper of Banerjee–Bradshaw–Letzter–
Pokrovskiy. -/
theorem fiveSixthLower_at_eighth (ε : ℝ) (hε : 1 / 8 ≤ ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → 5 * (n : ℝ) / 6 - ε * n ≤ (EG n : ℝ) := by
  refine ⟨18, fun n hn => ?_⟩
  have h1 := EG_ge_classical_real n (by omega)
  rw [Nat.cast_sub (by omega : (1 : ℕ) ≤ n)] at h1
  norm_num at h1
  have h4 : (18 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  nlinarith

end JSP140
