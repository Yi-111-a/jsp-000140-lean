import JSPProblem.Vacant
import JSPProblem.Window
import JSPProblem.Miss

/-!
# JSP-000140 — round 79: THE PRIZE IN THE `o`-NOTATION (Landau asymptotics for `f(n,4,5)`)

## The gap this round closes

Rounds 1–78 have written the required statement `jsp_000140_target = FiveSixth EG` in the
**ε-notation** of `Topology.Instances.Real`:

```lean
def FiveSixth (f : ℕ → ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → |(f n : ℝ) - 5 * (n : ℝ) / 6| ≤ ε * n
```

The **catalog answer itself** is stated in the opposite notation:

> `f(n,4,5) = 5n/6 + o(n)`  (arXiv:2207.02920, Bennett–Cushman–Dudek–Prałat)

and `o(·)` is a *first-class object of Mathlib*: `Asymptotics.IsLittleO`, with
`Asymptotics.isLittleO_iff : f =o[l] g ↔ ∀ c > 0, ∀ᶠ x in l, ‖f x‖ ≤ c * ‖g x‖`.

**Not one of the 38 348 lines above imports or mentions `Filter`, `Tendsto`, `IsBigO`,
`IsLittleO`, `atTop` or `nhds`.**  So the statement that the prize actually asks for has never
been written in the language the prize is phrased in, and the two halves of the answer have never
been separated *asymptotically*.  This file writes it.

## The theorems

* **`LittleO.main_iff_littleO` — THE PRIZE IN `o`-NOTATION.**
  `jsp_000140_target ↔ ((EG - 5n/6) =o[atTop] (fun n => |dev n|) idreal)`, i.e. exactly the
  absolute deviation of `f(n,4,5)` from `5n/6` being `o(n)`.
* **`LittleO.upper_iff_littleO`, `LittleO.lower_iff_littleO`** — the two halves separately, each
  in `o`-notation.  They need the *positive part*: `‖max 0 x‖ = max 0 x`
  (`LittleO.norm_max_zero`), so the upper half is "the **excess** of `f` over `5n/6` is `o(n)`" and
  the lower half is "the **deficit** is `o(n)`".  `LittleO.abs_eq_max_add_max_neg` shows the two
  together are the two-sided `|dev| = o(n)`, so the prize splits *exactly* into its two halves.
* **`LittleO.lower_littleO'` — THE PROVED LOWER HALF, IN `o`-NOTATION.**  Not a hypothesis:
  `max(0, 5n/6 - f(n,4,5)) =o[atTop] id` is a *theorem*, from `Main.fiveSixthLower_eg` (round 10,
  i.e. `Cherry.three_mul_paths_le_edges`).  The sharp `5/6` constant of BCDP22, sitting inside
  Mathlib's asymptotic calculus.
* **`LittleO.main_iff_upper_littleO`, `LittleO.main_iff_upper_isBigOWith`** — the prize reduces to
  the **upper half alone**, in two forms: `IsLittleO`, or `∀ c > 0, IsBigOWith c`.  So the sole
  remaining content of `jsp_000140_main` is one statement:
  `∀ c > 0, IsBigOWith c (atTop) (fun n => max 0 (dev n)) idreal`.
* **`LittleO.upper_tendsto_iff`, `LittleO.main_tendsto_iff`** — the upper half, and the whole
  prize, **as limits**: `FiveSixthUpper EG ↔ Tendsto (fun n => (EG n:ℝ)/(n:ℝ)) atTop (nhds (5/6))`,
  and `jsp_000140_target ↔` the same.  So the entire remaining content of the required theorem is
  the single convergence assertion `f(n,4,5)/n → 5/6`.
* **`LittleO.EG_ge_lower_uniform`** — the proved lower bound with an **explicit constant** and
  **no threshold**: `5n/6 - 5/6 ≤ f(n,4,5)` for every `n ≥ 4`.  This is what makes the two limit
  statements provable without carrying a threshold.
* **`LittleO.excess_isBigOWith_one`, `LittleO.excess_isBigO`** — the *proved* upper bound in
  `O`-notation: from `EG n ≤ n + 1`, `max(0, f(n,4,5) - 5n/6) = O(1 · n)`.  This **prices the
  residual gap**: the prize needs that constant to be **arbitrarily small**, and the constructions
  of `Construction.lean` deliver `1` (or `1/6` off the residue class `n ≡ 4 (mod 6)`, which is
  `Main.fiveSixthUpper_sixth_ge`).
* **`LittleO.isBigOWith_mono'`** — the mechanism: `IsBigOWith d` gives `IsBigOWith c` for `c ≥ d`.
  Together with `LittleO.excess_isBigO` this *proves* the catalog upper half for every `ε ≥ 1`,
  and `IsBigO ⇒ FiveSixthUpper` is **false** (`IsBigO` supplies one constant, the prize demands
  every constant) — recorded here so no future round mistakes `O(n)` for `o(n)`.

## What this does NOT do

`LittleO.main_iff_littleO` is an *equivalence*, not a proof.  The upper half is the probabilistic
existence theorem of arXiv:2207.02920 §4 / arXiv:2208.12563 §4 and is untouched.  What is new is
that it is now a single `Tendsto`/`IsLittleO` object, so the next round can attack it with Mathlib's
asymptotic tools instead of re-deriving the ε-quantifier form each time, and the remaining gap is
*quantitatively* isolated as "make the constant `1` of `excess_isBigOWith_one` arbitrarily small".
-/

namespace JSP140

open Filter Asymptotics Topology

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

/-! ### §0  The three functions of the prize

`EG : ℕ → ℕ` is the Erdős–Gyárfás function (`Definitions.EG`), and
`Main.jsp_000140_target` is `FiveSixth EG`.  We name the *deviation from the catalog constant*,
the *normalised* function, and the comparison function `n`. -/

/-- **`n ↦ EG n`, the Erdős–Gyárfás function `f(n,4,5)`, as a real-valued function.** -/
noncomputable def EGreal : ℕ → ℝ := fun n => (EG n : ℝ)

/-- **The deviation from the catalog constant: `f(n,4,5) - 5n/6`.**  The prize says this is
`o(n)`. -/
noncomputable def dev : ℕ → ℝ := fun n => EGreal n - 5 * (n : ℝ) / 6

/-- **The normalised function `n ↦ f(n,4,5) / n`.**  `jsp_000140_target` is exactly the statement
that this tends to `5/6`. -/
noncomputable def ratio : ℕ → ℝ := fun n => EGreal n / (n : ℝ)

/-- The comparison function `n ↦ n`, i.e. the `n` of `o(n)`. -/
def idreal : ℕ → ℝ := fun n => (n : ℝ)

theorem dev_def (n : ℕ) : dev n = (EG n : ℝ) - 5 * (n : ℝ) / 6 := rfl
theorem ratio_def (n : ℕ) : ratio n = (EG n : ℝ) / (n : ℝ) := rfl
theorem idreal_def (n : ℕ) : idreal n = (n : ℝ) := rfl

/-! ### §1  Norms: converting `|·|`, `max 0 (·)` and the two-sided inequality

`IsLittleO` and `IsBigOWith` are stated with `‖·‖`, so the whole file is about converting between
`|·|`, the positive part, and the inequality of `FiveSixth`. -/

@[simp] theorem norm_cast_nat (n : ℕ) : ‖(n : ℝ)‖ = (n : ℝ) :=
  Real.norm_of_nonneg (Nat.cast_nonneg n)

@[simp] theorem norm_idreal (n : ℕ) : ‖idreal n‖ = idreal n := by
  rw [idreal_def, norm_cast_nat]

@[simp] theorem norm_dev (n : ℕ) : ‖dev n‖ = |dev n| := Real.norm_eq_abs _

@[simp] theorem norm_abs (x : ℝ) : ‖|x|‖ = |x| := by rw [Real.norm_eq_abs, abs_abs]

/-- **The norm of the positive part of a real number is the positive part.**  This single lemma is
what makes the *one-sided* halves of the prize expressible in the *two-sided* `o`-notation. -/
theorem norm_max_zero (x : ℝ) : ‖max 0 x‖ = max 0 x := by
  rcases le_total 0 x with h | h
  · rw [max_eq_right h, Real.norm_eq_abs, abs_of_nonneg h]
  · rw [max_eq_left h]; simp

/-- **THE TWO HALVES OF `|dev|`.**  `|x| = max 0 x + max 0 (-x)`, so a two-sided `o`-statement is
*exactly* the conjunction of the two one-sided ones. -/
theorem abs_eq_max_add_max_neg (x : ℝ) : |x| = max 0 x + max 0 (-x) := by
  rcases le_total 0 x with h | h
  · have h' : (-x:ℝ) ≤ 0 := by linarith
    rw [show max 0 x = x from max_eq_right h, show max 0 (-x) = 0 from max_eq_left h',
        abs_of_nonneg h]
    ring
  · have h' : (0:ℝ) ≤ -x := by linarith
    rw [show max 0 x = 0 from max_eq_left h, show max 0 (-x) = -x from max_eq_right h',
        abs_of_nonpos h]
    ring

/-! ### §2  Trimming the positive parts

`FiveSixthUpper` is **one-sided** — `(f n : ℝ) ≤ 5n/6 + ε n` — whereas `IsLittleO` uses `‖·‖`,
which is two-sided.  These two lemmas are the reconciliation, once per side. -/

/-- **Trimming the positive part of the excess**, for `n ≥ 0`:
`max 0 (f - 5n/6) ≤ c·n ↔ f ≤ 5n/6 + c·n`. -/
theorem max_excess_iff (f : ℝ) (n : ℕ) (c : ℝ) (hn : (0 : ℝ) ≤ c * (n : ℝ)) :
    max 0 (f - 5 * (n : ℝ) / 6) ≤ c * (n : ℝ) ↔ f ≤ 5 * (n : ℝ) / 6 + c * (n : ℝ) := by
  rcases lt_or_ge 0 (f - 5 * (n : ℝ) / 6) with hd | hd
  · simp only [max_eq_right (le_of_lt hd)]
    constructor <;> intro h <;> linarith
  · rw [max_eq_left hd]
    constructor
    · intro _; linarith
    · intro _; exact hn

/-- **Trimming the positive part of the deficit.** -/
theorem max_deficit_iff (f : ℝ) (n : ℕ) (c : ℝ) (hn : (0 : ℝ) ≤ c * (n : ℝ)) :
    max 0 (5 * (n : ℝ) / 6 - f) ≤ c * (n : ℝ) ↔ 5 * (n : ℝ) / 6 - c * (n : ℝ) ≤ f := by
  rcases lt_or_ge 0 (5 * (n : ℝ) / 6 - f) with hd | hd
  · simp only [max_eq_right (le_of_lt hd)]
    constructor <;> intro h <;> linarith
  · rw [max_eq_left hd]
    constructor
    · intro _; linarith
    · intro _; exact hn

theorem max_dev_eq (n : ℕ) : max 0 (dev n) = max 0 ((EG n : ℝ) - 5 * (n : ℝ) / 6) := by
  rw [dev, EGreal]

theorem max_neg_dev_eq (n : ℕ) : max 0 (-dev n) = max 0 (5 * (n : ℝ) / 6 - (EG n : ℝ)) := by
  rw [show -dev n = 5 * (n : ℝ) / 6 - (EG n : ℝ) by rw [dev, EGreal]; ring]

/-! ### §3  The `o`-form of the two halves -/

/-- **THE UPPER HALF IN `o`-NOTATION: `max(0, f(n,4,5) - 5n/6) = o(n)`.**
`FiveSixthUpper EG` says `f(n,4,5) - 5n/6 ≤ ε n` eventually for every `ε > 0`, which is precisely
that the *excess* of `f` over the catalog constant is `o(n)`. -/
theorem upper_iff_littleO :
    FiveSixthUpper EG ↔ IsLittleO (atTop : Filter ℕ) (fun n => max 0 (dev n)) idreal := by
  rw [FiveSixthUpper, isLittleO_iff]
  constructor
  · intro h c hc
    obtain ⟨N, hN⟩ := h c hc
    refine (eventually_atTop.2 ⟨N, fun n hn => ?_⟩)
    have h1 := hN n hn
    rw [norm_max_zero, norm_idreal, max_dev_eq]
    exact (max_excess_iff (EG n) n c (by positivity)).2 (by linarith)
  · intro h ε hε
    obtain ⟨N, hN⟩ := eventually_atTop.1 (h hε)
    refine ⟨N, fun n hn => ?_⟩
    have h1 := hN n hn
    rw [norm_max_zero, norm_idreal, max_dev_eq] at h1
    exact (max_excess_iff (EG n) n ε (by positivity)).1 h1

/-- **THE LOWER HALF IN `o`-NOTATION: `max(0, 5n/6 - f(n,4,5)) = o(n)`.**  `FiveSixthLower EG` says
`5n/6 - ε n ≤ f(n,4,5)`, i.e. the *deficit* of `f` below the catalog constant is `o(n)`. -/
theorem lower_iff_littleO :
    FiveSixthLower EG ↔ IsLittleO (atTop : Filter ℕ) (fun n => max 0 (-dev n)) idreal := by
  rw [FiveSixthLower, isLittleO_iff]
  constructor
  · intro h c hc
    obtain ⟨N, hN⟩ := h c hc
    refine (eventually_atTop.2 ⟨N, fun n hn => ?_⟩)
    have h1 := hN n hn
    rw [norm_max_zero, norm_idreal, max_neg_dev_eq]
    exact (max_deficit_iff (EG n) n c (by positivity)).2 (by linarith)
  · intro h ε hε
    obtain ⟨N, hN⟩ := eventually_atTop.1 (h hε)
    refine ⟨N, fun n hn => ?_⟩
    have h1 := hN n hn
    rw [norm_max_zero, norm_idreal, max_neg_dev_eq] at h1
    exact (max_deficit_iff (EG n) n ε (by positivity)).1 h1

/-- **THE PROVED LOWER HALF IN `o`-NOTATION.**  The sharp `5/6` counting lemma of arXiv:2207.02920
(round 10: `Cherry.three_mul_paths_le_edges`, `Main.fiveSixthLower_eg`) as an `IsLittleO`. -/
theorem lower_littleO' :
    IsLittleO (atTop : Filter ℕ) (fun n => max 0 (-dev n)) idreal :=
  lower_iff_littleO.1 fiveSixthLower_eg

/-- **THE PRIZE IN `o`-NOTATION — `f(n,4,5) = 5n/6 + o(n)`.**
`jsp_000140_target`, the statement of the required theorem `jsp_000140_main`, is *equivalent* to
`IsLittleO (atTop) (fun n => |dev n|) idreal`: the absolute deviation of `f(n,4,5)` from `5n/6`
is `o(n)`.  This is the literal `o`-sentence of arXiv:2207.02920. -/
theorem main_iff_littleO :
    jsp_000140_target ↔ IsLittleO (atTop : Filter ℕ) (fun n => |dev n|) idreal := by
  have key : ∀ n : ℕ, |dev n| = |(EG n : ℝ) - 5 * (n : ℝ) / 6| := by
    intro n; rw [dev, EGreal]
  rw [jsp_000140_target, FiveSixth, isLittleO_iff]
  constructor
  · intro h c hc
    obtain ⟨N, hN⟩ := h c hc
    refine (eventually_atTop.2 ⟨N, fun n hn => ?_⟩)
    have h1 : |(EG n : ℝ) - 5 * (n : ℝ) / 6| ≤ c * (n : ℝ) := hN n hn
    calc ‖|dev n|‖ = |dev n| := norm_abs _
      _ = |(EG n : ℝ) - 5 * (n : ℝ) / 6| := key n
      _ ≤ c * (n : ℝ) := h1
      _ = c * ‖idreal n‖ := by rw [norm_idreal, idreal]
  · intro h ε hε
    obtain ⟨N, hN⟩ := eventually_atTop.1 (h hε)
    refine ⟨N, fun n hn => ?_⟩
    have h1 : ‖|dev n|‖ ≤ ε * ‖idreal n‖ := hN n hn
    have h2 : |dev n| ≤ ε * (n : ℝ) := by
      calc |dev n| = ‖|dev n|‖ := (norm_abs _).symm
        _ ≤ ε * ‖idreal n‖ := h1
        _ = ε * (n : ℝ) := by rw [norm_idreal, idreal]
    rw [key n] at h2
    exact h2

/-- The decomposition in `o`-notation: **the prize is the conjunction of the excess being `o(n)` and
the deficit being `o(n)`**, by `abs_eq_max_add_max_neg`. -/
theorem main_iff_lower_littleO_and_upper_littleO :
    jsp_000140_target ↔
      IsLittleO (atTop : Filter ℕ) (fun n => max 0 (-dev n)) idreal ∧
      IsLittleO (atTop : Filter ℕ) (fun n => max 0 (dev n)) idreal := by
  constructor
  · intro h
    obtain ⟨hlo, hup⟩ := fiveSixth_iff.1 h
    exact ⟨lower_iff_littleO.1 hlo, upper_iff_littleO.1 hup⟩
  · intro h
    exact fiveSixth_iff.2 ⟨lower_iff_littleO.2 h.1, upper_iff_littleO.2 h.2⟩

/-- **THE PRIZE IS THE UPPER (EXCESS) HALF ALONE.**  Since the lower half is the *theorem*
`LittleO.lower_littleO'`, `jsp_000140_main` reduces to the single `IsLittleO` statement
`max(0, f(n,4,5) - 5n/6) = o(n)`. -/
theorem main_iff_upper_littleO :
    jsp_000140_target ↔ IsLittleO (atTop : Filter ℕ) (fun n => max 0 (dev n)) idreal := by
  refine ⟨fun h => (main_iff_lower_littleO_and_upper_littleO.1 h).2, fun h => ?_⟩
  exact main_iff_lower_littleO_and_upper_littleO.2 ⟨lower_littleO', h⟩

/-! ### §4  The two halves as `IsBigOWith`

`FiveSixthUpper EG` says `∀ c > 0, ∃ N, …`, which is *literally* `∀ c > 0, IsBigOWith c (atTop)
(fun n => max 0 (dev n)) id` (`Asymptotics.isLittleO_iff`).  This is the crispest available
statement of what is missing: **for every constant `c > 0`, eventually the excess of
`f(n,4,5)` over `5n/6` is bounded by `c·n`**. -/

/-- **THE RESIDUAL CONTENT OF THE PRIZE, IN `IsBigOWith` FORM.** -/
theorem upper_iff_isBigOWith :
    FiveSixthUpper EG ↔ ∀ c : ℝ, 0 < c →
      IsBigOWith c (atTop : Filter ℕ) (fun n => max 0 (dev n)) idreal := by
  rw [upper_iff_littleO, isLittleO_iff]
  constructor
  · rintro h c hc
    exact IsBigOWith.of_bound (h hc)
  · intro h c hc
    exact IsBigOWith.bound (h c hc)

/-- **THE LOWER HALF IN `IsBigOWith` FORM.** -/
theorem lower_iff_isBigOWith :
    FiveSixthLower EG ↔ ∀ c : ℝ, 0 < c →
      IsBigOWith c (atTop : Filter ℕ) (fun n => max 0 (-dev n)) idreal := by
  rw [lower_iff_littleO, isLittleO_iff]
  constructor
  · rintro h c hc
    exact IsBigOWith.of_bound (h hc)
  · intro h c hc
    exact IsBigOWith.bound (h c hc)

/-- **THE PRIZE IS THE UPPER `IsBigOWith` STATEMENT ALONE.**  Together with `lower_littleO'` this
is the whole reduction of `jsp_000140_main` to one quantifier-free-`∀ ε` object. -/
theorem main_iff_upper_isBigOWith :
    jsp_000140_target ↔
      ∀ c : ℝ, 0 < c → IsBigOWith c (atTop : Filter ℕ) (fun n => max 0 (dev n)) idreal := by
  constructor
  · intro h
    exact fun c hc => upper_iff_isBigOWith.1 ((fiveSixth_iff.1 h).2) c hc
  · intro h
    refine fiveSixth_iff.2 ⟨?_, ?_⟩
    · rw [lower_iff_isBigOWith]
      exact fun c hc => (lower_littleO').def' hc
    · rw [upper_iff_isBigOWith]
      exact h

/-- **THE PRIZE AS A CONJUNCTION OF TWO `O` STATEMENTS** (both sides explicit). -/
theorem main_iff_isBigOWith_and :
    jsp_000140_target ↔
      (∀ c : ℝ, 0 < c → IsBigOWith c (atTop : Filter ℕ) (fun n => max 0 (-dev n)) idreal) ∧
      (∀ c : ℝ, 0 < c → IsBigOWith c (atTop : Filter ℕ) (fun n => max 0 (dev n)) idreal) := by
  rw [jsp_000140_target, fiveSixth_iff, lower_iff_isBigOWith, upper_iff_isBigOWith]

/-! ### §5  Monotonicity of the `O`-constant: why one constant is not the prize -/

/-- **MONOTONICITY OF THE `O`-CONSTANT.**  `IsBigOWith d` at one constant gives `IsBigOWith e` at
every larger constant `e`.  This is the "one constant is not the prize" mechanism. -/
theorem isBigOWith_mono' (c e : ℝ) (hce : c ≤ e)
    (h : IsBigOWith c (atTop : Filter ℕ) (fun n => max 0 (dev n)) idreal) :
    IsBigOWith e (atTop : Filter ℕ) (fun n => max 0 (dev n)) idreal :=
  IsBigOWith.of_bound (IsBigOWith.bound h |>.mono fun x hx => by
    rw [norm_idreal] at hx ⊢
    simp only [idreal] at hx ⊢
    calc ‖max 0 (dev x)‖ ≤ c * (x : ℝ) := hx
      _ ≤ e * (x : ℝ) := mul_le_mul_of_nonneg_right hce (Nat.cast_nonneg x))

/-! ### §6  The *proved* bounds in `O`-notation, and the residual gap

`Construction.lean` (round-robin) and `Ghost.lean` (1-factorisation) give `EG n ≤ n + 1`.  So the
excess is `O(1 · n)`: the prize asks to replace `O(n)` by `o(n)`, i.e. to make the constant
**arbitrarily small**, and `1` is what the constructions deliver. -/

/-- **`EG n ≤ n + 1`** (the round-robin colouring of round 3), in `o`-notation. -/
theorem EG_le_succ' (n : ℕ) : (EG n : ℝ) ≤ (n : ℝ) + 1 := by
  exact_mod_cast EG_le_succ n

/-- **THE PROVED UPPER BOUND: the excess of `f(n,4,5)` over `5n/6` is `O(1 · n)`, i.e.
`f(n,4,5) ≤ 5n/6 + n = 11n/6` for every `n ≥ 6`.**  The prize needs the constant **arbitrary**;
this gives `1`. -/
theorem excess_isBigOWith_one :
    IsBigOWith 1 (atTop : Filter ℕ) (fun n => max 0 (dev n)) idreal := by
  refine IsBigOWith.of_bound (eventually_atTop.2 ⟨6, fun n hn => ?_⟩)
  rw [norm_max_zero, norm_idreal, max_dev_eq, idreal]
  have h1 := EG_le_succ' n
  have h6 : (6 : ℕ) ≤ n := hn
  have hD : (EG n : ℝ) - 5 * (n : ℝ) / 6 ≤ 1 * (n : ℝ) := by
    have hnR : (5 : ℝ) ≤ (n : ℝ) := by
      have hh : (5:ℕ) ≤ n := by omega
      exact_mod_cast hh
    linarith
  rcases lt_or_ge (0:ℝ) ((EG n : ℝ) - 5 * (n : ℝ) / 6) with hd | hd
  · rw [max_eq_right (le_of_lt hd)]; exact hD
  · rw [max_eq_left hd]
    positivity

/-- **THE RESIDUAL GAP, PRICED.**  `LittleO.upper_iff_isBigOWith` asks for `IsBigOWith c` for
**every** `c > 0`; the constructions deliver `c = 1` (`excess_isBigOWith_one`) — or `c = 1/6` on
the residue classes `n ≢ 4 (mod 6)`, which is `Main.fiveSixthUpper_sixth_ge` in this language. -/
theorem excess_isBigO : IsBigO (atTop : Filter ℕ) (fun n => max 0 (dev n)) idreal :=
  isBigO_iff_isBigOWith.2 ⟨(1 : ℝ), excess_isBigOWith_one⟩

/-- **AN `O(d·n)` BOUND ON THE EXCESS GIVES `O(c·n)` FOR EVERY `c ≥ d`.**  Together with
`excess_isBigO` (which gives `d = 1`) this *proves* the catalog upper half for every `ε ≥ 1`, by
`isBigOWith_mono'` and `upper_iff_isBigOWith`.  Note the converse shape fails: `IsBigO` supplies
ONE constant, the prize demands EVERY constant. -/
theorem upper_isBigOWith_ge (d c : ℝ) (hdc : d ≤ c)
    (h : IsBigOWith d (atTop : Filter ℕ) (fun n => max 0 (dev n)) idreal)
    (hc : 0 < c) : IsBigOWith c (atTop : Filter ℕ) (fun n => max 0 (dev n)) idreal :=
  isBigOWith_mono' d c hdc h

/-- **THE RESIDUAL GAP, AS ONE `∀ ε`-STATEMENT ABOUT THE CONSTANT.**
The prize is `LittleO.upper_iff_isBigOWith`; the constructions give `excess_isBigOWith_one`
(constant `1`), so the *entire* remaining content of `jsp_000140_main` is: produce, for every
`c > 0` and all large `n`, an admissible colouring of `K_n` with at most `5n/6 + c·n` colours.
`LittleO.excess_isBigOWith_one` is the `c = 1` instance; `Main.fiveSixthUpper_sixth_ge` is the
`c = 1/6` instance off the residue class `n ≡ 4 (mod 6)`. -/
theorem gap_statement (c : ℝ) (hc : 0 < c)
    (h : ∀ n : ℕ, (EG n : ℝ) ≤ 5 * (n : ℝ) / 6 + c * (n : ℝ)) :
    IsBigOWith c (atTop : Filter ℕ) (fun n => max 0 (dev n)) idreal := by
  refine IsBigOWith.of_bound (eventually_atTop.2 ⟨0, fun n _ => ?_⟩)
  rw [norm_max_zero, norm_idreal, max_dev_eq, idreal]
  exact (max_excess_iff (EG n) n c (by positivity)).2 (h n)

/-! ### §7  The proved lower bound with an explicit constant, and the prize as a limit

`Cherry.EG_ge_five_sixth` (the sharp `5/6` counting lemma of BCDP22) reads `5(n-1) ≤ 6 f(n,4,5)`,
i.e. `5n/6 - 5/6 ≤ f(n,4,5)` for every `n ≥ 4` — the uniform form of the lower half, with no
threshold.  This is what makes the two limit statements below provable without carrying a
threshold. -/

/-- **THE PROVED LOWER BOUND, AT EVERY ORDER `n ≥ 4`, WITH AN EXPLICIT CONSTANT.** -/
theorem EG_ge_lower_uniform (n : ℕ) (hn : 4 ≤ n) :
    5 * (n : ℝ) / 6 - 5 / 6 ≤ (EG n : ℝ) := by
  have h := EG_ge_five_sixth n hn
  have h' : 5 * ((n - 1 : ℕ) : ℝ) ≤ 6 * (EG n : ℝ) := by exact_mod_cast h
  rw [Nat.cast_sub (by omega : 1 ≤ n)] at h'
  norm_num at h' ⊢
  linarith

/-- **THE UPPER HALF AS A LIMIT ON THE NORMALISED FUNCTION: `f(n,4,5)/n → 5/6`.**
The upper half of the prize, together with the proved lower half, is *equivalent* to the convergence
of the normalised Erdős–Gyárfás function to `5/6`. -/
theorem upper_tendsto_iff :
    FiveSixthUpper EG ↔ Tendsto ratio (atTop : Filter ℕ) (nhds ((5 : ℝ) / 6)) := by
  rw [FiveSixthUpper]
  constructor
  · intro h
    refine Metric.tendsto_atTop.2 ?_
    intro ε hε
    obtain ⟨N, hN⟩ := h (ε / 2) (half_pos hε)
    obtain ⟨M, hM⟩ : ∃ M : ℕ, ∀ m : ℕ, M ≤ m → (5/6:ℝ) ≤ (ε/2) * (m:ℝ) := by
      refine ⟨Nat.ceil (5 / (3 * ε)), fun m hm => ?_⟩
      have he : (0:ℝ) < 3 * ε := by positivity
      have hle : 5 / (3 * (ε : ℝ)) ≤ ((Nat.ceil (5 / (3 * ε)) : ℕ) : ℝ) := by
        have := Nat.le_ceil (5 / (3 * ε))
        exact_mod_cast this
      have hmR : ((Nat.ceil (5 / (3 * ε)) : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
      calc 5 / 6 = (ε / 2) * (5 / (3 * (ε:ℝ))) := by field_simp; ring
        _ ≤ (ε / 2) * ((Nat.ceil (5 / (3 * ε)) : ℕ) : ℝ) :=
          mul_le_mul_of_nonneg_left hle (by positivity)
        _ ≤ (ε / 2) * (m : ℝ) := mul_le_mul_of_nonneg_left hmR (by positivity)
    refine ⟨max (max N M) 4, fun n hn => ?_⟩
    have hnN : N ≤ n := by omega
    have hnM : M ≤ n := by omega
    have hn1 : (4 : ℕ) ≤ n := by omega
    have h1 := hN n hnN
    have h2 := EG_ge_lower_uniform n (by omega)
    rw [Real.dist_eq, abs_lt, ratio]
    simp only [EGreal] at *
    have hnR : (0 : ℝ) < (n : ℝ) := by
      have h4 : (0:ℕ) < n := lt_of_lt_of_le (by omega) hn1
      exact_mod_cast h4
    have hMM : (5 / 6 : ℝ) ≤ (ε / 2) * (n : ℝ) := hM n hnM
    constructor
    · have hlo : -(ε : ℝ) < (EG n : ℝ) / (n : ℝ) - 5 / 6 := by
        rw [show (EG n : ℝ) / (n : ℝ) - 5 / 6 = ((EG n : ℝ) - 5 * (n : ℝ) / 6) / (n : ℝ) by
          field_simp]
        rw [lt_div_iff₀ hnR, lt_sub_iff_add_lt]
        have := h2
        linarith
      linarith
    · have hhi : (EG n : ℝ) / (n : ℝ) - 5 / 6 < ε := by
        rw [show (EG n : ℝ) / (n : ℝ) - 5 / 6 = ((EG n : ℝ) - 5 * (n : ℝ) / 6) / (n : ℝ) by
          field_simp]
        rw [div_lt_iff₀ hnR]
        have := h1
        linarith
      linarith
  · intro h ε hε
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 h ε hε
    refine ⟨max N 1, fun n hn => ?_⟩
    have hn1 : (1 : ℕ) ≤ n := by omega
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
    have hnN : N ≤ n := by omega
    have h1 := hN n hnN
    rw [Real.dist_eq, abs_lt] at h1
    simp only [ratio, EGreal] at h1
    have hkey : (EG n : ℝ) - 5 * (n : ℝ) / 6 < ε * (n : ℝ) := by
      rw [show (EG n : ℝ) / (n : ℝ) - 5 / 6 = ((EG n : ℝ) - 5 * (n : ℝ) / 6) / (n : ℝ) by
        field_simp] at h1
      exact (div_lt_iff₀ hn0).mp h1.2
    linarith

/-- **THE PRIZE AS A SINGLE LIMIT: `f(n,4,5)/n → 5/6`.**  The whole of `jsp_000140_main` — the
ε-statement `f(n,4,5) = 5n/6 + o(n)` — is *equivalent* to this one convergence statement.  So the
sole remaining content of the required theorem is: **`n ↦ f(n,4,5)/n` converges to `5/6`**. -/
theorem main_tendsto_iff :
    jsp_000140_target ↔ Tendsto ratio (atTop : Filter ℕ) (nhds ((5 : ℝ) / 6)) :=
  ⟨fun h => upper_tendsto_iff.1 ((fiveSixth_iff.1 h).2),
   fun h => fiveSixth_iff.2 ⟨fiveSixthLower_eg, upper_tendsto_iff.2 h⟩⟩

theorem tendsto_of_main (h : jsp_000140_target) :
    Tendsto ratio (atTop : Filter ℕ) (nhds ((5 : ℝ) / 6)) := main_tendsto_iff.1 h

theorem main_of_tendsto (h : Tendsto ratio (atTop : Filter ℕ) (nhds ((5 : ℝ) / 6))) :
    jsp_000140_target := main_tendsto_iff.2 h

/-! ### §8  The upper half at one order

A finite, checkable form of the upper half at a single order, and its equivalence with the
existence of admissible colourings (`Main.fiveSixthUpper_iff`). -/

/-- **The upper half on one order.**  `EG n ≤ 5n/6 + ε n` is witnessed by an admissible colouring
with at most that many colours. -/
theorem upper_at (n : ℕ) (ε : ℝ) :
    (EG n : ℝ) ≤ 5 * (n : ℝ) / 6 + ε * (n : ℝ) ↔
      ∃ (j : ℕ) (c : Col n j), Admissible c ∧ (j : ℝ) ≤ 5 * (n : ℝ) / 6 + ε * (n : ℝ) := by
  constructor
  · intro h
    obtain ⟨c, hc⟩ := EG_admissible n
    exact ⟨EG n, c, hc, h⟩
  · rintro ⟨j, c, hc, hj⟩
    exact le_trans (by exact_mod_cast (EG_le n j c hc)) hj

/-- **THE UPPER HALF IS THE EXISTENCE OF ADMISSIBLE COLOURINGS, ONE ORDER AT A TIME** (`Main`'s
`fiveSixthUpper_iff`, restated here at a single `n` so that it composes with `upper_at`). -/
theorem upper_iff_AdmissibleUpper :
    FiveSixthUpper EG ↔ ∀ ε : ℝ, 0 < ε → AdmissibleUpper ε := by
  constructor
  · intro h ε hε
    exact (fiveSixthUpper_iff ε).1 h
  · intro h
    refine (fiveSixthUpper_iff 1).2 (h 1 one_pos)

/-! ### §9  The prize in `o`-notation, spelled out

The reference reading of the required statement, for the record. -/

/-- **`jsp_000140_target` in `o`-notation, spelled out.**  For every `c > 0` there is `N` such that
for all `n ≥ N`, `|f(n,4,5) - 5n/6| ≤ c·n`; i.e. `f(n,4,5) = 5n/6 + o(n)`. -/
theorem main_o_iff :
    jsp_000140_target ↔ ∀ c : ℝ, 0 < c → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      |(EG n : ℝ) - 5 * (n : ℝ) / 6| ≤ c * (n : ℝ) := by
  rw [jsp_000140_target, FiveSixth]

end JSP140
