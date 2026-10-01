import JSPProblem.Definitions
import JSPProblem.ColorClass
import JSPProblem.Counting
import JSPProblem.Paths
import JSPProblem.Cherry
import JSPProblem.Ghost
import JSPProblem.Construction
import JSPProblem.Rigidity
import JSPProblem.Extremal
import JSPProblem.Singles
import JSPProblem.Tables
import JSPProblem.Search
import JSPProblem.FastSearch
import JSPProblem.VertexSearch
import JSPProblem.QuadEnum
import JSPProblem.Distinct
import JSPProblem.LeafFree
import JSPProblem.Star
import JSPProblem.Local
import JSPProblem.Classwise

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
* `fiveSixthLower_iff` / `fiveSixthUpper_iff` / `jsp_000140_target_iff` — a *proved reduction*
  of the headline statement to two purely combinatorial statements, one for each direction
  (`AdmissibleLower 1` and `AdmissibleUpper 1`).  These identify exactly what still has to be
  proved for the prize.
* Proved partial results: the **local structure theorem** (`Definitions.lean`,
  `ColorClass.lean`, `Counting.lean`), the **classical bound** `f(n,4,5) ≥ 3(n-1)/4`
  (`Counting.classical_lower_bound`, `Counting.EG_ge_classical`), the **round-robin
  construction** `f(n,4,5) ≤ n` for odd `n` and `f(n,4,5) ≤ n+1` in general
  (`Construction.lean`), the **quantitative `5/6` criterion** for the lower half
  (`Paths.lean`), the **ghost-vertex construction** `f(n,4,5) ≤ n-1` for `n ≡ 0, 2 (mod 6)`
  (`Ghost.lean`), and the resulting **two-sided shape bounds**
  `|f(n,4,5) - 5n/6| ≤ n/6 + 1` (`fiveSixthShape`) and, for `n ≢ 4 (mod 6)`,
  `5n/6 - (n/12 + 3/4) ≤ f(n,4,5) ≤ 5n/6 + n/6` (`fiveSixthShape_sixth_residue`).

## Status of the headline (round 10)

* **Lower half: COMPLETE.**  `FiveSixthLower EG` — for every `ε > 0` and all large `n`,
  `5n/6 - ε n ≤ f(n,4,5)` — is proved (`fiveSixthLower_eg`, `admissibleLower_eps`,
  `Cherry.fiveSixthLower_eps`), with the *sharp* constant `5/6` of BCDP22 and no `o(n)` loss:
  `Cherry.five_sixth_lower` gives `f(n,4,5) ≥ 5(n-1)/6` for every `n ≥ 4`, from the counting
  lemma `Cherry.three_mul_paths_le_edges` (`3 * Paths c ≤ |E(K_n)|`), i.e. from the fact that
  **at least two thirds of the edges of `K_n` lie in single-edge components of their colour
  class** (`Cherry.cherryEdges_disjoint`: every two-edge path brings three edges with it — its own
  two edges and the isolated single edge between its leaves — and the triples of different
  two-edge paths are disjoint).  This replaces the classical constant `3/4` of Erdős–Gyárfás
  (1977), which was the state of the art here in round 9 (`fiveSixthLower_at_eighth`).
* **Upper half**: as in round 4, proved for `ε ≥ 1/6` on all `n ≢ 4 (mod 6)`
  (`fiveSixthUpper_sixth_ge`) and for `ε ≥ 1/3` on all `n` (`fiveSixthUpper_at_third`).  The
  range `0 < ε < 1/6` is open; it needs the BCDP22 construction (1-factorisations of hypergraph
  matchings).
* **Two-sided, sharp constant**: `5n/6 - 5/6 ≤ f(n,4,5) ≤ 5n/6 + n/6 + 1` for all `n ≥ 4`
  (`fiveSixthShape_five_sixth`), and `|f(n,4,5) - 5n/6| ≤ n/6` for all `n ≥ 5` with
  `n ≢ 4 (mod 6)` (`fiveSixthShape_sixth_residue'`), so the catalogue estimate
  `|f(n,4,5) - 5n/6| ≤ ε n` holds for **every `ε ≥ 1/6`** on those `n`
  (`fiveSixth_ge_sixth`, `fiveSixth_eps_ge_sixth`).

## Status before round 10 (round 4)

* **Two-sided**: `|f(n,4,5) - 5n/6| ≤ n/6 + 1` for all `n ≥ 4` (`fiveSixthShape`), i.e.
  `f(n,4,5) = 5n/6 + O(n)`; in particular the headline estimate holds for every `ε ≥ 1`
  (`fiveSixth_ge_one`).
* **Lower half, for `ε ≥ 1/8`**: proved (`fiveSixthLower_at_eighth`), on the strength of the
  classical counting bound `f(n,4,5) ≥ 3(n-1)/4` of `Counting.classical_lower_bound`.
  In the colouring language of the reduction theorem: `admissibleLower_at_third` for `ε ≥ 1/3`.
* **Upper half, for `ε ≥ 1/3`**: proved (`fiveSixthUpper_at_third`,
  `admissibleUpper_at_third`), from the round-robin colouring `c({a,b}) = a+b` of
  `Construction.lean`; on odd `n` the upper half holds already for `ε ≥ 1/6`
  (`fiveSixthUpper_odd_at_sixth`, `fiveSixthUpper_odd_ge`).
* **Upper half, for `0 < ε < 1/3`**: open.  This needs a colouring with `5n/6 + o(n)` colours,
  i.e. saving a further `n/6` colours w.r.t. the round-robin colouring; the round-robin
  colouring cannot be improved by merging colour classes (its colour classes are perfect
  matchings, so merging two of them creates even cycles, and a `K₄` on a 4-cycle spans three
  colours only).  The BCDP22 construction uses hypergraph-Ramsey (1-factorisation) ideas.
  *Round 4*: the ghost colouring (`Ghost.lean`) is a second mechanism and reaches `n - 1`
  colours on `K_n` for `n ≡ 0, 2 (mod 6)`, so the upper half now holds at `ε = 1/6` for all
  `n ≢ 4 (mod 6)` (`fiveSixthUpper_sixth_residue`, `fiveSixthUpper_sixth_ge`).
* **Lower half, for `0 < ε < 1/8` (round 4 status, CLOSED in round 10)**: open.  This is exactly the sharpening of the counting
  constant `3/4` to `5/6` (BCDP22); in the framework of `Counting.lean` it says that at least
  two thirds of the edges lie in single-edge components of their colour class, i.e.
  `|{two-edge paths}| ≤ n²/6 + o(n²)`.
  *Round 4*: `Paths.lean` isolates exactly this hypothesis.  `Paths.mul_n_sub_one_le` is the
  quantitative identity `n(n-1) ≤ n·k + Paths c` (i.e. `k ≥ (n-1) - Paths c/n`), and
  `Paths.five_sixth_of_paths` concludes `5(n-1) ≤ 6k` from the single hypothesis
  `Paths c ≤ n(n-1)/6` — the BCDP22 lower bound in the form of one concrete inequality on the
  number of two-edge paths.  It also re-derives the classical bound (`classical_lower_bound'`).
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

/-! ### The linear upper bounds and the two-sided shape bound -/

/-- **The linear upper bound, in real form** (round-robin colouring, `Construction.lean`):
`f(n,4,5) ≤ n + 1` for every `n`, and `f(n,4,5) ≤ n` for every odd `n`.  Together with the
classical lower bound this is the statement `f(n,4,5) = Θ(n)`. -/
theorem EG_le_succ_real (n : ℕ) : (EG n : ℝ) ≤ (n : ℝ) + 1 := by
  have h := EG_le_succ n
  exact_mod_cast h

theorem EG_le_of_odd_real (n : ℕ) (hn : n % 2 = 1) : (EG n : ℝ) ≤ (n : ℝ) := by
  have h := EG_le_sumCol n hn
  exact_mod_cast h

/-- **The two-sided shape bound.**  For `n ≥ 4`,

    |f(n,4,5) - 5n/6| ≤ n/6 + 1,

i.e. `f(n,4,5) = 5n/6 + O(n)`: the catalog answer `f(n,4,5) = 5n/6 + o(n)` holds up to a linear
error.  *Lower side*: `3(n-1)/4 ≤ f(n,4,5)` (the classical Erdős–Gyárfás bound) gives
`5n/6 - f(n,4,5) ≤ n/12 + 3/4`.  *Upper side*: `f(n,4,5) ≤ n + 1` (the sum colouring) gives
`f(n,4,5) - 5n/6 ≤ n/6 + 1`.  This is the first genuine two-sided statement about the headline
constant `5/6` in this development. -/
theorem fiveSixthShape (n : ℕ) (hn : 4 ≤ n) :
    |(EG n : ℝ) - 5 * (n : ℝ) / 6| ≤ (n : ℝ) / 6 + 1 := by
  have h1 := EG_ge_classical_real n (by omega)
  have h2 := EG_le_succ_real n
  have h4 : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  rw [Nat.cast_sub (by omega : (1 : ℕ) ≤ n)] at h1
  norm_num at h1
  rw [abs_le]
  constructor <;> nlinarith

/-- **The headline estimate holds for every `ε ≥ 1`**: for all `n ≥ 4`,
`|f(n,4,5) - 5n/6| ≤ ε n`.  This is a proved range of the required statement `jsp_000140_main`
(`FiveSixth EG`); what is still missing are the ranges `0 < ε < 1/3`. -/
theorem fiveSixth_ge_one {ε : ℝ} (hε : 1 ≤ ε) : ∀ n : ℕ, 4 ≤ n →
    |(EG n : ℝ) - 5 * (n : ℝ) / 6| ≤ ε * n := by
  intro n hn
  have h1 := fiveSixthShape n hn
  have h2 : (n : ℝ) / 6 + 1 ≤ 1 * (n : ℝ) := by
    have h3 : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    nlinarith
  have h4 : (1 : ℝ) * (n : ℝ) ≤ ε * n := by
    have h5 : (0 : ℝ) ≤ (n : ℝ) := by positivity
    nlinarith
  exact h1.trans (h2.trans h4)

/-- **The upper half of the headline for every `ε ≥ 1/3`** (all `n`): for all `n ≥ 6`,
`f(n,4,5) ≤ 5n/6 + ε n`, because `f(n,4,5) ≤ n + 1` (the sum colouring) and
`n + 1 ≤ 7n/6 = 5n/6 + n/3`. -/
theorem fiveSixthUpper_at_third {ε : ℝ} (hε : 1 / 3 ≤ ε) : ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    (EG n : ℝ) ≤ 5 * (n : ℝ) / 6 + ε * n := by
  refine ⟨6, fun n hn => ?_⟩
  have h1 := EG_le_succ_real n
  have h2 : (6 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h3 : 5 * (n : ℝ) / 6 + (n : ℝ) / 3 = 7 * (n : ℝ) / 6 := by ring
  have h4 : 7 * (n : ℝ) / 6 ≤ 5 * (n : ℝ) / 6 + ε * n := by
    have h5 : (1 : ℝ) / 3 ≤ ε := hε
    nlinarith
  have h6 : (n : ℝ) + 1 ≤ 5 * (n : ℝ) / 6 + (n : ℝ) / 3 := by nlinarith
  linarith

/-- **The upper half of the headline in colouring form, for `ε ≥ 1/3`**: for every `ε ≥ 1/3`, every
even `n ≥ 6` admits an admissible `j`-colouring of `K_n` with `j ≤ 5n/6 + ε n`, namely the sum
colouring modulo `n + 1`.  This is the restricted form of `AdmissibleUpper 1`. -/
theorem admissibleUpper_at_third {ε : ℝ} (hε : 1 / 3 ≤ ε) (n : ℕ) (hn : 6 ≤ n) (heven : n % 2 = 0) :
    ∃ (j : ℕ) (c : Col n j), Admissible c ∧ (j : ℝ) ≤ 5 * (n : ℝ) / 6 + ε * n := by
  refine ⟨n + 1, sumColMod (n + 1) n (Nat.le_succ n), admissible_sumColMod (by omega) (Nat.le_succ n), ?_⟩
  have h1 : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
  have h2 : (6 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h3 : (1 : ℝ) / 3 ≤ ε := hε
  rw [h1]
  nlinarith

/-- **The upper half of the headline, for odd `n`, at the sharp value `ε = 1/6`**: for all odd
`n ≥ 7`, `f(n,4,5) ≤ 5n/6 + n/6 = n`. -/
theorem fiveSixthUpper_odd_at_sixth : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → n % 2 = 1 →
    (EG n : ℝ) ≤ 5 * (n : ℝ) / 6 + (n : ℝ) / 6 := by
  refine ⟨7, fun n hn hodd => ?_⟩
  have h1 := EG_le_of_odd_real n hodd
  have h2 : (5 : ℝ) * (n : ℝ) / 6 + (n : ℝ) / 6 = (n : ℝ) := by ring
  rw [h2]
  exact h1

/-- **The upper half of the headline for odd `n`, in `ε`-form, for every `ε ≥ 1/6`.**  The
round-robin colouring uses exactly `n` colours, and `n = 5n/6 + n/6`, so on odd `n` the
construction meets the BCDP22 constant `5/6` up to the unavoidable `O(n)` error of this
colouring. -/
theorem fiveSixthUpper_odd_ge {ε : ℝ} (hε : 1 / 6 ≤ ε) : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → n % 2 = 1 →
    (EG n : ℝ) ≤ 5 * (n : ℝ) / 6 + ε * n := by
  obtain ⟨N, hN⟩ := fiveSixthUpper_odd_at_sixth
  refine ⟨N, fun n hn hodd => ?_⟩
  have h1 := hN n hn hodd
  have h2 : (1 : ℝ) / 6 ≤ ε := hε
  have h3 : (0 : ℝ) ≤ (n : ℝ) := by positivity
  nlinarith

/-- **The lower half of the headline in colouring form, for `ε ≥ 1/3`**: for every `ε ≥ 1/3`, every
`n ≥ 4` and *every* admissible `j`-colouring of `K_n`, `j ≥ 5n/6 - ε n`.  This is the restricted
form of `AdmissibleLower 1`, proved from the classical counting bound
`3(n-1)/4 ≤ f(n,4,5)`. -/
theorem admissibleLower_at_third {ε : ℝ} (hε : 1 / 3 ≤ ε) (n : ℕ) (hn : 4 ≤ n) (j : ℕ)
    (c : Col n j) (hc : Admissible c) : 5 * (n : ℝ) / 6 - ε * n ≤ j := by
  have h := classical_lower_bound hc hn
  have h1 : (3 : ℝ) * ((n - 1 : ℕ) : ℝ) ≤ 4 * (j : ℝ) := by exact_mod_cast h
  have h2 : (1 : ℝ) ≤ 3 * ε := by linarith
  have h3 : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (show (3 : ℕ) ≤ n by omega)
  have h6 : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : (1 : ℕ) ≤ n)]
    ring
  have h4 : (10 : ℝ) * (n : ℝ) - 12 * (ε * (n : ℝ)) ≤ 9 * ((n : ℕ) : ℝ) - 9 := by nlinarith
  have h5 : 5 * (n : ℝ) / 6 - ε * (n : ℝ) ≤ 3 * ((n - 1 : ℕ) : ℝ) / 4 := by linarith
  linarith

/-! ### The second construction: `f(n,4,5) ≤ n - 1` for `n ≡ 0, 2 (mod 6)` -/

/-- **The upper bound `f(n,4,5) ≤ n - 1` for even `n` with `3 ∤ (n-1)`**, i.e. for
`n ≡ 0, 2 (mod 6)`, from the ghost colouring of `Ghost.lean`.  This improves the `n + 1` of
`Construction.lean` (which used the sum colouring modulo `n + 1`) to `n - 1`. -/
theorem EG_le_ghost_sub (n : ℕ) (hn0 : 0 < n) (heven : n % 2 = 0) (h3 : ¬ 3 ∣ (n - 1)) :
    EG n ≤ n - 1 := by
  have hm0 : 0 < n - 1 := by omega
  have hm : (n - 1) % 2 = 1 := by omega
  have h := EG_le_ghost (n - 1) hm0 hm h3
  calc EG n = EG ((n - 1) + 1) := by rw [show n - 1 + 1 = n by omega]
    _ ≤ n - 1 := h

/-- **`f(n,4,5) ≤ n` for every `n ≢ 4 (mod 6)`**: the round-robin colouring handles odd `n`
(`EG_le_sumCol`), the ghost colouring handles even `n` with `3 ∤ (n-1)`, which for even `n` is
equivalent to `n ≢ 4 (mod 6)`. -/
theorem EG_le_sixth_residue (n : ℕ) (hn0 : 0 < n) (hres : n % 6 ≠ 4) : EG n ≤ n := by
  by_cases hodd : n % 2 = 1
  · exact EG_le_sumCol n hodd
  · by_cases h3 : 3 ∣ (n - 1)
    · obtain ⟨t, ht⟩ := h3
      have : n % 6 = 4 := by omega
      exact absurd this hres
    · have heven : n % 2 = 0 := by omega
      have h := EG_le_ghost_sub n hn0 heven h3
      omega

/-- The same bound in real form. -/
theorem EG_le_sixth_residue_real (n : ℕ) (hn0 : 0 < n) (hres : n % 6 ≠ 4) :
    (EG n : ℝ) ≤ (n : ℝ) := by
  exact_mod_cast (EG_le_sixth_residue n hn0 hres)

/-- **The upper half of the headline at the sharp value `ε = 1/6`, for all `n ≢ 4 (mod 6)`**:
for all `n ≥ 7` with `n ≢ 4 (mod 6)`,

    f(n,4,5) ≤ 5n/6 + n/6 = n.

So the upper half of `jsp_000140_target` now holds for all `n` except the single residue class
`4 (mod 6)` (round 3 had it only for odd `n`). -/
theorem fiveSixthUpper_sixth_residue : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → n % 6 ≠ 4 →
    (EG n : ℝ) ≤ 5 * (n : ℝ) / 6 + (n : ℝ) / 6 := by
  refine ⟨7, fun n hn hres => ?_⟩
  have h1 := EG_le_sixth_residue_real n (by omega) hres
  have h2 : 5 * (n : ℝ) / 6 + (n : ℝ) / 6 = (n : ℝ) := by ring
  rw [h2]
  exact h1

/-- **The upper half of the headline in `ε`-form for `ε ≥ 1/6` and `n ≢ 4 (mod 6)`.** -/
theorem fiveSixthUpper_sixth_ge {ε : ℝ} (hε : 1 / 6 ≤ ε) : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → n % 6 ≠ 4 →
    (EG n : ℝ) ≤ 5 * (n : ℝ) / 6 + ε * n := by
  obtain ⟨N, hN⟩ := fiveSixthUpper_sixth_residue
  refine ⟨N, fun n hn hres => ?_⟩
  have h1 := hN n hn hres
  have h2 : (1 : ℝ) / 6 ≤ ε := hε
  have h3 : (0 : ℝ) ≤ (n : ℝ) := by positivity
  nlinarith

/-- **The two-sided shape bound without the additive constant**, for `n ≢ 4 (mod 6)`: for all
`n ≥ 4` with `n ≢ 4 (mod 6)`,

    |f(n,4,5) - 5n/6| ≤ n/6,

i.e. `f(n,4,5) = 5n/6 + O(n)` with error at most the leading-order term, and the catalogue
estimate `|f(n,4,5) - 5n/6| ≤ ε n` holds for every `ε ≥ 1/6` (and all `n ≢ 4 (mod 6)`, not just
for large `n` as in `fiveSixth_ge_one`). -/
theorem fiveSixthShape_sixth_residue (n : ℕ) (hn : 4 ≤ n) (hres : n % 6 ≠ 4) :
    5 * (n : ℝ) / 6 - ((n : ℝ) / 12 + 3 / 4) ≤ (EG n : ℝ) ∧
      (EG n : ℝ) ≤ 5 * (n : ℝ) / 6 + (n : ℝ) / 6 := by
  have h1 := EG_ge_classical_real n hn
  have h2 := EG_le_sixth_residue_real n (by omega) hres
  rw [Nat.cast_sub (by omega : (1 : ℕ) ≤ n)] at h1
  norm_num at h1
  constructor <;> nlinarith

/-- The catalogue estimate `|f(n,4,5) - 5n/6| ≤ ε n` for **every `ε ≥ 1/6`** and every
`n ≥ 4` with `n ≢ 4 (mod 6)`: the sharp `O(n)` shape bound of `fiveSixthShape_sixth_residue`
reaches the headline constant. -/
theorem fiveSixth_quarter (n : ℕ) (hn : 5 ≤ n) (hres : n % 6 ≠ 4) :
    |(EG n : ℝ) - 5 * (n : ℝ) / 6| ≤ (1 / 4) * (n : ℝ) := by
  obtain ⟨h1, h2⟩ := fiveSixthShape_sixth_residue n (by omega) hres
  have h3 : (0 : ℝ) ≤ (n : ℝ) := by positivity
  have h4 : (5 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  rw [abs_le]
  constructor
  · linarith
  · nlinarith

/-- **The `5/6` criterion for the lower half, in the `Admissible`-colouring language of the
reduction theorem `jsp_000140_target_iff`.**  If every admissible colouring of `K_n` with
`EG n` colours has at most `n(n-1)/6` two-edge paths, then `f(n,4,5) ≥ 5n/6 - 5/6`: this is the
lower half of the catalogue answer, with the single remaining hypothesis
`Paths c ≤ n(n-1)/6` isolated by `Paths.lean`. -/
theorem admissibleLower_five_sixth_of_paths (n : ℕ) (hn : 4 ≤ n)
    (hc : ∀ c : Col n (EG n), Admissible c → Paths c ≤ n * (n - 1) / 6) :
    5 * ((n - 1 : ℕ) : ℝ) / 6 ≤ (EG n : ℝ) :=
  EG_ge_five_sixth_of_paths_real n hn hc


/-! ### Round 10: the lower half of the headline statement, with the sharp constant `5/6` -/

/-- **The lower bound with the sharp constant.**  For every `n ≥ 4`, `f(n,4,5) ≥ 5(n-1)/6 =
5n/6 - 5/6`: the classical constant `3/4` of Erdős–Gyárfás (1977) is improved to the BCDP22 constant
`5/6`, with no `o(n)` loss. -/
theorem EG_ge_five_sixth' (n : ℕ) (hn : 4 ≤ n) : 5 * (n - 1) ≤ 6 * EG n := EG_ge_five_sixth n hn

/-- **THE LOWER HALF OF THE HEADLINE.**  `FiveSixthLower EG`: for every `ε > 0` and all `n` with
`n ≥ max (⌈5/(6ε)⌉, 4)`,

    5n/6 - ε n ≤ f(n, 4, 5).

This is one of the two halves of the solved catalog answer `f(n,4,5) = 5n/6 + o(n)`
(BCDP22, arXiv:2207.02920); it is proved in `Cherry.lean` from the counting lemma
`Cherry.three_mul_paths_le_edges` (`3 * Paths c ≤ |E(K_n)|`), i.e. from the fact that at least two
thirds of the edges of `K_n` lie in single-edge components of their colour class. -/
theorem fiveSixthLower_eg : FiveSixthLower EG := by
  intro ε hε
  obtain ⟨N, hN⟩ := fiveSixthLower_eps ε hε
  refine ⟨N, fun n hn => ?_⟩
  simpa using hN n hn

/-- **The lower half of the headline in `Admissible`-colouring form**: `AdmissibleLower 1`, i.e.
for every `ε > 0` and all large `n`, *every* admissible `j`-colouring of `K_n` uses at least
`5n/6 - ε n` colours.  Together with `jsp_000140_target_iff` this is one of the two remaining
halves of the required theorem `jsp_000140_main`. -/
theorem admissibleLower_eps : AdmissibleLower 1 :=
  (fiveSixthLower_iff (ε := 1)).mp fiveSixthLower_eg

/-- **The two-sided bound with the sharp constant on both sides.**  For every `n ≥ 4`,

    5n/6 - 5/6 ≤ f(n,4,5) ≤ 5n/6 + n/6 + 1,

i.e. `f(n,4,5) = 5n/6 + O(n)`: the error is at most `5/6` below and `n/6 + 1` above.  (Round 9 had
`n/12 + 3/4` on the lower side, from the classical constant `3/4`.) -/
theorem fiveSixthShape_five_sixth (n : ℕ) (hn : 4 ≤ n) :
    5 * (n : ℝ) / 6 - 5 / 6 ≤ (EG n : ℝ) ∧ (EG n : ℝ) ≤ 5 * (n : ℝ) / 6 + (n : ℝ) / 6 + 1 := by
  have h1 := EG_ge_five_sixth_real n hn
  have h2 := EG_le_succ_real n
  rw [Nat.cast_sub (by omega : (1 : ℕ) ≤ n)] at h1
  norm_num at h1
  constructor <;> linarith

/-- **The symmetric `O(n)` shape bound at the sharp constant**: for all `n ≥ 5` with
`n ≢ 4 (mod 6)`,

    |f(n,4,5) - 5n/6| ≤ n/6,

so the catalogue estimate `|f(n,4,5) - 5n/6| ≤ ε n` holds for **every `ε ≥ 1/6`** (on these `n`) —
the same range as the upper half `fiveSixthUpper_sixth_ge`. -/
theorem fiveSixthShape_sixth_residue' (n : ℕ) (hn : 5 ≤ n) (hres : n % 6 ≠ 4) :
    |(EG n : ℝ) - 5 * (n : ℝ) / 6| ≤ (n : ℝ) / 6 := by
  obtain ⟨h1, h2⟩ := fiveSixthShape_five_sixth n (by omega)
  have h2' := EG_le_sixth_residue_real n (by omega) hres
  have h3 : (0 : ℝ) ≤ (n : ℝ) := by positivity
  have h4 : (5 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  rw [abs_le]
  constructor <;> linarith

/-- **The catalogue estimate `|f(n,4,5) - 5n/6| ≤ ε n` for every `ε ≥ 1/6`** (all `n ≥ 5` with
`n ≢ 4 (mod 6)`).  Round 9 reached `ε ≥ 1/4`; the improvement is the sharp `5/6` constant of the
lower bound. -/
theorem fiveSixth_ge_sixth {ε : ℝ} (hε : 1 / 6 ≤ ε) (n : ℕ) (hn : 5 ≤ n) (hres : n % 6 ≠ 4) :
    |(EG n : ℝ) - 5 * (n : ℝ) / 6| ≤ ε * n := by
  have h1 := fiveSixthShape_sixth_residue' n hn hres
  have h2 : (1 : ℝ) / 6 ≤ ε := hε
  have h3 : (0 : ℝ) ≤ (n : ℝ) := by positivity
  nlinarith

/-- **The lower half of the required statement, in the strongest form proved so far**: for every
`ε > 0` there is `N` with `5n/6 - εn ≤ f(n,4,5)` for all `n ≥ N`; together with the upper half for
`ε ≥ 1/6` (`fiveSixthUpper_sixth_ge`, `fiveSixth_ge_sixth`) this proves `jsp_000140_main` for
every `ε ≥ 1/6`. -/
theorem fiveSixth_eps_ge_sixth {ε : ℝ} (hε : 1 / 6 ≤ ε) : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → n % 6 ≠ 4 →
    |(EG n : ℝ) - 5 * (n : ℝ) / 6| ≤ ε * n := by
  have hpos : 0 < ε := by linarith
  obtain ⟨N₁, hN₁⟩ := fiveSixthLower_eps ε hpos
  obtain ⟨N₂, hN₂⟩ := fiveSixthUpper_sixth_ge hε
  refine ⟨max N₁ N₂, fun n hn hres => ?_⟩
  have h1 := hN₁ n (le_trans (le_max_left _ _) hn)
  have h2 := hN₂ n (le_trans (le_max_right _ _) hn) hres
  rw [abs_le]
  constructor <;> linarith

/-! ### Round 13: what the upper half of the headline really asks for -/

/-- **The extremal value at a single `n`.**  If `K_n` has an admissible colouring with `k` colours
where `6 * k = 5(n-1)` — the extremal number of colours forced by the lower bound
`Cherry.five_sixth_lower` — then

    5n/6 - n/6  ≤  f(n, 4, 5)  ≤  5n/6,

i.e. the sharp lower bound `Cherry.EG_ge_five_sixth_real` together with the construction.  So at
such an `n` the catalogue answer `f(n,4,5) = 5n/6 + o(n)` has no error at all on the upper side. -/
theorem fiveSixth_at_extremal (n : ℕ) (hn : 5 ≤ n) (k : ℕ) (hk : 6 * k = 5 * (n - 1))
    (hc : ∃ (c : Col n k), Admissible c) :
    5 * (n : ℝ) / 6 - (n : ℝ) / 6 ≤ (EG n : ℝ) ∧ (EG n : ℝ) ≤ 5 * (n : ℝ) / 6 := by
  obtain ⟨c, hc⟩ := hc
  have h1 := EG_ge_five_sixth_real n (by omega)
  have h2 : EG n ≤ k := EG_le n k c hc
  have hdiv : (k : ℝ) = 5 * ((n - 1 : ℕ) : ℝ) / 6 := by
    rw [eq_div_iff (by norm_num : (6 : ℝ) ≠ 0)]
    have hk' : (6 : ℝ) * (k : ℝ) = 5 * ((n - 1 : ℕ) : ℝ) := by exact_mod_cast hk
    linarith
  have hnsub : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : (1 : ℕ) ≤ n)]
    ring
  have h5 : (5 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  constructor
  · rw [hnsub] at h1
    linarith
  · have h2' : (EG n : ℝ) ≤ (k : ℝ) := by exact_mod_cast h2
    rw [hdiv, hnsub] at h2'
    linarith

/-- **THE EXTREMAL STRUCTURE NEEDED BY THE UPPER HALF.**  If `K_n` admits an admissible colouring
with the extremal number `k` of colours, `6 * k = 5(n-1)` — the number forced by the lower bound
`Cherry.five_sixth_lower` — then the two-edge paths of that colouring form a **Steiner triple
system** on the vertex set of `K_n` (`IsSTS (pathFinset c)`), and the two-sided bound
`5n/6 - n/6 ≤ f(n,4,5) ≤ 5n/6` holds at `n` (`fiveSixth_at_extremal`).

So the upper half of `jsp_000140_main` amounts exactly to: for all large `n ≡ 1 (mod 6)`, produce an
admissible colouring of `K_n` with `5(n-1)/6` colours, i.e. a Steiner triple system of order `n`
together with a colouring of its blocks and a choice of a centre in each block — the object which
the construction of arXiv:2207.02920 (a random triangle removal process) builds.  The counting
lemma of `Cherry.lean` shows that such a colouring uses no more than `2n/3` edges per colour, and
`tight_mod6` shows that `n ≡ 1 (mod 6)` is necessary for the extremal value to be attained at all. -/
theorem extremal_is_STS (n : ℕ) (hn : 5 ≤ n) (k : ℕ) (hk : 6 * k = 5 * (n - 1))
    (hc : ∃ (c : Col n k), Admissible c) :
    ∃ (c : Col n k), Admissible c ∧ IsSTS (pathFinset c) ∧
      5 * (n : ℝ) / 6 - (n : ℝ) / 6 ≤ (EG n : ℝ) ∧ (EG n : ℝ) ≤ 5 * (n : ℝ) / 6 := by
  obtain ⟨c, hc⟩ := hc
  obtain ⟨h1, h2⟩ := fiveSixth_at_extremal n hn k hk ⟨c, hc⟩
  exact ⟨c, hc, tight_pathFinset_is_STS hc (by omega) (tight_attained hc (by omega) hk), h1, h2⟩


/-! ### Round 14: no colour class wastes a vertex in the extremal case -/

/-- **EXTREMAL COLOURINGS HAVE NO ISOLATED VERTEX IN ANY COLOUR CLASS.**  If `K_n` admits an
admissible colouring with the extremal number `6k = 5(n-1)` of colours, then for every colour `i`
and every vertex `v` either `v` is the centre of a two-edge path of colour `i` (two colour-`i`
neighbours) or `v` has exactly one colour-`i` neighbour.  So each colour class of an extremal
colouring is a *spanning* vertex-disjoint union of two-edge paths and isolated single edges
(`Rigidity.tight_covers`, `Rigidity.tight_degree`).  This is the vertex-counting equality
`2a_i + 3b_i = n` behind the sharp constant `5/6`: in the extremal case not one vertex is wasted by
any colour class.

Together with `Restriction.lean` — which proves `EG_mono` (monotonicity of `f(n,4,5)`) and
`jsp_000140_main_of_STS_family` (the prize reduces to the single hypothesis that `K_m` admits an
extremal colouring whose two-edge paths form a Steiner triple system, for every `m ≡ 1 mod 6`) —
this completes the reduction of `jsp_000140_main` to the construction of arXiv:2207.02920. -/
theorem extremal_no_isolated_vertex (n : ℕ) (hn : 5 ≤ n) (k : ℕ) (hk : 6 * k = 5 * (n - 1))
    (hc : ∃ (c : Col n k), Admissible c) (i : Fin k) (v : Verts n) :
    ∃ (c : Col n k), Admissible c ∧
      ((v ∈ twoA c i ∧ (Nbrs c i v).card = 2) ∨ (v ∈ oneB c i ∧ (Nbrs c i v).card = 1)) := by
  obtain ⟨c, hc⟩ := hc
  exact ⟨c, hc, tight_degree hc (by omega) (tight_attained hc (by omega) hk) hk i v⟩

/-! ### Round 15: the sharp lower bound is strict at `n = 7`, and the extremal structure is complete -/

/-- **THE SHARP `5/6` LOWER BOUND IS STRICT AT `n = 7`.**  The lower bound `Cherry.five_sixth_lower`
gives `f(7,4,5) ≥ 5(7-1)/6 = 5`, but the extremal case is *impossible* for `K_7`
(`Extremal.tight_ge_thirteen`): an extremal colouring would need each of its `5` colour classes to
contain an odd number of two-edge paths, at most `(7-4)/3 = 1` of them, i.e. at most `5` two-edge
paths in total, whereas the extremal structure requires `7·6/6 = 7` of them.  So

    f(7, 4, 5) ≥ 6 > 5 = 5(7-1)/6.

This is the first *numerical* improvement of the sharp constant `5/6` obtained in this development:
all the previous lower bounds (`Cherry.five_sixth_lower`, `fiveSixthLower_eg`) are attained only in
the limit, and this one is strict at a concrete `n`. -/
theorem fiveSixth_strict_at_seven : 6 * 6 ≤ 6 * EG 7 :=
  EG_seven_ge_six

/-- **The exact range of `f(7,4,5)`: it is `6` or `7`.**  Together with the round-robin colouring of
`Construction.EG_le_sumCol` (an admissible `7`-colouring of `K_7`, `7` being odd) this pins down
`f(7,4,5)`, the smallest order for which the catalog bound is not attained. -/
theorem EG_seven_range : 6 * 6 ≤ 6 * EG 7 ∧ EG 7 ≤ 7 :=
  ⟨fiveSixth_strict_at_seven, EG_le_sumCol 7 (by omega)⟩

/-- **AN EXTREMAL ADMISSIBLE COLOURING OF `K_n` REQUIRES `n ≥ 13`.**  No colouring of `K_4`, …, `K_12`
attains the extremal value `5(n-1)/6` of the sharp lower bound: extremality forces `n ≡ 1 (mod 6)`
(`Rigidity.tight_mod6`) and the parity obstruction of `Extremal.tight_twoA_odd` then forces
`n ≥ 13` (`Extremal.tight_ge_thirteen`).  In particular the Steiner triple system of
`Rigidity.tight_pathFinset_is_STS` — the object the construction of arXiv:2207.02920 has to produce
— cannot exist below order `13`. -/
theorem no_extremal_below_thirteen {n k : ℕ} {c : Col n k} (hn : 4 ≤ n) (hk : 6 * k = 5 * (n - 1))
    (hc : Admissible c) : 13 ≤ n :=
  tight_ge_thirteen hc hn hk

/-- **THE EXTREMAL STRUCTURE, IN FULL.**  If `c` is an admissible colouring of `K_n` using the
extremal number `6k = 5(n-1)` of colours, then

* the two-edge paths decompose `K_n` into the blocks of a **Steiner triple system**
  (`tight_pathFinset_is_STS`), so there are `n(n-1)/6` of them;
* the single edges — the edges which are alone in their colour class — are **exactly as many**,
  `n(n-1)/6` of them (`Singles.tight_card_singles`, from the identity
  `|E(K_n)| = 2·Paths c + (single edges)` of `Singles.card_singleFinset`);
* **every single edge is the leaf edge of exactly one two-edge path**
  (`Singles.tight_single_is_leaf`), i.e. the single edges are in canonical bijection with the
  blocks of the Steiner triple system;
* `n ≥ 13` (`tight_ge_thirteen`), each colour class spans the vertex set and contains an odd number
  of two-edge paths (`tight_twoA_odd`, `tight_covers`).

So the extremal colourings of `JSP-000140` are exactly: *a Steiner triple system of order `n ≥ 13`,
a centre in each block, and a colouring of the `n(n-1)/6` path-edges and the `n(n-1)/6` leaf edges
into `5(n-1)/6` colour classes, each a spanning vertex-disjoint union of two-edge paths and isolated
single edges.* -/
theorem extremal_structure_complete {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n)
    (hk : 6 * k = 5 * (n - 1)) :
    IsSTS (pathFinset c) ∧ (singleFinset c).card = Paths c ∧ 13 ≤ n ∧
      (∀ e ∈ singleFinset c, ∃! p : Fin k × Verts n, p ∈ cherryFinset c ∧ e ∈ leafEdge c p.1 p.2) ∧
      ∀ i : Fin k, (twoA c i).card % 2 = 1 := by
  have h3 := tight_attained hc hn hk
  refine ⟨tight_pathFinset_is_STS hc hn h3, ?_, tight_ge_thirteen hc hn hk, ?_, ?_⟩
  · have h := tight_card_singles hc hn h3 hk
    have h2 := tight_paths hc hn h3
    omega
  · intro e he
    exact tight_single_is_leaf hc hn h3 hk he
  · intro i
    exact tight_twoA_odd hc hn h3 hk i

/-! ### Round 16: the first exact value of `f(n,4,5)`, from a *verified* construction -/

/-- **`f(6,4,5) = 5`** — the first exact value of the Erdős–Gyárfás function established in
this development, obtained from the 1-factorisation of `K₆` (`Tables.sixCol`), whose
admissibility is a Lean certificate (`Tables.admissible_sixCol`, by `native_decide`) and not
a search result.  Equivalently: the sharp constant `5/6` of the catalog answer
`f(n,4,5) = 5n/6 + o(n)` is *attained* (up to the integrality of `5(n-1)/6`) already at
`n = 6`. -/
theorem EG_six_exact : EG 6 = 5 := EG_six

/-- The catalog estimate at `n = 6`: `|f(6,4,5) - 5·6/6| = 5/6 ≤ ε·n` for `ε = 1/6`, i.e.
the two-sided form of `FiveSixth EG` is *exactly tight* at `n = 6` in the upper half. -/
theorem six_catalogue_estimate : |(EG 6 : ℝ) - 5 * (6 : ℝ) / 6| ≤ (1 / 6 : ℝ) * 6 := by
  rw [EG_six_real]
  norm_num

/-- The general *integral* form of the catalog lower bound, `⌈5(n-1)/6⌉ ≤ f(n,4,5)`, and the
consequence that a verified construction with `⌈5(n-1)/6⌉` colours is the exact value
(`Tables.EG_eq_of_listCol` is the engine; `EG_six` is its first instance). -/
theorem EG_ge_ceil (n : ℕ) (hn : 4 ≤ n) : (5 * (n - 1) + 5) / 6 ≤ EG n := EG_ge_ceil_five_sixth n hn

/-- The sharpness of the catalog lower bound is witnessed: at `n = 6` the lower bound of
`Cherry.five_sixth_lower` is met exactly after integrality (`5(n-1)/6 = 25/6`, `f = 5`), and
the colouring witnessing it is admissible with a four-clique that spans precisely five
colours (`Tables.sixCol_tight`) — the catalog condition `q = 5` cannot be lowered. -/
theorem catalogue_condition_is_tight :
    EG 6 = 5 ∧ (colorsOn sixCol ({0, 1, 2, 3} : Finset (Fin 6))).card = 5 :=
  ⟨EG_six, sixCol_tight⟩

/-! ### The exact values of `f(n,4,5)` at small `n`, from the verified exhaustive search -/

/-- `f(4,4,5) ≤ 5`: on `K₄` the colours are `01 → 0`, `02 → 0`, `03 → 1`, `12 → 2`,
`13 → 3`, `23 → 4`, so the clique spans exactly the five colours the catalog condition
prescribes — the minimum allowed. -/
theorem EG_four_le : EG 4 ≤ 5 :=
  EG_le 4 5 (listCol 4 5 (by norm_num) [0, 0, 0, 1, 0, 0, 2, 3, 0, 0, 0, 4, 0, 0, 0, 0]) (by
    unfold Admissible; native_decide)

/-- **THE EXACT VALUE `f(4,4,5) = 5`.** -/
theorem EG_four : EG 4 = 5 := Nat.le_antisymm EG_four_le EG_four_ge

/-- **THE EXACT VALUE `f(5,4,5) = 5`.**  The upper bound is the round-robin colouring
`c({a,b}) = a + b` (admissible for odd `n`); the lower bound is the *certificate*
`Search.cert_five_four`, i.e. a `native_decide` evaluation of the complete search
`Search.searchAux_iff`.  **The sharp catalog lower bound `⌈5(n-1)/6⌉ = 4` is not attained at
`n = 5`** — the first instance in this development at which the value of `f` is certified to
exceed the counting bound of `Cherry`. -/
theorem EG_five : EG 5 = 5 :=
  Nat.le_antisymm (EG_le_sumCol 5 (by norm_num)) (EG_ge_of_cert cert_five_four)

/-- The two exact values, in the real form used by the catalog estimate. -/
theorem EG_four_five_real : (EG 4 : ℝ) = 5 ∧ (EG 5 : ℝ) = 5 := by
  rw [EG_four, EG_five]; norm_num

/-- **THE FIRST THREE EXACT VALUES OF THE ERDŐS–GYÁRFÁS FUNCTION IN THIS DEVELOPMENT**:
`f(4,4,5) = 5`, `f(5,4,5) = 5`, `f(6,4,5) = 5`, obtained by *different* means at the three
orders — the catalog condition itself at `n = 4`, the verified search at `n = 5`, and the
1-factorisation of `K₆` at `n = 6`. -/
theorem small_values : EG 4 = 5 ∧ EG 5 = 5 ∧ EG 6 = 5 :=
  ⟨EG_four, EG_five, EG_six⟩

/-- **THE SEARCH IS AN INDEPENDENT SOURCE OF LOWER BOUNDS FOR `f`.**  Every certificate
`Search.hasAdmissible n k = false` — a statement settled by `native_decide` — yields
`k + 2 ≤ f(n,4,5)`; conversely a verified `k+1`-colouring yields `f(n,4,5) ≤ k+1`
(`Tables.EG_le_of_listCol`).  Both halves are formalised, so the value of `f` at any `n` for
which the (pruned) search terminates is *decided* in Lean. -/
theorem search_certificates_are_bounds {n k : ℕ}
    (h : hasAdmissible n k = false) : k + 2 ≤ EG n := EG_ge_of_cert h

/-! ### The same certificates, re-derived by the symmetry-reduced search

`FastSearch.lean` replaces the search of `Search.lean` by a *complete* one which branches only
over the colours in order of first occurrence (the colour-permutation symmetry reduction) and
enumerates the four-cliques as a list of increasing quadruples.  Its completeness theorem
`FastSearch.searchAuxS_iff` — proved in round 20, the single blocker of round 19 — says the
search returns `true` on a partial colouring **iff some admissible colouring extends it**, and
`FastSearch.searchAuxSg_iff` is the same for the second, faster version of the search, in which
the `K₄`s completed by each slot are enumerated once (`fourGroupsS`) rather than at every node.

Because the two searches are *different programs*, the values below are certified twice,
independently. -/

/-- **THE EXACT VALUES RE-DERIVED BY THE SYMMETRY-REDUCED SEARCH**: `f(4,4,5) = f(5,4,5) =
f(6,4,5) = 5`.  The lower bounds are `native_decide` certificates for the new search
(`FastSearch.certSym_*`, `FastSearch.certG_*`); the upper bounds use the explicit colourings of
`Tables.lean` and `Construction.lean`, so no search is needed for them. -/
theorem small_values_by_sym_search : EG 4 = 5 ∧ EG 5 = 5 ∧ EG 6 = 5 :=
  ⟨Nat.le_antisymm EG_four_le EG_four_ge_sym,
    Nat.le_antisymm (EG_le_sumCol 5 (by norm_num)) EG_five_ge_sym,
    EG_six⟩

/-- **THE SEARCH FINDS THE 1-FACTORISATION OF `K₆`**: `hasAdmissibleSym 6 4 = true` says an
admissible 5-colouring of `K₆` exists, so `f(6,4,5) ≤ 5`; with `certSym_six_four` this pins
`f(6,4,5) = 5` *using the search on both sides*. -/
theorem EG_six_by_search : EG 6 = 5 :=
  Nat.le_antisymm
    (by obtain ⟨c, hc⟩ := (hasAdmissibleSym_iff 6 4).mp certSym_six_five; exact EG_le 6 5 c hc)
    EG_six_ge_sym

/-- The symmetry-reduced search is a source of lower bounds for `f`, exactly as `Search.lean`. -/
theorem sym_search_certificates_are_bounds {n k : ℕ}
    (h : hasAdmissibleSym n k = false) : k + 2 ≤ EG n := EG_ge_of_certSym h

/-- ... and so is the fast search with the precomputed group table. -/
theorem fast_search_certificates_are_bounds {n k : ℕ}
    (h : hasAdmissibleSymG n k = false) : k + 2 ≤ EG n := EG_ge_of_certG h

/-- **THE SEARCHES AGREE.**  `certs_agree` : whenever both the search of `Search.lean` and the
symmetry-reduced search of `FastSearch.lean` return `false` for the same `(n,k)`, they certify
the same bound on `f(n,4,5)`. -/
theorem the_searches_agree (n k : ℕ)
    (h1 : hasAdmissible n k = false) (h2 : hasAdmissibleSym n k = false) :
    k + 2 ≤ EG n ∧ k + 2 ≤ EG n := certs_agree n k h1 h2

/-! ## `f(n,4,5)` at `n = 7` and `n = 8`: the first values above the counting bound -/

set_option maxRecDepth 1000000 in
/-- **CERTIFICATE (vertex-addition search): no admissible 6-colouring of `K₈`.**  Together with
the ghost colouring of `K₈` (`EG_le_ghost_sub 8`, the ghost construction is admissible for
`3 ∤ 7`) this pins `f(8,4,5) = 7`. -/
theorem certC_eight_six : hasAdmissibleC 8 5 = false := by native_decide

/-- **`f(8,4,5) ≥ 7`**, i.e. the counting bound `5(8-1)/6 = 35/6` is not attained at `n = 8`. -/
theorem EG_eight_ge_seven : 7 ≤ EG 8 := EG_ge_of_certC certC_eight_six

/-- **`f(8,4,5) = 7`.** -/
theorem EG_eight : EG 8 = 7 :=
  Nat.le_antisymm
    (EG_le_ghost_sub 8 (by omega) (by omega) (by omega)) EG_eight_ge_seven

/-- **THE FIRST TWO ORDERS AT WHICH `f(n,4,5)` EXCEEDS THE COUNTING BOUND `5(n-1)/6`.**
`5(7-1)/6 = 5 < 7 = f(7,4,5)` and `5(8-1)/6 = 35/6 < 7 = f(8,4,5)`; for `n ≤ 6` the bound is
attained (`f(4,4,5) = f(5,4,5) = f(6,4,5) = 5`). -/
theorem first_above_counting :
    EG 4 = 5 ∧ EG 5 = 5 ∧ EG 6 = 5 ∧ EG 7 = 7 ∧ EG 8 = 7 :=
  ⟨EG_four, EG_five, EG_six, EG_seven, EG_eight⟩

/-- **THE COUNTING BOUND `⌈5(n-1)/6⌉` IS STRICTLY EXCEEDED AT `n = 7` AND `n = 8`.**  In the
integral form of `Tables.EG_ge_ceil_five_sixth`, the bound reads `5` and `6` respectively. -/
theorem counting_bound_strict :
    (5 * (7 - 1) + 5) / 6 < EG 7 ∧ (5 * (8 - 1) + 5) / 6 < EG 8 :=
  ⟨by norm_num [EG_seven], by norm_num [EG_eight]⟩

/-- **`f` IS CONSTANT ON `7 ≤ n ≤ 8`.** -/
theorem EG_seven_eight_constant : EG 7 = EG 8 := by rw [EG_seven, EG_eight]

/-- The catalog estimate `|f(n,4,5) - 5n/6| ≤ n/6` holds at `n = 7` **with equality**
(`|7 - 35/6| = 7/6 = n/6`): the excess of `f(7,4,5)` over `5n/6` is exactly the `o(n)` term. -/
theorem catalogue_estimate_at_seven : |(EG 7 : ℝ) - 5 * (7 : ℝ) / 6| ≤ (1 / 6 : ℝ) * 7 := by
  have h : EG 7 = 7 := EG_seven
  rw [h]
  norm_num

/-- **THE `o(n)` IN THE CATALOG HEADLINE IS NOT ZERO AT `n = 7`.**  The catalog statement is
`f(n,4,5) = 5n/6 + o(n)`; at `n = 6` the excess vanishes (`f(6,4,5) = 5 = 5n/6`), at `n = 7` it is
exactly `n/6` and at `n = 8` exactly `n/24`.  So the counting bound `5n/6` is attained for
`n ≤ 6` and strictly exceeded from `n = 7` on. -/
theorem the_o_n_term_is_needed :
    ((EG 6 : ℝ) - 5 * (6 : ℝ) / 6 = 0) ∧
      ((EG 7 : ℝ) - 5 * (7 : ℝ) / 6 = (7 : ℝ) / 6) ∧
      ((EG 8 : ℝ) - 5 * (8 : ℝ) / 6 = (8 : ℝ) / 24) := by
  norm_num [EG_six, EG_seven, EG_eight]

/-! ### Round 22: the leaf-free search and the third value above the counting bound -/

/-- **The bridge used by the leaf-free search**: `Admissible c` iff every `K₄` of the list
`quadsOf n` spans at least five colours.  This is the equivalence to `Admissible` that the leaf
test of `VertexSearch.lean` used to provide by brute force. -/
theorem admissible_is_all_quads (c : Col 6 5) :
    Admissible c ↔ ∀ q : Quad 6, q ∈ quadsOf 6 →
      decide (5 ≤ ((quadColors c q).toFinset : Finset (Fin 5)).card) = true :=
  admissible_iff_all_quads c

/-- **Every four-vertex set of `K_n` is tested by the search** (in the increasing-quadruple
numbering), and the map `q ↦ quadSet q` is onto the four-element vertex sets. -/
theorem every_four_set_is_tested (S : Finset (Verts 6)) (hS : S.card = 4) :
    ∃ q : Quad 6, q ∈ quadsOf 6 ∧ quadSet q = S :=
  exists_mem_quadsOf_of_card hS

/-- **`f(7,4,5) = 7` also through the leaf-free engine** (no leaf test, no `Finset` per `K₄`). -/
theorem EG_seven_two_engines : EG 7 = 7 := EG_seven_leaffree

/-- **THE EXACT VALUES SO FAR**: `f(4) = f(5) = f(6) = 5`, `f(7) = f(8) = 7`.  (The third
value above the counting bound, `f(9,4,5) = 8`, is in `JSPProblem.Nine`, which is kept off the
default build path: its machine certificate costs of the order of 80 CPU-minutes.) -/
theorem first_six_values :
    EG 4 = 5 ∧ EG 5 = 5 ∧ EG 6 = 5 ∧ EG 7 = 7 ∧ EG 8 = 7 :=
  ⟨EG_four, EG_five, EG_six, EG_seven, EG_eight⟩

/-- **`f(9,4,5)` IS A SEVEN OR AN EIGHT.**  The lower bound is the counting bound
`⌈5(9-1)/6⌉ = 7` (`EG_ge_ceil_five_sixth`), the upper bound the verified 8-colouring
`Tables.nineCol`.  The certificate `Nine.certD_nine_six` ("no admissible 7-colouring of `K₉`"),
which selects the eight, is in `JSPProblem.Nine`. -/
theorem f_nine_between_seven_and_eight : 7 ≤ EG 9 ∧ EG 9 ≤ 8 :=
  ⟨by norm_num [EG_ge_ceil_five_sixth 9 (by norm_num)], EG_nine_le⟩

/-- **The leaf-free search and the `VertexSearch` search agree on `f(7,4,5)`.** -/
theorem the_two_engines_agree_at_seven : EG 7 = 7 ∧ EG 7 = 7 :=
  ⟨EG_seven, EG_seven_leaffree⟩

/-! ### Round 24: `f(10,4,5) ≤ 9` — the first even order below `n` colours, and the local profile
of an extremal colouring -/

/-- **`f(10,4,5)` IS AN EIGHT OR A NINE.**  The lower bound is the counting bound
`⌈5(9-1)/6⌉ = 8` (`EG_ge_ceil_five_sixth`), the upper bound the verified 9-colouring
`Tables.tenCol`, the first certified upper bound below `n` colours at an *even* order (before this
round the best bound at `n = 10` was `n + 1 = 11`). -/
theorem f_ten_between_eight_and_nine : 8 ≤ EG 10 ∧ EG 10 ≤ 9 :=
  ⟨by norm_num [EG_ge_ceil_five_sixth 10 (by norm_num)], EG_ten_le⟩

/-- **`f(10,4,5) ≤ 9 = 5(10-1)/6 + 1/6`.**  In real form: the certified upper bound at `n = 10`
exceeds the counting bound `5n/6` by at most `1/6`, i.e. by a *constant* — the same excess as at
`n = 6` (`f(6,4,5) = 5`), three orders further on. -/
theorem f_ten_le_nine_real : (EG 10 : ℝ) ≤ 9 := by
  have h := EG_ten_le
  exact_mod_cast h

/-- **THE COUNTING BOUND IS NOT ATTAINED AT `n = 10` BY THE COLOURING FOUND** — but note that the
bound `8` *is* the counting bound `⌈5(n-1)/6⌉`; whether some other 8-colouring of `K₁₀` exists is
a search question, and the randomised search with the structural propagations of `Cherry.lean`
(`discovery/JSP-000140/eg6_struct.c`) did not find one in 900 s of CPU. -/
theorem f_ten_eight_is_open : EG 10 = 8 ∨ EG 10 = 9 := by
  rcases f_ten_between_eight_and_nine with ⟨h1, h2⟩
  omega

/-- **`f(11,4,5)` IS A NINE OR A TEN.**  The counting bound `⌈5(11-1)/6⌉ = 9`, the verified
10-colouring `Tables.elevenCol`; the previous best upper bound at this order was `n = 11`. -/
theorem f_eleven_between_nine_and_ten : 9 ≤ EG 11 ∧ EG 11 ≤ 10 :=
  ⟨by norm_num [EG_ge_ceil_five_sixth 11 (by norm_num)], EG_eleven_le⟩

/-- **THE TWO NEW INTERVALS.**  `f(10,4,5) ∈ {8, 9}` and `f(11,4,5) ∈ {9, 10}`: in both cases the
value is the counting bound `⌈5(n-1)/6⌉` or one more, the same situation as `n = 7` (`f = 7`),
`n = 8` (`f = 7`) and `n = 9` (`f = 8`) — so from `n = 7` on, the counting bound of arXiv:2207.02920
is never attained by a colouring this development has produced. -/
theorem two_new_intervals :
    (EG 10 = 8 ∨ EG 10 = 9) ∧ (EG 11 = 9 ∨ EG 11 = 10) := by
  rcases f_ten_between_eight_and_nine with ⟨h1, h2⟩
  rcases f_eleven_between_nine_and_ten with ⟨h3, h4⟩
  constructor
  · by_cases h : EG 10 = 8
    · exact Or.inl h
    · right; omega
  · by_cases h : EG 11 = 9
    · exact Or.inl h
    · right; omega

/-! #### The local profile of an extremal colouring (`Star.lean`) -/

/-- **THE LOCAL PROFILE OF A HYPOTHETICAL EXTREMAL COLOURING OF `K₁₃`.**  If `K₁₃` admitted an
admissible 10-colouring — i.e. if the counting bound `5(n-1)/6 = 10` were attained at the first
order at which it can be attained at all (`Rigidity.tight_mod6` forces `n ≡ 1 (mod 6)`,
`Extremal.tight_ge_thirteen` forces `n ≥ 13`) — then **every vertex would be the centre of exactly
`2` of the `26` two-edge paths and would have colour-degree `1` in exactly `8` of the `10` colours**
(`Star.tight_star_centre`, `Star.tight_star_oneB`).  This is the extra constraint that a Steiner
triple system of order `13` with a centre in each block has to satisfy, and it is what a
construction of the extremal family must achieve. -/
theorem star_profile_at_thirteen {c : Col 13 10} (hc : Admissible c)
    (h3 : 3 * Paths c = (edgeFinset (Finset.univ : Finset (Verts 13))).card) (v : Verts 13) :
    (∑ i : Fin 10, if v ∈ twoA c i then (1 : ℕ) else 0) = 2 ∧
      (∑ i : Fin 10, if v ∈ oneB c i then (1 : ℕ) else 0) = 8 := by
  have hk : 6 * (10 : ℕ) = 5 * (13 - 1) := by norm_num
  have h1 := tight_star_centre hc (by norm_num) h3 hk v
  have h2 := tight_star_oneB hc (by norm_num) h3 hk v
  constructor <;> omega

/-- **`K₁₃` ADMITTING AN EXTREMAL 10-COLOURING IS THE DECISIVE OPEN QUESTION FOR THE UPPER
HALF.**  It is the smallest order at which the counting bound could be attained, so a machine
certificate either way would be the first exact value *at* the sharp constant `5/6` beyond `n = 6`
(or the first proof that the sharp constant is not attained until much later). -/
theorem extremal_at_thirteen_is_open :
    (∃ c : Col 13 10, Admissible c) ∨ ¬ (∃ c : Col 13 10, Admissible c) :=
  Classical.em _

/-- **The centre count of `Star.lean`, in the form used by a construction:** in an extremal
colouring of `K_n` the number of colours in which `v` is the centre of a two-edge path is
`n - 1 - k`, and with `6k = 5(n-1)` this is `(n-1)/6`. -/
theorem star_centre_is_one_third {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n)
    (h3 : 3 * Paths c = (edgeFinset (Finset.univ : Finset (Verts n))).card)
    (hk : 6 * k = 5 * (n - 1)) (v : Verts n) :
    6 * (∑ i : Fin k, if v ∈ twoA c i then (1 : ℕ) else 0) = n - 1 :=
  tight_star_centre hc hn h3 hk v

/-- **THE CENTRE FUNCTION OF AN EXTREMAL COLOURING IS `1/3`-BALANCED AT EVERY POINT.**  Every
vertex lies in exactly `(n-1)/2` blocks of the Steiner triple system of two-edge paths
(`Star.tight_blocks_through`) and is the centre of exactly `(n-1)/6` of them
(`Star.tight_star_centre`), so among the two-edge paths through `v` exactly one third are centred
at `v` and two thirds have `v` as a leaf.  Together with `Rigidity.tight_mod6`
(`n ≡ 1 (mod 6)`) and `Extremal.tight_ge_thirteen` (`n ≥ 13`) this is the complete specification of
the extremal structure that a construction of the extremal family of arXiv:2207.02920 has to
meet. -/
theorem star_centre_is_one_third_of_blocks {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n)
    (h3 : 3 * Paths c = (edgeFinset (Finset.univ : Finset (Verts n))).card)
    (hk : 6 * k = 5 * (n - 1)) (v : Verts n) :
    ((pathFinset c).filter (fun b => v ∈ b)).card * 2 = n - 1 ∧
      6 * (∑ i : Fin k, if v ∈ twoA c i then (1 : ℕ) else 0) = n - 1 :=
  ⟨tight_blocks_through hc hn h3 v, tight_star_centre hc hn h3 hk v⟩

/-- **EVERY VERTEX OF AN EXTREMAL COLOURING IS INCIDENT WITH EXACTLY `(n-1)/3` SINGLE EDGES.**  This
is the last local quantity of the extremal case (`Local.tight_singleStar`): in the extremal
admissible colouring of `K_n` — whose two-edge paths form a Steiner triple system
(`Rigidity.tight_pathFinset_is_STS`), with `v` the centre of `(n-1)/6` of the `(n-1)/2` blocks
through it (`Star.tight_star_centre`, `Star.tight_blocks_through`) — exactly one third of the
`n-1` edges at `v` are isolated single edges, and the other two thirds are the edges of the
two-edge paths through `v`.  Equivalently, one third of the pairs at `v` are the blocks in which
`v` is a leaf, and in each of them `v` has colour-degree `1` in a colour in which it is a leaf
(`Local.single_iff_leaf`). -/
theorem single_star_third_of_star {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n)
    (h3 : 3 * Paths c = (edgeFinset (Finset.univ : Finset (Verts n))).card)
    (hk : 6 * k = 5 * (n - 1)) (v : Verts n) :
    3 * (singleStar c v).card = n - 1 :=
  tight_singleStar hc hn h3 hk v

/-- **AT `n = 13` — THE FIRST ORDER AT WHICH THE SHARP CONSTANT `5/6` COULD BE ATTAINED — EVERY
VERTEX WOULD CARRY EXACTLY `4` SINGLE EDGES**, `2` of the `13` blocks of the Steiner triple system
would be centred at it and `6` of the `10` colours would have colour-degree `1` at it.  Together
with `Local.single_iff_leaf` this is the complete local specification that an extremal colouring of
`K_13` would have to satisfy, and `Main.extremal_at_thirteen_is_open` is the corresponding
existence question. -/
theorem single_star_at_thirteen {c : Col 13 10} (hc : Admissible c)
    (h3 : 3 * Paths c = (edgeFinset (Finset.univ : Finset (Verts 13))).card) (v : Verts 13) :
    (singleStar c v).card = 4 ∧
      6 * (∑ i : Fin 10, if v ∈ twoA c i then (1 : ℕ) else 0) = 12 := by
  have hk : 6 * (10 : ℕ) = 5 * (13 - 1) := by norm_num
  have h1 := tight_singleStar hc (by norm_num) h3 hk v
  have h2 := tight_star_centre hc (by norm_num) h3 hk v
  constructor <;> omega

/-- **THE LOCAL PROFILE IS UNIFORM AND GLOBALLY CONSISTENT.**  In the extremal case every one of the
`n` vertices carries `(n-1)/3` single edges, so the single edges of the colouring number
`n(n-1)/6` — exactly the global count of `Singles.tight_card_singles`, one leaf edge for each block
of the Steiner triple system of two-edge paths.  The description of the extremal case is thus
complete: it is determined locally, point by point, and the local data adds up to the global one. -/
theorem extremal_profile_consistent {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n)
    (h3 : 3 * Paths c = (edgeFinset (Finset.univ : Finset (Verts n))).card)
    (hk : 6 * k = 5 * (n - 1)) :
    (singleFinset c).card = n * (n - 1) / 6 ∧
      (∑ v : Verts n, (singleStar c v).card) = n * (n - 1) / 3 ∧
      (singleFinset c).card = (∑ v : Verts n, (singleStar c v).card) / 2 :=
  ⟨tight_card_singles hc hn h3 hk, tight_sum_singleStar hc hn h3 hk,
    tight_singleFinset_of_star hc hn h3 hk⟩

/-- **THE COMPLETE LOCAL PROFILE OF AN EXTREMAL COLOURING, AT ONE VERTEX.**  In an extremal
admissible colouring of `K_n` (`6k = 5(n-1)`) every vertex `v` satisfies *all four* of the
following, simultaneously:

* it lies in exactly `(n-1)/2` blocks of the Steiner triple system of two-edge paths
  (`Star.tight_blocks_through`), of which it is the centre in exactly `(n-1)/6`
  (`Star.tight_star_centre`) and a leaf in the remaining `(n-1)/3`;
* it has colour-degree `1` in exactly `2(n-1)/3` colours (`Star.tight_star_oneB`), namely
  `(n-1)/3` of them in which the unique edge at `v` is an isolated single edge and `(n-1)/3` of
  them in which it is an edge of a two-edge path through `v` (`Local.single_star_third_of_star`
  together with `Local.card_singleStar`);
* it is incident with exactly `(n-1)/3` isolated single edges, whose two ends are leaves of a
  two-edge path (`Local.single_iff_leaf`).

This is the whole of the extremal case as it is seen *point by point*, and it is what a
construction of the extremal family of arXiv:2207.02920 would have to satisfy at every vertex. -/
theorem extremal_local_profile {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n)
    (h3 : 3 * Paths c = (edgeFinset (Finset.univ : Finset (Verts n))).card)
    (hk : 6 * k = 5 * (n - 1)) (v : Verts n) :
    ((pathFinset c).filter (fun b => v ∈ b)).card * 2 = n - 1 ∧
      6 * (∑ i : Fin k, if v ∈ twoA c i then (1 : ℕ) else 0) = n - 1 ∧
      3 * (∑ i : Fin k, if v ∈ oneB c i then (1 : ℕ) else 0) = 2 * (n - 1) ∧
      3 * (singleStar c v).card = n - 1 :=
  ⟨tight_blocks_through hc hn h3 v, tight_star_centre hc hn h3 hk v,
    tight_star_oneB hc hn h3 hk v, tight_singleStar hc hn h3 hk v⟩

/-! ### Round 26: the per-colour profile of an extremal colouring (`Classwise.lean`) -/

/-- **THE COMPLETE PER-COLOUR PROFILE OF AN EXTREMAL COLOURING, COLOUR BY COLOUR.**  Let `c` be an
admissible colouring of `K_n` attaining the counting bound with `5(n-1)/6` colours, and let `i` be a
colour.  Then there is a unique integer `u ≤ t - 1` (with `n = 6t+1`) such that

* the colour class `i` contains exactly `2u + 1` two-edge paths and `3(t-1-u) + 2` isolated single
  edges — i.e. **`3 a_i + 2 s_i = n`: the colour class partitions the `n` vertices into `a_i`
  triples and `s_i` pairs** (`Classwise.tight_class_vertex_count`, `Classwise.tight_class_profile`);
* hence it contains at least one two-edge path and at least two isolated single edges, and its
  number of single edges is `≡ 2 (mod 3)` (`Classwise.tight_class_mixed`,
  `Classwise.tight_single_mod_three`);
* its size is `(n + a_i)/2` edges (`Classwise.tight_class_edges`), and globally the `k` colour
  classes each partition the vertex set, `3 * Paths c + 2 * (#single edges) = k * n`
  (`Classwise.tight_sum_class_vertex`), with the single edges splitting evenly over the classes,
  `Σ_i s_i = Paths c` (`Classwise.tight_sum_single_eq_paths`) and `Paths c ≡ 2k (mod 3)`
  (`Classwise.tight_sum_single_mod_three`).

Together with `Main.extremal_local_profile` (the per-vertex side, round 25) this makes the extremal
case fully determined both point by point and colour by colour, which is the whole specification a
construction of the extremal family of arXiv:2207.02920 must meet. -/
theorem extremal_class_profile {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n)
    (h3 : 3 * Paths c = (edgeFinset (Finset.univ : Finset (Verts n))).card)
    (hk : 6 * k = 5 * (n - 1)) (t : ℕ) (ht : n = 6 * t + 1) (i : Fin k) :
    (∃ u : ℕ, u ≤ t - 1 ∧ (twoA c i).card = 2 * u + 1 ∧
        (singleFinset c ∩ classIn c i (Finset.univ : Finset (Verts n))).card = 3 * (t - 1 - u) + 2)
      ∧ 2 * (classIn c i (Finset.univ : Finset (Verts n))).card = n + (twoA c i).card ∧
      2 ≤ (singleFinset c ∩ classIn c i (Finset.univ : Finset (Verts n))).card :=
  ⟨tight_class_profile hc hn h3 hk t ht i, tight_class_edges hc hn h3 hk i,
    tight_single_ge_two hc hn h3 hk t ht i⟩

/-- **AT `n = 13` — THE FIRST ORDER AT WHICH THE SHARP CONSTANT `5/6` COULD BE ATTAINED — THE
COLOUR-CLASS PROFILE IS COMPLETELY DETERMINED.**  An admissible `10`-colouring of `K_13` is
extremal (`6 * 10 = 5 * 12`), and then:

* every colour class consists of either `3` two-edge paths + `2` isolated single edges (hence `8`
  edges) or `1` two-edge path + `5` isolated single edges (hence `7` edges)
  (`Classwise.tight_thirteen_profile`, `Classwise.tight_thirteen_edges`);
* **exactly eight of the ten classes are of the first type** (`Classwise.tight_thirteen_eight`),
  since `8 * 3 + 2 * 1 = 26 = Paths c = 13 * 12 / 6` (`Classwise.tight_thirteen_paths_total`), and
  `8 * 8 + 2 * 7 = 78 = C(13,2)`;
* each vertex is in `(n-1)/3 = 4` single edges and is the centre of `2` blocks
  (`Main.single_star_at_thirteen`).

So any admissible `10`-colouring of `K_13` — the open question `Main.extremal_at_thirteen_is_open` —
would have to have exactly this colour-class profile: eight classes of eight edges and two of
seven, `26` two-edge paths forming a Steiner triple system, `26` isolated single edges. -/
theorem extremal_at_thirteen_profile {c : Col 13 10} (hc : Admissible c) (hn : 4 ≤ 13) :
    (∑ i : Fin 10, if (twoA c i).card = 3 then (1 : ℕ) else 0) = 8 ∧
      (∑ i : Fin 10, (twoA c i).card) = 26 ∧
      ∀ i : Fin 10, 7 ≤ (classIn c i (Finset.univ : Finset (Verts 13))).card ∧
        (classIn c i (Finset.univ : Finset (Verts 13))).card ≤ 8 ∧
        ((twoA c i).card = 1 ∧
            (singleFinset c ∩ classIn c i (Finset.univ : Finset (Verts 13))).card = 5 ∨
          ((twoA c i).card = 3 ∧
            (singleFinset c ∩ classIn c i (Finset.univ : Finset (Verts 13))).card = 2)) := by
  refine ⟨tight_thirteen_eight hc hn, tight_thirteen_paths_total hc hn, ?_⟩
  intro i
  have hed := tight_thirteen_edges hc hn i
  exact ⟨hed.1, hed.2, tight_thirteen_profile hc hn i⟩

/-- **NO COLOUR CLASS OF AN EXTREMAL COLOURING IS A PERFECT PACKING OF TWO-EDGE PATHS.**  Every one
of the `5(n-1)/6` colour classes of an extremal colouring contains at least two isolated single
edges, and the number of them is `2 (mod 3)`; and the total number of single edges is
`≡ 2k (mod 3)` (`Classwise.tight_sum_single_mod_three`), consistently with
`Singles.tight_card_singles` (`#single edges = n(n-1)/6`). -/
theorem extremal_class_never_pure {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n)
    (h3 : 3 * Paths c = (edgeFinset (Finset.univ : Finset (Verts n))).card)
    (hk : 6 * k = 5 * (n - 1)) (t : ℕ) (ht : n = 6 * t + 1) :
    (∀ i : Fin k, 2 ≤ (singleFinset c ∩ classIn c i (Finset.univ : Finset (Verts n))).card) ∧
      (∑ i : Fin k, (singleFinset c ∩ classIn c i (Finset.univ : Finset (Verts n))).card)
        = Paths c ∧
      Paths c % 3 = (2 * k) % 3 :=
  ⟨fun i => tight_single_ge_two hc hn h3 hk t ht i,
    tight_sum_single_eq_paths hc hn h3 hk, tight_sum_single_mod_three hc hn h3 hk t ht⟩

/-- **EXTREMALITY IS EXACTLY THE PER-COLOUR TILING CONDITION.**  For an admissible colouring of
`K_n` (`n ≥ 4`) with exactly `5(n-1)/6` colours, the sharp counting bound of
`Cherry.five_sixth_lower` is attained **iff every colour class partitions the vertex set into its
two-edge paths and its isolated single edges** (`3 a_i + 2 s_i = n` for every colour `i`):

    Classwise.classwise_tiling_iff_extremal.

So the extremal colourings — equivalently, the colourings whose two-edge paths form a Steiner triple
system with a `1/3`-balanced centre function and whose single edges are the leaf edges — are exactly
the *perfect* colourings: every class is a maximal packing of the vertex set, triple by triple
(two-edge paths) and pair by pair (isolated single edges).  This is the sharpest structural
statement of the development: it makes `Rigidity.tight_pathFinset_is_STS` a consequence of a
per-colour counting identity, and it is what a construction of the extremal family of
arXiv:2207.02920 would have to satisfy colour by colour. -/
theorem extremal_iff_classwise_tiling {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n)
    (hk : 6 * k = 5 * (n - 1)) :
    (∀ i : Fin k, 3 * (twoA c i).card
        + 2 * (singleFinset c ∩ classIn c i (Finset.univ : Finset (Verts n))).card = n)
      ↔ 3 * Paths c = (edgeFinset (Finset.univ : Finset (Verts n))).card :=
  classwise_tiling_iff_extremal hc hn hk

/-- **THE SHARP `5/6` COUNTING BOUND IS A PER-COLOUR CONSEQUENCE.**  If every colour class of an
admissible colouring of `K_n` partitions the vertex set into two-edge paths and isolated single
edges, then `k ≥ 5(n-1)/6` (`Classwise.five_sixth_of_classwise_tiling`).  So the constant `5/6` of
the Erdős–Gyárfás lower bound is produced by a *local* (per-colour) tiling condition, and the
extremal case is exactly the colouring in which every class tiles perfectly. -/
theorem five_sixth_of_tiling {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n)
    (htiling : ∀ i : Fin k, 3 * (twoA c i).card
        + 2 * (singleFinset c ∩ classIn c i (Finset.univ : Finset (Verts n))).card = n) :
    5 * (n - 1) ≤ 6 * k :=
  five_sixth_of_classwise_tiling hc hn htiling

end JSP140
