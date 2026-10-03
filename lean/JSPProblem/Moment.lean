import JSPProblem.Pairs
import Mathlib.Algebra.Order.Chebyshev

/-!
# JSP-000140 — THE CENSUS OBSTRUCTION AS A CONDITION ON `(n, k)`

`Pairs.lean` (round 62) closed the **exact** four-set census: for every admissible colouring

    `|fiveFourSets c| = ∑_i choose |E_i| 2 + (n - 4) * Paths c`,   `|fiveFourSets c| ≤ C(n,4)`.

Both sides of that identity are `O(n⁴)` at the extremal scale, so the identity itself has no
asymptotic content; but its **lower** side is a function of the *profile* `(|E_i|)` and of
`Paths c`, and `Paths c` is the very quantity the counting bound `Cherry.five_sixth_lower`
controls.  This file closes that loop and obtains what `Pairs.lean` could not state: a **numerical
necessary condition on the pair `(n, k)` alone**, obtained by

1. **Cauchy–Schwarz on the colour classes** (§1) — a *lower* bound on the pair census
   `∑_i choose |E_i| 2 ≥ (|E(K_n)|²/k - |E(K_n)|)/2`, the mirror image of the *upper* second moment
   `Pairs.sum_sq_le`;
2. **the census** (§2) — turning that lower bound into an **upper bound on `Paths c`**;
3. **the exact surplus identity** (§3) — a **lower bound on `Paths c`** in terms of `k`;
4. **the two together** (§4) — **`moment_obstruction`**, a *quadratic* polynomial condition on
   `(n,k)`.

## The theorem

In the subtraction-free form `Moment.moment_obstruction_raw`, every admissible `k`-colouring of
`K_n` (`n ≥ 4`) satisfies

    **`6n(n-1)k(n-4) + 3·C(n,2)² ≤ 6nk²(n-4) + 6k·C(n,4) + 3k·C(n,2)`**,

i.e. (in integers, `|E| = C(n,2)`)

    **`3·|E|² ≤ k · ( 6n(n-4)·(k - (n-1)) + 6·C(n,4) + 3·|E| )`**.

`Cherry.five_sixth_lower : 5(n-1) ≤ 6k` is **linear** in `k`; this is **quadratic**.  For fixed
`n` the condition excludes every `k` below a root which exceeds `5(n-1)/6` precisely when
`5n² - 63n + 158 < 0`, i.e. for `n ≤ 9`.

## Where it bites — and where it does not (§5, machine-checked)

* `census_at_least_five_sixth_below_eleven` — for every `n < 11` and `k < 20`, `momentOK n k`
  implies `5(n-1) ≤ 6k`, except at `n ≤ 8` where the census is *stronger*;
* `classical_misses_eight` — at `(8,6)` the counting bound `35 ≤ 36` holds and `momentOK 8 6` does
  **not**;
* `census_weaker_at_eleven` — at `(11,8)` the situation is reversed: `momentOK 11 8` holds while
  `50 ≤ 48` fails.  So the two instruments are genuinely incomparable from `n = 11` on, for the
  asymptotic reason that the census left-hand side is `Θ(n³)` at `k = Θ(n)` against a right-hand
  side of `Θ(n⁴)`.  **This file does not improve the published lower bound `f(n,4,5) ≥ 5n/6 -
  o(n)`; it improves the `O(1)` at four small orders, analytically.**

## What it decides (§6)

* **`no_six_of_eight` — `f(8,4,5) ≥ 7`, by counting alone.**  The classical counting bound gives
  only `⌈35/6⌉ = 6` at `n = 8`, and `Main.EG_eight : EG 8 = 7` was previously obtained from a
  *search certificate* (`certC_eight_six`) together with the ghost colouring.  The census
  obstruction excludes the six-colouring **analytically** — no enumeration of `C(8,2)` edge
  assignments.  `Census.lean`'s header has advertised `no_six_of_eight` (and `no_six_of_seven`)
  since round ~37 without either existing; this file proves the first.  The second does **not**
  follow: `momentOK 7 6` holds, so `no_six_of_seven` is *not* a consequence of the census and
  `EG 7 = 7` still rests on the search certificate.
* `no_four_of_four`, `no_four_of_five`, `no_five_of_seven` — `f(4,4,5) ≥ 5`, `f(5,4,5) ≥ 5`,
  `f(7,4,5) ≥ 6`, where the counting bound gives `3`, `4`, `5`;
* `no_four_of_six`, `no_six_of_nine`, `no_seven_of_ten` — further instances of the same argument,
  recorded so that the finite targets of §5 are theorems rather than computations;
* `EG_moment` — the condition holds of **`EG n` itself**, so it is a statement about the
  Erdős–Gyárfás function (`EG_five_ge_five_census` … `EG_ten_ge_eight_census`).

## The new theorems

* `card_fourSets`, `card_edges` (§0) — `|fourSets n| = C(n,4)` and `|E(K_n)| = C(n,2)`, i.e. the
  numerical sizes that give the census a numerical form at all;
* `sum_sq_card_mul_ge`, `sum_sq_classF` (§1) — Cauchy–Schwarz for the colour-class profile;
* **`pairs_lower`** (§1) — **`2·k·∑_i choose |E_i| 2 + k·|E| ≥ |E|²`**, the lower half of the pair
  census.  `Surplus.surplus_identity` knows only `∑ |E_i|`, `Paths` and `Isolated`, so this is new
  information about the same colouring;
* **`paths_le_of_census`** (§2) and **`paths_ge_of_surplus`** (§3) — the two halves of the pincer on
  `Paths c`;
* **`moment_obstruction`** (§4), `momentOK` (§4) and `EG_moment` (§6) — the condition;
* §7: the obstruction is **satisfied by all four verified constructions** of `Tables.lean`
  (`K₆, K₉, K₁₀, K₁₁`), so it is not vacuous.

## Lean 4.34.0 pitfalls recorded this round

* **`Decidable` does NOT see through a plain `def`.**  `native_decide` on `¬ momentOK 8 6` fails
  with *"failed to synthesize `Decidable (momentOK 8 6)`"* until `momentOK` is marked
  `@[reducible]` — typeclass resolution never delta-unfolds an ordinary definition;
* `Multiset.sq_sum_le_card_mul_sum_sq` (in `Mathlib/Algebra/Order/Chebyshev.lean`) quantifies over the
  **multiset element type** (the semiring is the multiset's element type), *not* over a scalar:
  for `f : Fin k → ℕ` one wants the `Finset` version `sq_sum_le_card_mul_sum_sq`, whose
  `simpa`-normalisation `∑ i ∈ univ, f i ↦ ∑ i : Fin k, f i` is exactly what is needed;
* `Finset.powersetCard` takes the size **first**: `(Finset.univ : Finset (Finset α)).powersetCard 4`
  silently has type `Finset (Finset (Finset α))`, and `Finset.card_powersetCard` then gives
  `choose ((Finset (Finset α)).card)`, not `choose (Fintype.card α)`;
* `norm_num` does **not** evaluate `Nat.choose` (`Nat.choose 8 4 = 70` is left open) while `decide`
  and `native_decide` do — for small arguments;
* `Nat.choose_two_mul` does **not** exist in this Mathlib; the pair arithmetic is
  `Nat.choose_two_right : n.choose 2 = n * (n-1) / 2`, and the round's own
  `Pairs.choose_two_mul : 2 * n.choose 2 = n * (n-1)` is what turns `2 * |E| = n * (n-1)` into
  `|E| = C(n,2)` by `omega`;
* `Nat.mul_add`, `Nat.add_mul` have only their **last** argument explicit (`{m n} (k)`) while
  `Nat.mul_le_mul_left`/`_right` have only their **multiplier** explicit — the two families read
  identically and are written in opposite orders;
* `Nat.add_le_add` takes **two** inequalities (`a ≤ b → c ≤ d → a + c ≤ b + d`); the
  `add_le_add_right` variant is the one needed when the common term is on the right;
* `omega` does **not** normalise `5 * n * (n-1)` into `5 * (n * (n-1))`, so a hypothesis and a goal
  mentioning the same product in different parenthesisations are *unrelated atoms*: hand it the two
  `by ring` equalities first.  The same is true of the products `k * (n-4) * Paths c` etc., which
  is why `moment_obstruction_raw` generalises all six of its terms and then calls `omega` once;
* `rcases` on `k ≤ M` into a case split needs `interval_cases k`, and each case then needs its own
  decision procedure (`exact absurd hk (by decide)`) — `norm_num [momentOK] at hk` leaves
  `Nat.choose` untouched and produces nonsense goals;
* `Decidable` for `Nat.choose` exists (so `decide` proves `Nat.choose 8 4 = 70`), but `norm_num`
  has no simp lemma for it.
-/

set_option maxHeartbeats 1000000

namespace JSP140

variable {n k : ℕ}

noncomputable section

/-! ### §0  the numerical size of the objects the census counts -/

/-- **THE NUMBER OF FOUR-SETS OF `K_n` IS `C(n,4)`.**  `fourSets n` filters `univ` by `S.card = 4`,
i.e. it is the `Finset`-version `powersetCard` of `Finset.univ`, whose cardinality is the binomial
coefficient.  This is what gives the census a numerical form. -/
theorem card_fourSets (n : ℕ) : (fourSets n).card = Nat.choose n 4 := by
  have h : fourSets n = (Finset.univ : Finset (Verts n)).powersetCard 4 := by
    ext S
    simp [fourSets]
  rw [h, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

/-- **THE NUMBER OF EDGES OF `K_n` IS `C(n,2)`.**  `Counting.card_edgeFinset_univ_two` gives
`2 * |E| = n * (n-1)` without division; `Pairs.choose_two_mul` gives the same for `C(n,2)`, and
`omega` cancels the `2`. -/
theorem card_edges (n : ℕ) :
    (edgeFinset (Finset.univ : Finset (Verts n))).card = Nat.choose n 2 := by
  have h1 := card_edgeFinset_univ_two n
  have h2 := choose_two_mul n
  omega

/-! ### §1  Cauchy–Schwarz on the colour classes: the LOWER pair census -/

/-- **CAUCHY–SCHWARZ FOR THE COLOUR CLASSES:** `k * ∑_i m_i² ≥ (∑_i m_i)²` for any
`m : Fin k → ℕ`.  (`Multiset.sq_sum_le_card_mul_sum_sq`, from
`Mathlib/Algebra/Order/Chebyshev.lean`.) -/
theorem sum_sq_card_mul_ge {k : ℕ} (f : Fin k → ℕ) :
    k * ∑ i : Fin k, (f i) ^ 2 ≥ (∑ i : Fin k, f i) ^ 2 := by
  have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin k))) (f := f)
  simpa using h

/-- **THE LOWER SECOND MOMENT OF THE COLOUR-CLASS PROFILE:**
`k * ∑_i |E_i|² ≥ |E(K_n)|²`.  The mirror image of `Pairs.sum_sq_le`. -/
theorem sum_sq_classF {n k : ℕ} (c : Col n k) :
    k * ∑ i : Fin k, (classF c i).card * (classF c i).card
      ≥ (edgeFinset (Finset.univ : Finset (Verts n))).card ^ 2 := by
  have h := sum_sq_card_mul_ge (fun i : Fin k => (classF c i).card)
  have e : ∑ i : Fin k, (classF c i).card ^ 2
      = ∑ i : Fin k, (classF c i).card * (classF c i).card :=
    Finset.sum_congr rfl fun i _ => pow_two (classF c i).card
  rw [e] at h
  have e' : ∑ i : Fin k, (classF c i).card = (edgeFinset (Finset.univ : Finset (Verts n))).card :=
    sum_card_classF c
  rw [e'] at h
  exact h

/-- **THE LOWER HALF OF THE PAIR CENSUS:**

    `2 * k * ∑_i choose |E_i| 2 + k * |E(K_n)| ≥ |E(K_n)|²`,

i.e. `∑_i choose |E_i| 2 ≥ (|E|² / k - |E|) / 2` without division.  `Pairs.sum_sq_le` is the upper
half of the same pair census; **neither is a consequence of `Surplus.surplus_identity`**, which
knows only `∑_i |E_i|`, `Paths c` and `Isolated c`. -/
theorem pairs_lower {n k : ℕ} (c : Col n k) :
    2 * (k * (∑ i : Fin k, Nat.choose (classF c i).card 2))
      + k * (edgeFinset (Finset.univ : Finset (Verts n))).card
    ≥ (edgeFinset (Finset.univ : Finset (Verts n))).card ^ 2 := by
  have hA : ∀ i : Fin k, (classF c i).card * (classF c i).card
      = 2 * Nat.choose (classF c i).card 2 + (classF c i).card := by
    intro i
    rw [← mul_sub_add, ← choose_two_mul]
  have hS : ∑ i : Fin k, (2 * Nat.choose (classF c i).card 2)
      = 2 * ∑ i : Fin k, Nat.choose (classF c i).card 2 := by
    symm
    exact Finset.mul_sum _ _ _
  have hB : k * ∑ i : Fin k, (classF c i).card * (classF c i).card
      = 2 * (k * (∑ i : Fin k, Nat.choose (classF c i).card 2))
        + k * (edgeFinset (Finset.univ : Finset (Verts n))).card := by
    calc k * ∑ i : Fin k, (classF c i).card * (classF c i).card
        = k * ∑ i : Fin k,
            (2 * Nat.choose (classF c i).card 2 + (classF c i).card) :=
          congrArg (fun t => k * t) (Finset.sum_congr rfl fun i _ => hA i)
      _ = k * (∑ i : Fin k, (2 * Nat.choose (classF c i).card 2)
            + ∑ i : Fin k, (classF c i).card) := by rw [Finset.sum_add_distrib]
      _ = k * (2 * ∑ i : Fin k, Nat.choose (classF c i).card 2
            + (edgeFinset (Finset.univ : Finset (Verts n))).card) := by
        rw [hS, sum_card_classF c]
      _ = k * (2 * ∑ i : Fin k, Nat.choose (classF c i).card 2)
            + k * (edgeFinset (Finset.univ : Finset (Verts n))).card := by
        rw [Nat.mul_add]
      _ = 2 * (k * (∑ i : Fin k, Nat.choose (classF c i).card 2))
            + k * (edgeFinset (Finset.univ : Finset (Verts n))).card := by
        rw [Nat.mul_left_comm]
  have hC := sum_sq_classF c
  rw [hB] at hC
  exact hC

/-! ### §2  the census turns the lower pair bound into an upper bound on `Paths c` -/

/-- **THE CENSUS GIVES AN UPPER BOUND ON THE NUMBER OF TWO-EDGE PATHS:**

    `2 * k * ((n-4) * Paths c) + |E(K_n)|² ≤ 2 * k * C(n,4) + k * |E(K_n)|`.

This is `Pairs.census_obstruction` (`∑_i choose |E_i| 2 + (n-4) * Paths c ≤ C(n,4)`) with
`Pairs.pairs_lower` substituted on the left.  `Quad.fiveFourSets_le_fourSets` already gave the
weaker `(n-3) * Paths c ≤ C(n,4)`; the point is that **the colour-class profile now appears**. -/
theorem paths_le_of_census {n k : ℕ} {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n) :
    2 * k * ((n - 4) * Paths c)
      + (edgeFinset (Finset.univ : Finset (Verts n))).card ^ 2
    ≤ 2 * k * (fourSets n).card
      + k * (edgeFinset (Finset.univ : Finset (Verts n))).card := by
  have h1 := fiveFourSets_census hc hn
  have h2 := fiveFourSets_le_fourSets (c := c)
  have h3 := pairs_lower c
  have hA : (∑ i : Fin k, Nat.choose (classF c i).card 2) + (n - 4) * Paths c
      ≤ (fourSets n).card := by omega
  calc 2 * k * ((n - 4) * Paths c)
        + (edgeFinset (Finset.univ : Finset (Verts n))).card ^ 2
      ≤ 2 * k * ((n - 4) * Paths c)
        + (2 * (k * (∑ i : Fin k, Nat.choose (classF c i).card 2))
          + k * (edgeFinset (Finset.univ : Finset (Verts n))).card) :=
        Nat.add_le_add_left h3 _
      _ = (2 * k * (∑ i : Fin k, Nat.choose (classF c i).card 2)
          + 2 * k * ((n - 4) * Paths c))
          + k * (edgeFinset (Finset.univ : Finset (Verts n))).card := by ring
      _ ≤ (2 * k * (fourSets n).card)
          + k * (edgeFinset (Finset.univ : Finset (Verts n))).card :=
        Nat.add_le_add_right
          ((show 2 * k * (∑ i : Fin k, Nat.choose (classF c i).card 2)
              + 2 * k * ((n - 4) * Paths c)
            = 2 * k * ((∑ i : Fin k, Nat.choose (classF c i).card 2) + (n - 4) * Paths c) by
            ring).trans_le (Nat.mul_le_mul_left (2 * k) hA))
          (k * (edgeFinset (Finset.univ : Finset (Verts n))).card)

/-! ### §3  the exact surplus identity gives a lower bound on `Paths c` -/

/-- **THE SURPLUS IDENTITY GIVES A LOWER BOUND ON THE NUMBER OF TWO-EDGE PATHS:**

    `6 * n * (n-1) ≤ 6 * n * k + 6 * Paths c`,

i.e. `Paths c ≥ n * (n - 1 - k)`.  This is `Surplus.surplus_identity`
(`6nk = 5n(n-1) + 6 * Isolated c + 2 * Defect c`, `Defect c = |E| - 3 * Paths c`) with
`Isolated c ≥ 0` dropped.  It is the lower half of the pincer of §2. -/
theorem paths_ge_of_surplus {n k : ℕ} {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n) :
    6 * n * (n - 1) ≤ 6 * n * k + 6 * Paths c := by
  have h3 := three_mul_paths_le_edges hc hn
  have hD : (edgeFinset (Finset.univ : Finset (Verts n))).card = 3 * Paths c + Defect c := by
    unfold Defect
    omega
  have hE := card_edgeFinset_univ_two n
  have hI : 0 ≤ Isolated c := Finset.sum_nonneg fun i _ => Nat.zero_le _
  have h : 6 * n * k = 5 * n * (n - 1) + 6 * Isolated c + 2 * Defect c := by
    have h' := surplus_identity hc hn
    unfold Defect at h'
    unfold Defect
    convert h' using 1 <;> ring
  have hA1 : 5 * n * (n - 1) = 5 * (n * (n - 1)) := by ring
  have hA2 : 6 * n * (n - 1) = 6 * (n * (n - 1)) := by ring
  omega

/-! ### §4  THE MOMENT OBSTRUCTION -/

/-- **THE MOMENT OBSTRUCTION, in the raw form.**  For every admissible `k`-colouring of `K_n`
(`n ≥ 4`),

    `6n(n-1)k(n-4) + 3|E|² ≤ 6nk²(n-4) + 6k·C(n,4) + 3k|E|`,

with `|E| = C(n,2)`.  Equivalently (in integers) `3|E|² ≤ k · (6n(n-4)(k - (n-1)) + 6C(n,4) + 3|E|)`:
a **quadratic** necessary condition on `(n,k)`, where `Cherry.five_sixth_lower` is linear. -/
theorem moment_obstruction_raw {n k : ℕ} {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n) :
    6 * n * (n - 1) * k * (n - 4) + 3 * (edgeFinset (Finset.univ : Finset (Verts n))).card ^ 2
      ≤ 6 * n * k * k * (n - 4) + 6 * k * (fourSets n).card
        + 3 * k * (edgeFinset (Finset.univ : Finset (Verts n))).card := by
  have h1 := paths_ge_of_surplus hc hn
  have h2 := paths_le_of_census hc hn
  have h3 : 6 * n * (n - 1) * k * (n - 4)
      ≤ 6 * n * k * k * (n - 4) + 6 * k * ((n - 4) * Paths c) := by
    have h := Nat.mul_le_mul_right (k * (n - 4)) h1
    convert h using 1 <;> ring
  have h4 : 6 * k * ((n - 4) * Paths c) + 3 * (edgeFinset (Finset.univ : Finset (Verts n))).card ^ 2
      ≤ 6 * k * (fourSets n).card
        + 3 * k * (edgeFinset (Finset.univ : Finset (Verts n))).card := by
    have h := Nat.mul_le_mul_left 3 h2
    convert h using 1 <;> ring
  generalize hA1 : 6 * n * (n - 1) * k * (n - 4) = A1
  generalize hB1 : 6 * n * k * k * (n - 4) = B1
  generalize hC1 : 6 * k * ((n - 4) * Paths c) = C1
  generalize hD1 : 6 * k * (fourSets n).card = D1
  generalize hE2 : 3 * (edgeFinset (Finset.univ : Finset (Verts n))).card ^ 2 = E2
  generalize hE3 : 3 * k * (edgeFinset (Finset.univ : Finset (Verts n))).card = E3
  omega

/-- **THE MOMENT OBSTRUCTION: the numerical predicate on `(n, k)`.**  `momentOK n k` is the
subtraction-free quadratic form of §4 with `C(n,2)` and `C(n,4)` substituted in.  The
`@[reducible]` attribute is what lets `native_decide` see through it (typeclass resolution does not
delta-unfold a plain `def`). -/
@[reducible] def momentOK (n k : ℕ) : Prop :=
  6 * n * (n - 1) * k * (n - 4) + 3 * (Nat.choose n 2) ^ 2
    ≤ 6 * n * k * k * (n - 4) + 6 * k * Nat.choose n 4 + 3 * k * Nat.choose n 2

/-- **THE MOMENT OBSTRUCTION — every admissible `k`-colouring of `K_n` satisfies `momentOK n k`.** -/
theorem moment_obstruction {n k : ℕ} {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n) :
    momentOK n k := by
  have h := moment_obstruction_raw hc hn
  rw [card_fourSets, card_edges] at h
  exact h


/-! ### §5  where the census obstruction is sharper than the counting bound -/

/-- **AT `(8, 6)` THE COUNTING BOUND IS SATISFIED AND THE CENSUS OBSTRUCTION IS NOT.**  This is the
witness that §4 is *not* a reformulation of `Cherry.five_sixth_lower : 5(n-1) ≤ 6k`. -/
theorem classical_misses_eight : 5 * (8 - 1) ≤ 6 * 6 ∧ ¬ momentOK 8 6 := by native_decide

/-- **BELOW `n = 11` THE CENSUS OBSTRUCTION IS AT LEAST AS STRONG AS THE COUNTING BOUND.**
Machine-checked for all `n < 11` and `k < 20`: whenever `momentOK n k` holds, either the classical
bound `5(n-1) ≤ 6k` holds as well, or `n ≤ 8` — and at `n = 4, 5, 7, 8` §6 below exhibits the pairs
where only the census obstruction bites. -/
theorem census_at_least_five_sixth_below_eleven :
    ∀ n ∈ Finset.range 11, ∀ k ∈ Finset.range 20,
      momentOK n k → 5 * (n - 1) ≤ 6 * k ∨ n ≤ 8 := by native_decide

/-- **AND FROM `n = 11` ON IT IS WEAKER.**  At `(11, 8)` the condition of §4 holds while the counting
bound fails, so the two instruments are genuinely incomparable above `n = 10`; the reason is the
asymptotics: the census left-hand side is `Θ(n³)` at `k = Θ(n)` while its right-hand side is
`Θ(n⁴)`, so the condition can only bite at small `k`.  Recorded so that §4 is not mistaken for a
uniform improvement of the published lower bound. -/
theorem census_weaker_at_eleven : ¬ (5 * (11 - 1) ≤ 6 * 8) ∧ momentOK 11 8 := by native_decide

/-- At `n = 4`: `k ≥ 5` (the counting bound gives `3`; this is `f(4,4,5) = 5` by another route). -/
theorem moment_four_ge_five : ∀ k : ℕ, momentOK 4 k → 5 ≤ k := by
  intro k hk
  by_contra h
  have hk' : k < 5 := Nat.lt_of_not_ge h
  interval_cases k <;> exact absurd hk (by decide)

/-- At `n = 5`: `k ≥ 5` (the counting bound gives `4`). -/
theorem moment_five_ge_five : ∀ k : ℕ, momentOK 5 k → 5 ≤ k := by
  intro k hk
  by_contra h
  have hk' : k < 5 := Nat.lt_of_not_ge h
  interval_cases k <;> exact absurd hk (by decide)

/-- At `n = 6`: `k ≥ 5`, the classical value. -/
theorem moment_six_ge_five : ∀ k : ℕ, momentOK 6 k → 5 ≤ k := by
  intro k hk
  by_contra h
  have hk' : k < 5 := Nat.lt_of_not_ge h
  interval_cases k <;> exact absurd hk (by decide)

/-- At `n = 7`: `k ≥ 6`, where the classical counting bound gives only `5`. -/
theorem moment_seven_ge_six : ∀ k : ℕ, momentOK 7 k → 6 ≤ k := by
  intro k hk
  by_contra h
  have hk' : k < 6 := Nat.lt_of_not_ge h
  interval_cases k <;> exact absurd hk (by decide)

/-- **AT `n = 8`: `k ≥ 7`, where the classical counting bound gives only `6`.** -/
theorem moment_eight_ge_seven : ∀ k : ℕ, momentOK 8 k → 7 ≤ k := by
  intro k hk
  by_contra h
  have hk' : k < 7 := Nat.lt_of_not_ge h
  interval_cases k <;> exact absurd hk (by decide)

/-- At `n = 9`: `k ≥ 7`, the classical value. -/
theorem moment_nine_ge_seven : ∀ k : ℕ, momentOK 9 k → 7 ≤ k := by
  intro k hk
  by_contra h
  have hk' : k < 7 := Nat.lt_of_not_ge h
  interval_cases k <;> exact absurd hk (by decide)

/-- At `n = 10`: `k ≥ 8`, the classical value. -/
theorem moment_ten_ge_eight : ∀ k : ℕ, momentOK 10 k → 8 ≤ k := by
  intro k hk
  by_contra h
  have hk' : k < 8 := Nat.lt_of_not_ge h
  interval_cases k <;> exact absurd hk (by decide)

/-! ### §6  the negative results and their `EG` form -/

/-- **`f(4,4,5) ≥ 5`.**  (The counting bound gives `3`.) -/
theorem no_four_of_four : ¬ (∃ c : Col 4 4, Admissible c) := by
  rintro ⟨c, hc⟩
  have h := moment_obstruction hc (by norm_num)
  exact absurd (moment_four_ge_five 4 h) (by decide)

/-- **`f(5,4,5) ≥ 5`.**  (The counting bound gives `4`.) -/
theorem no_four_of_five : ¬ (∃ c : Col 5 4, Admissible c) := by
  rintro ⟨c, hc⟩
  have h := moment_obstruction hc (by norm_num)
  exact absurd (moment_five_ge_five 4 h) (by decide)

/-- **`f(6,4,5) ≥ 5`.** -/
theorem no_four_of_six : ¬ (∃ c : Col 6 4, Admissible c) := by
  rintro ⟨c, hc⟩
  have h := moment_obstruction hc (by norm_num)
  exact absurd (moment_six_ge_five 4 h) (by decide)

/-- **`f(7,4,5) ≥ 6`.**  (The counting bound gives `5`.) -/
theorem no_five_of_seven : ¬ (∃ c : Col 7 5, Admissible c) := by
  rintro ⟨c, hc⟩
  have h := moment_obstruction hc (by norm_num)
  exact absurd (moment_seven_ge_six 5 h) (by decide)

/-- **`f(8,4,5) ≥ 7` — NO ADMISSIBLE SIX-COLOURING OF `K₈` EXISTS.**  This is the `no_six_of_eight`
step advertised by `Census.lean`'s header since round ~37; unlike `Main.EG_eight`, it needs **no
search certificate**.  (The companion `no_six_of_seven` of the same header does **not** follow:
`momentOK 7 6` holds.) -/
theorem no_six_of_eight : ¬ (∃ c : Col 8 6, Admissible c) := by
  rintro ⟨c, hc⟩
  have h := moment_obstruction hc (by norm_num)
  exact absurd (moment_eight_ge_seven 6 h) (by decide)

/-- **`f(9,4,5) ≥ 7`.** -/
theorem no_six_of_nine : ¬ (∃ c : Col 9 6, Admissible c) := by
  rintro ⟨c, hc⟩
  have h := moment_obstruction hc (by norm_num)
  exact absurd (moment_nine_ge_seven 6 h) (by decide)

/-- **`f(10,4,5) ≥ 8`.** -/
theorem no_seven_of_ten : ¬ (∃ c : Col 10 7, Admissible c) := by
  rintro ⟨c, hc⟩
  have h := moment_obstruction hc (by norm_num)
  exact absurd (moment_ten_ge_eight 7 h) (by decide)

/-- **THE MOMENT OBSTRUCTION HOLDS OF `EG n` ITSELF.**  `EG n` colours are attained
(`Definitions.EG_admissible`), so the quadratic condition of §4 is a statement about the
Erdős–Gyárfás function: the classical lower bound is linear in `f(n,4,5)`, this one is quadratic. -/
theorem EG_moment (n : ℕ) (hn : 4 ≤ n) : momentOK n (EG n) :=
  moment_obstruction (c := (EG_admissible n).choose) (EG_admissible n).choose_spec hn

/-- `f(5,4,5) ≥ 5` from `EG_moment`. -/
theorem EG_five_ge_five_census : 5 ≤ EG 5 := moment_five_ge_five _ (EG_moment 5 (by norm_num))

/-- `f(7,4,5) ≥ 6` from `EG_moment` — the classical counting bound gives `5`. -/
theorem EG_seven_ge_six_census : 6 ≤ EG 7 := moment_seven_ge_six _ (EG_moment 7 (by norm_num))

/-- **`f(8,4,5) ≥ 7` from `EG_moment`: the census obstruction, not a search certificate.** -/
theorem EG_eight_ge_seven_census : 7 ≤ EG 8 := moment_eight_ge_seven _ (EG_moment 8 (by norm_num))

/-- `f(9,4,5) ≥ 7` from `EG_moment`. -/
theorem EG_nine_ge_seven_census : 7 ≤ EG 9 := moment_nine_ge_seven _ (EG_moment 9 (by norm_num))

/-- `f(10,4,5) ≥ 8` from `EG_moment`. -/
theorem EG_ten_ge_eight_census : 8 ≤ EG 10 := moment_ten_ge_eight _ (EG_moment 10 (by norm_num))

/-- **THE CENSUS REPRODUCES `Main.EG_eight`'s LOWER HALF ANALYTICALLY.**  The exact value
`EG 8 = 7` needs the ghost colouring for the upper half; the lower half `7 ≤ EG 8` is the counting
argument of §4. -/
theorem census_eight_lower_half : 7 ≤ EG 8 ∧ ¬ (∃ c : Col 8 6, Admissible c) :=
  ⟨EG_eight_ge_seven_census, no_six_of_eight⟩

/-! ### §7  the obstruction is not vacuous: the four verified constructions -/

/-- The obstruction holds on the `K₆` witness `sixCol` (`5` colours). -/
theorem moment_sixCol : momentOK 6 5 := moment_obstruction admissible_sixCol (by norm_num)

/-- … on the `K₉` witness `nineCol` (`8` colours). -/
theorem moment_nineCol : momentOK 9 8 := moment_obstruction admissible_nineCol (by norm_num)

/-- … on the `K₁₀` witness `tenCol` (`9` colours). -/
theorem moment_tenCol : momentOK 10 9 := moment_obstruction admissible_tenCol (by norm_num)

/-- … on the `K₁₁` witness `elevenCol` (`10` colours). -/
theorem moment_elevenCol : momentOK 11 10 := moment_obstruction admissible_elevenCol (by norm_num)

/-- **THE OBSTRUCTION IS SATISFIED BY EVERY VERIFIED CONSTRUCTION OF `Tables.lean`.**  So §4 does not
contradict the witnesses the searches of rounds 45–46 produced. -/
theorem moment_consistent_with_tables :
    momentOK 6 5 ∧ momentOK 9 8 ∧ momentOK 10 9 ∧ momentOK 11 10 :=
  ⟨moment_sixCol, moment_nineCol, moment_tenCol, moment_elevenCol⟩

end

end JSP140
