import JSPProblem.Moment

/-!
# JSP-000140 — THE PER-CLASS CHARGE: `f(7,4,5) ≥ 7` WITH NO COMPUTER SEARCH

## The gap left by round 63

`Pairs.lean` (round 62) closed the **exact** four-set census,

    `∑_i choose |E_i| 2 + (n-4) * Paths c = |fiveFourSets c| ≤ C(n,4)`,

and `Moment.lean` (round 63) closed it numerically with **Cauchy–Schwarz** on the colour-class
profile, giving the quadratic condition `Moment.moment_obstruction` on `(n, k)`.  Cauchy–Schwarz
sees only `∑_i |E_i| = C(n,2)`: it is blind to the *shape* of the profile, and that blindness is
exactly what stops it at `(n, k) = (7, 6)` — `Moment.momentOK 7 6` holds, so the six-colouring of
`K_7` is not excluded, and `discovery/JSP-000140/policy.json` still listed `no_six_of_seven` (the
one remaining member of the census family) as open.  Until round 63 the only Lean proof that
`EG 7 ≥ 7` was the search certificate `VertexSearch.certC_seven` (38 654 nodes).

## The input this file adds: a per-class charge

`Paths.two_mul_classIn_le_add` (round 4) is a **per-class** lemma,

    `2 * |E_i| ≤ n + |A_i|`,      i.e.      `|A_i| ≥ 2 * |E_i| - n`,

so a colour class with more than `n/2` edges *must* pay for itself in two-edge paths, and in the
census term `(n-4) * |A_i|` this becomes a lower bound that depends on the *shape* of the profile.
`Cherry.three_mul_paths_le_edges` (`3 * Paths c ≤ |E|`), `Surplus.surplus_identity` and
`Moment.pairs_lower` all discard it: they compare totals only.  §0–§1 charge each class with the
part of its census term that its own size already forces, and §1 adds one genuinely new
*arithmetic* observation that Cauchy–Schwarz cannot see:

    **`Σ_i (2|E_i| - n) = Σ_i (n - 2|E_i|)` whenever `2C(n,2) = n·k`, and every one of the `k` pairs
    is at least `1` when `n` is odd — so `k ≤ 2 · Σ_i (2|E_i| - n)`.**

(The equality of the two sums is the truncation identity `a - b = max a b - b` summed against
`Σ a = Σ b`; the parity of `n` is what forbids `2|E_i| = n`.)

## What is proved here

* `Profile.card_classF_le` — a colour class of an admissible colouring has at most `n` edges
  (max degree `2`), the hypothesis any comparison of two profiles needs;
* `Profile.profileCost`, `Profile.profileCost_le_census_term`,
  **`Profile.sum_profileCost_le_fourSets`** — the *relaxed* census
  `∑_i [ choose |E_i| 2 + (n-4) * (2|E_i| - n) ] ≤ C(n,4)`, valid for every admissible colouring;
* `Profile.sum_sub_eq_sum_sub_rev`, `Profile.sum_surplus_ge`, `Profile.surplus_ge_odd` — the parity
  charge, in general form;
* **`Profile.charge_census`, `Profile.chargeOK`, `Profile.charge_obstruction`** — the charge and the
  census combined into a **numerical predicate `chargeOK n` on the order alone**: the first
  `(n,k)`-only instrument of this development which uses the profile *shape* rather than
  Cauchy–Schwarz, and hence the first one which can see `k = n - 1`;
* **`Profile.no_six_of_seven : ¬ (∃ c : Col 7 6, Admissible c)`** and
  **`Profile.EG_seven_ge_seven : 7 ≤ EG 7`** — the lower half of `Main.EG_seven : EG 7 = 7` is now
  **analytic**; the search certificate `VertexSearch.certC_seven` is no longer needed for it.
  `Moment.momentOK 7 6` still holds, so this is strictly stronger than round 63;
* `Profile.sum_profileCost_seven_six` — the same conclusion from the profile alone: **every**
  profile of six classes summing to `21 = C(7,2)` has relaxed cost `≥ 36`;
* §5 — the exclusion misses by a **single** four-set (`36 = C(7,4) + 1`), and both halves of the
  bound are attained by the balanced profile `(4,4,4,3,3,3)`.

## What is *not* proved here

`chargeOK n` is a *lower* bound on `k`; like every instrument of this family it does not exclude
the six-colourings of `K_9`, `K_11`, … (machine-checked: `chargeOK 9`, `chargeOK 11` hold), so it
adds nothing at large `n`, and in particular it does not touch the upper half of
`jsp_000140_main` (`Main.AdmissibleUpper ε` for `0 < ε < 1/6`, the probabilistic existence theorem
of arXiv:2207.02920 §4), which remains the sole content of the prize.
-/


namespace JSP140

variable {n k : ℕ}

noncomputable section

/-- The sum of a constant over `Fin k`. -/
private lemma sum_const_fin (m k : ℕ) : (∑ _i : Fin k, (m : ℕ)) = m * k := by
  calc (∑ i : Fin k, (m : ℕ)) = ∑ _i ∈ (Finset.univ : Finset (Fin k)), m := rfl
    _ = (Finset.univ : Finset (Fin k)).card • m := Finset.sum_const _
    _ = Fintype.card (Fin k) * m := by rw [Finset.card_univ, Nat.nsmul_eq_mul]
    _ = m * k := by rw [Fintype.card_fin, Nat.mul_comm]

/-! ### §0  a colour class has at most `n` edges, and the relaxed cost of a colour class -/

/-- **A COLOUR CLASS HAS AT MOST `n` EDGES.**  Every vertex has at most two colour-`i` neighbours
(`ColorClass.nb_card_le_two`), so the colour-`i` edges are `2`-regular at worst and
`2 |E_i| = ∑_v deg_i (v) ≤ 2n`.  This is the hypothesis that makes two profiles comparable. -/
theorem card_classF_le {n k : ℕ} (c : Col n k) (hc : Admissible c) (i : Fin k) :
    (classF c i).card ≤ n := by
  have hdeg := degree_sum (c := c) (i := i) (S := (Finset.univ : Finset (Verts n)))
  have hdeg' : (∑ v : Verts n, (nb c i v (Finset.univ : Finset (Verts n))).card)
      = 2 * (classF c i).card := by simpa only [classF] using hdeg
  have h1 : ∀ v : Verts n,
      (nb c i v (Finset.univ : Finset (Verts n))).card ≤ 2 :=
    fun v => nb_card_le_two hc i v (Finset.univ : Finset (Verts n))
  have h2 : (∑ v : Verts n, (nb c i v (Finset.univ : Finset (Verts n))).card) ≤ 2 * n := by
    calc _ ≤ ∑ _v : Verts n, (2 : ℕ) := Finset.sum_le_sum fun v _ => h1 v
      _ = 2 * n := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, Nat.nsmul_eq_mul,
            Nat.mul_comm]
  omega

/-- **THE RELAXED COST OF A COLOUR CLASS.**  The census charges colour `i` with
`choose |E_i| 2 + (n-4) * |A_i|` four-sets (`Pairs.card_twoFourSets_census`).  Of the second term,
`|A_i| ≥ 2|E_i| - n` is already forced by the size of the class
(`Paths.two_mul_classIn_le_add`), so only the *smaller* number `2|E_i| - n` has to be paid for.
`profileCost n c i` is that smaller charge; the difference between the two is the amount this file
recovers. -/
@[reducible] def profileCost (n : ℕ) (c : Col n k) (i : Fin k) : ℕ :=
  Nat.choose (classF c i).card 2 + (n - 4) * (2 * (classF c i).card - n)

/-- **THE RELAXED COST IS AT MOST THE CENSUS TERM.** -/
theorem profileCost_le_census_term {n k : ℕ} {c : Col n k} (hc : Admissible c) (i : Fin k) :
    profileCost n c i ≤ Nat.choose (classF c i).card 2 + (n - 4) * (twoA c i).card := by
  have h : 2 * (classF c i).card ≤ n + (twoA c i).card := by
    simpa only [classF] using two_mul_classIn_le_add hc i
  have h2 : 2 * (classF c i).card - n ≤ (twoA c i).card := by omega
  have h3 := Nat.mul_le_mul_left (n - 4) h2
  unfold profileCost
  exact Nat.add_le_add_left h3 _

/-- **THE RELAXED CENSUS: every admissible colouring of `K_n` (`n ≥ 4`) satisfies**

      **`∑_i [ choose |E_i| 2 + (n-4) * (2|E_i| - n) ] ≤ C(n,4)`.**

This is `Pairs.census_obstruction` with the *forced* part of every two-edge-path term deleted; it is
strictly stronger than `Moment.moment_obstruction` whenever the profile is unbalanced, because
Cauchy–Schwarz cannot see the individual class sizes at all. -/
theorem sum_profileCost_le_fourSets {n k : ℕ} {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n) :
    (∑ i : Fin k, profileCost n c i) ≤ Nat.choose n 4 := by
  have h1 : (∑ i : Fin k, profileCost n c i)
      ≤ ∑ i : Fin k, (Nat.choose (classF c i).card 2 + (n - 4) * (twoA c i).card) :=
    Finset.sum_le_sum fun i _ => profileCost_le_census_term hc i
  have h2 : (∑ i : Fin k, (Nat.choose (classF c i).card 2 + (n - 4) * (twoA c i).card))
      = ∑ i : Fin k, Nat.choose (classF c i).card 2 + (n - 4) * Paths c := by
    calc _ = ∑ i : Fin k, Nat.choose (classF c i).card 2
        + ∑ i : Fin k, (n - 4) * (twoA c i).card := Finset.sum_add_distrib
      _ = ∑ i : Fin k, Nat.choose (classF c i).card 2
        + (n - 4) * ∑ i : Fin k, (twoA c i).card := by rw [← Finset.mul_sum]
      _ = _ := by rw [Paths]
  have h3 := census_obstruction hc hn
  rw [card_fourSets] at h3
  omega

/-! ### §1  the parity charge -/

/-- **`2 * a ≠ b` whenever `b` is not even.**  A product by `2` is `Even`, so it cannot be a `b`
with `¬ Even b`. -/
theorem two_ne_odd (a b : ℕ) (hne : ¬ Even b) : 2 * a ≠ b := by
  intro he
  exact hne (he ▸ (show Even (2 * a) from ⟨a, by ring⟩))

/-- **`n - 1` IS EVEN whenever `n` is odd.**  (`Nat.even_or_odd`.) -/
theorem even_pred_of_not_even {n : ℕ} (hn : ¬ Even n) : Even (n - 1) := by
  rcases Nat.even_or_odd n with h | ⟨r, h⟩
  · exact (hn h).elim
  · exact ⟨r, by omega⟩

/-- **THE PARITY OF THE TRUNCATED SUM.**  `(a - b) + (b - a) ≥ 1` as soon as `a ≠ b`. -/
theorem sub_add_sub_ge_one (a b : ℕ) (hne : a ≠ b) : 1 ≤ (a - b) + (b - a) := by
  rcases Nat.lt_trichotomy a b with h | h | h
  · omega
  · exact absurd h hne
  · omega

/-- `a - b = max a b - b` in `ℕ`. -/
private lemma sub_eq_max_sub (a b : ℕ) : a - b = max a b - b := by
  rcases Nat.le_total a b with h | h
  · rw [Nat.max_eq_right h]; omega
  · rw [Nat.max_eq_left h]

/-- **`∑_i (h i - t i) = ∑_i h i - ∑_i t i`, provided `t i ≤ h i` pointwise.**  (The truncated
subtraction of `Nat` has no `Finset.sum_sub_distrib` instance, so this is proved from
`Nat.sub_add_cancel`.) -/
private lemma sum_sub_eq_of_le {k : ℕ} (h t : Fin k → ℕ) (hle : ∀ i, t i ≤ h i) :
    (∑ i : Fin k, (h i - t i)) = (∑ i : Fin k, h i) - ∑ i : Fin k, t i := by
  have h1 : (∑ i : Fin k, (h i - t i)) + ∑ i : Fin k, t i = ∑ i : Fin k, h i := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => Nat.sub_add_cancel (hle i)
  omega

/-- **THE TWO TRUNCATED SUMS ARE EQUAL WHEN THE UNTRUNCATED ONES ARE:**
`∑_i (a i - b i) = ∑_i (b i - a i)` whenever `∑_i a i = ∑_i b i`. -/
theorem sum_sub_eq_sum_sub_rev {k : ℕ} (a b : Fin k → ℕ)
    (hsum : (∑ i : Fin k, a i) = ∑ i : Fin k, b i) :
    (∑ i : Fin k, (a i - b i)) = ∑ i : Fin k, (b i - a i) := by
  calc (∑ i : Fin k, (a i - b i)) = ∑ i : Fin k, (max (a i) (b i) - b i) :=
        Finset.sum_congr rfl fun i _ => sub_eq_max_sub (a i) (b i)
    _ = ∑ i : Fin k, max (a i) (b i) - ∑ i : Fin k, b i :=
        sum_sub_eq_of_le (fun i => max (a i) (b i)) b (fun i => Nat.le_max_right _ _)
    _ = ∑ i : Fin k, max (a i) (b i) - ∑ i : Fin k, a i := by rw [hsum]
    _ = ∑ i : Fin k, (max (a i) (b i) - a i) :=
        (sum_sub_eq_of_le (fun i => max (a i) (b i)) a (fun i => Nat.le_max_left _ _)).symm
    _ = ∑ i : Fin k, (b i - a i) :=
        Finset.sum_congr rfl fun i _ => by
          rw [sub_eq_max_sub (b i) (a i), Nat.max_comm]

/-- **THE CHARGE, IN GENERAL FORM (the parity device of the header).**  Let
`f_1, …, f_k ∈ ℕ` have `∑_i 2 f_i = n·k` and let `n` be odd.  Then

      **`k ≤ 2 * ∑_i (2 * f_i - n)`.**

The two truncated sums coincide (`sum_sub_eq_sum_sub_rev`), and each of the `k` pairs
`(2 f_i - n) + (n - 2 f_i)` is at least `1` because `n` is odd and hence `2 f_i ≠ n`. -/
theorem sum_surplus_ge {k n : ℕ} (f : Fin k → ℕ) (hnodd : ¬ Even n)
    (hsum : (∑ i : Fin k, 2 * f i) = n * k) :
    k ≤ 2 * (∑ i : Fin k, (2 * f i - n)) := by
  have hAB := sum_sub_eq_sum_sub_rev (fun i => 2 * f i) (fun _ => n)
    (hsum.trans (sum_const_fin n k).symm)
  have hkey : ∀ i : Fin k, 1 ≤ (2 * f i - n) + (n - 2 * f i) :=
    fun i => sub_add_sub_ge_one _ _ (two_ne_odd (f i) n hnodd)
  have h1 : 2 * (∑ i : Fin k, (2 * f i - n))
      = ∑ i : Fin k, ((2 * f i - n) + (n - 2 * f i)) := by
    calc 2 * ∑ i : Fin k, (2 * f i - n)
        = (∑ i : Fin k, (2 * f i - n)) + ∑ i : Fin k, (n - 2 * f i) := by
          rw [Nat.two_mul, ← hAB]
      _ = ∑ i : Fin k, ((2 * f i - n) + (n - 2 * f i)) := Finset.sum_add_distrib.symm
  have h2 : (∑ i : Fin k, (1 : ℕ)) ≤ ∑ i : Fin k, ((2 * f i - n) + (n - 2 * f i)) :=
    Finset.sum_le_sum fun i _ => hkey i
  have h3 : (∑ i : Fin k, (1 : ℕ)) = k := by rw [sum_const_fin]; omega
  omega

/-- **THE COLOUR CLASSES OF AN ADMISSIBLE COLOURING OF `K_n` SATISFY THE CHARGE AT `k = n - 1`.**
The doubled class sizes sum to `2C(n,2) = n(n-1) = n·k`, the hypothesis of `sum_surplus_ge`. -/
theorem surplus_ge_odd {n : ℕ} (hnodd : ¬ Even n) (c : Col n (n - 1)) :
    n - 1 ≤ 2 * (∑ i : Fin (n - 1), (2 * (classF c i).card - n)) := by
  refine sum_surplus_ge _ hnodd ?_
  calc (∑ i : Fin (n - 1), 2 * (classF c i).card)
      = 2 * (∑ i : Fin (n - 1), (classF c i).card) := by rw [← Finset.mul_sum]
    _ = 2 * (edgeFinset (Finset.univ : Finset (Verts n))).card := by rw [sum_card_classF]
    _ = n * (n - 1) := card_edgeFinset_univ_two n

/-! ### §2  the charge and the census: a numerical condition on the order alone -/

/-- **THE CHARGED CENSUS.**  For every admissible `k`-colouring of `K_n` with `n` odd and
`k = n - 1`,

      **`∑_i choose |E_i| 2 + (n-4) * ((n-1)/2) ≤ C(n,4)`.**

The first term is the pair census of `Pairs.lean`; the second is the charge of §1, forced on every
class profile. -/
theorem charge_census {n : ℕ} (hn4 : 4 ≤ n) (hnodd : ¬ Even n) {c : Col n (n - 1)}
    (hc : Admissible c) :
    (∑ i : Fin (n - 1), Nat.choose (classF c i).card 2) + (n - 4) * ((n - 1) / 2)
      ≤ Nat.choose n 4 := by
  have h0 : (∑ i : Fin (n - 1), Nat.choose (classF c i).card 2)
      + (n - 4) * (∑ i : Fin (n - 1), (2 * (classF c i).card - n))
      ≤ Nat.choose n 4 := by
    have h := sum_profileCost_le_fourSets hc hn4
    simp only [profileCost, Finset.sum_add_distrib] at h
    rw [← Finset.mul_sum] at h
    exact h
  have h1 := surplus_ge_odd hnodd c
  have h2 : (n - 1) / 2 ≤ ∑ i : Fin (n - 1), (2 * (classF c i).card - n) := by omega
  have h3 := Nat.mul_le_mul_left (n - 4) h2
  omega

/-- **THE CHARGE OBSTRUCTION: the numerical predicate on the order.**  `chargeOK n` is the census of
§2 with the *pair* term eliminated by `Moment.pairs_lower` (Cauchy–Schwarz) and the *path* term
eliminated by the parity charge of §1.  A machine-checked `¬ chargeOK n` is a certificate that no
admissible `(n-1)`-colouring of `K_n` exists. -/
@[reducible] def chargeOK (n : ℕ) : Prop :=
  (Nat.choose n 2) ^ 2 - (n - 1) * Nat.choose n 2 + (n - 4) * (n - 1) * (n - 1)
    ≤ 2 * (n - 1) * Nat.choose n 4

/-- **EVERY ADMISSIBLE `(n-1)`-COLOURING OF AN ODD `K_n` SATISFIES `chargeOK n`.** -/
theorem charge_obstruction {n : ℕ} (hn4 : 4 ≤ n) (hnodd : ¬ Even n) {c : Col n (n - 1)}
    (hc : Admissible c) : chargeOK n := by
  have h1 := charge_census hn4 hnodd hc
  have h2 := pairs_lower c
  rw [card_edges] at h2
  -- the parity device: `n - 1` is even, so the charge `⌊(n-1)/2⌋` is exactly half of it
  have h3 : 2 * ((n - 1) / 2) = n - 1 := by
    obtain ⟨r, hr⟩ := even_pred_of_not_even hnodd
    omega
  have h6 : 2 * ((n - 1) * ((∑ i : Fin (n - 1), Nat.choose (classF c i).card 2)
      + (n - 4) * ((n - 1) / 2))) ≤ 2 * (n - 1) * Nat.choose n 4 := by
    have h := Nat.mul_le_mul_right (2 * (n - 1)) h1
    convert h using 1 <;> ring
  have h7 : Nat.choose n 2 * Nat.choose n 2
      ≤ 2 * ((n - 1) * (∑ i : Fin (n - 1), Nat.choose (classF c i).card 2))
        + (n - 1) * Nat.choose n 2 := by
    calc Nat.choose n 2 * Nat.choose n 2 = (Nat.choose n 2) ^ 2 := (pow_two _).symm
      _ ≤ _ := by omega
  have h8 : Nat.choose n 2 * Nat.choose n 2 - (n - 1) * Nat.choose n 2
      + 2 * ((n - 4) * (n - 1)) * ((n - 1) / 2) ≤ 2 * (n - 1) * Nat.choose n 4 := by
    calc _ ≤ 2 * ((n - 1) * (∑ i : Fin (n - 1), Nat.choose (classF c i).card 2))
        + 2 * ((n - 4) * (n - 1)) * ((n - 1) / 2) := by omega
      _ = 2 * ((n - 1) * ((∑ i : Fin (n - 1), Nat.choose (classF c i).card 2)
          + (n - 4) * ((n - 1) / 2))) := by ring
      _ ≤ _ := h6
  have h3' : ∀ m : ℕ, m * (n - 1) = m * (2 * ((n - 1) / 2)) := by
    intro m; rw [h3]
  have h9 : (n - 4) * (n - 1) * (n - 1) = 2 * ((n - 4) * (n - 1)) * ((n - 1) / 2) := by
    calc (n - 4) * (n - 1) * (n - 1) = ((n - 4) * (n - 1)) * (n - 1) := by ring
      _ = ((n - 4) * (n - 1)) * (2 * ((n - 1) / 2)) := h3' _
      _ = _ := by ring
  unfold chargeOK
  rw [pow_two, h9]
  exact h8

/-! ### §3  `f(7,4,5) ≥ 7`: the six-colouring of `K_7` is excluded analytically -/

/-- **`chargeOK 7` FAILS.**  `C(7,2)² - 6·C(7,2) + 3·6·6 = 423 > 420 = 2·6·C(7,4)`: the charge and
the census differ by exactly one four-set. -/
theorem not_chargeOK_seven : ¬ chargeOK 7 := by decide

/-- **THERE IS NO ADMISSIBLE SIX-COLOURING OF `K_7`.**  A purely analytic statement: no search is
involved, in contrast with `VertexSearch.certC_seven` (38 654 nodes) and `certD_seven_six`. -/
theorem no_six_of_seven : ¬ (∃ c : Col 7 6, Admissible c) := by
  rintro ⟨c, hc⟩
  exact not_chargeOK_seven (charge_obstruction (by decide) (by decide : ¬ Even 7) hc)

/-- **`chargeOK 5` FAILS.**  `C(5,2)² - 4·C(5,2) + 1·4·4 = 76 > 40 = 2·4·C(5,4)`. -/
theorem not_chargeOK_five : ¬ chargeOK 5 := by decide

/-- **THERE IS NO ADMISSIBLE FOUR-COLOURING OF `K_5`** (the second instance of the charge; the
statement itself is `Moment.no_four_of_five`, here re-derived by the charge). -/
theorem charge_no_four_of_five : ¬ (∃ c : Col 5 4, Admissible c) := by
  rintro ⟨c, hc⟩
  exact not_chargeOK_five (charge_obstruction (by decide) (by decide : ¬ Even 5) hc)

/-- **`f(7,4,5) ≥ 7` ANALYTICALLY.**  `Moment.EG_seven_ge_six_census` rules out `k ≤ 5` and
`no_six_of_seven` rules out `k = 6`; together with the attainment `EG_admissible` this is the lower
half of `Main.EG_seven : EG 7 = 7`, reached **without any computer search** — the search
certificate `VertexSearch.certC_seven` is now redundant for this value. -/
theorem EG_seven_ge_seven : 7 ≤ EG 7 := by
  by_contra h
  have h6 := EG_seven_ge_six_census
  have h7 : EG 7 = 6 := by omega
  have h8 := EG_admissible 7
  rw [h7] at h8
  obtain ⟨c, hc⟩ := h8
  exact no_six_of_seven ⟨c, hc⟩

/-- **THE CHARGE DOES NOT EXCLUDE `n = 9`.**  `chargeOK 9` holds, so — like every instrument of this
family — the charge says nothing about the seven-colourings of `K_9` (`EG 9 = 8` still rests on the
search certificate `Nine.certD_nine_six`).  Recorded here so that the next round does not re-derive
it. -/
theorem chargeOK_nine : chargeOK 9 := by decide

/-- … nor about `n = 11` (`EG 11 ≥ 9` is the counting bound `5·10/6`). -/
theorem chargeOK_eleven : chargeOK 11 := by decide

/-- **THE CHARGE IS SATISFIED BY THE VERIFIED CONSTRUCTION `nineCol`** (eight colours on `K_9`,
`k = n - 1`): the instrument does not contradict the witnesses the searches of rounds 45–46
produced.  This is the non-vacuity check of §3. -/
theorem charge_nineCol : chargeOK 9 :=
  charge_obstruction (by decide) (by decide : ¬ Even 9) admissible_nineCol

/-- … and by `elevenCol` (ten colours on `K_{11}`, again `k = n - 1`). -/
theorem charge_elevenCol : chargeOK 11 :=
  charge_obstruction (by decide) (by decide : ¬ Even 11) admissible_elevenCol

/-- **THE LOWER HALF OF `EG 7 = 7`, ANALYTICALLY, IN ONE STATEMENT.**  Both halves of
`Profile.EG_seven_ge_seven`: there is no admissible six-colouring of `K_7`, and `EG 7` is not `6`. -/
theorem EG_seven_lower_half :
    7 ≤ EG 7 ∧ ¬ (∃ c : Col 7 6, Admissible c) :=
  ⟨EG_seven_ge_seven, no_six_of_seven⟩

/-! ### §4  the same conclusion from the profile alone -/

/-- **THE CLASS SIZES OF A SIX-COLOURING OF `K_7` SUM TO 21.** -/
theorem sum_card_classF_seven (c : Col 7 6) : ∑ i : Fin 6, (classF c i).card = 21 := by
  have h := sum_card_classF c
  rw [card_edges, show Nat.choose 7 2 = 21 by decide] at h
  exact h

/-- **THE PAIR COUNT OF A SIX-COLOURING OF `K_7` IS AT LEAST 27.**  This is `Moment.pairs_lower`
at `(7,6)`, where Cauchy–Schwarz gives `26.25` and the integrality of the pair count rounds it up
to `27` — the first place where the integrality of `∑_i choose |E_i| 2` is load-bearing in this
development. -/
theorem sum_choose_two_seven (c : Col 7 6) : 27 ≤ ∑ i : Fin 6, Nat.choose (classF c i).card 2 := by
  have h := pairs_lower c
  rw [show (edgeFinset (Finset.univ : Finset (Verts 7))).card = 21 by
        rw [card_edges]; decide] at h
  omega

/-- **THE CHARGE AT `(7,6)`, WITH NO REFERENCE TO ADMISSIBILITY.**  Every profile of six classes
summing to `21 = C(7,2)` pays at least `3` in cherries. -/
theorem sum_surplus_seven (c : Col 7 6) : 3 ≤ ∑ i : Fin 6, (2 * (classF c i).card - 7) := by
  have hsum : (∑ i : Fin 6, 2 * (classF c i).card) = 7 * 6 := by
    calc (∑ i : Fin 6, 2 * (classF c i).card) = 2 * (∑ i : Fin 6, (classF c i).card) :=
          by rw [← Finset.mul_sum]
      _ = 2 * (edgeFinset (Finset.univ : Finset (Verts 7))).card := by rw [sum_card_classF]
      _ = 7 * 6 := card_edgeFinset_univ_two 7
  have h := sum_surplus_ge (fun i => (classF c i).card) (by decide : ¬ Even 7) hsum
  omega

private lemma profileCost_seven (c : Col 7 6) (i : Fin 6) :
    profileCost 7 c i = Nat.choose (classF c i).card 2 + 3 * (2 * (classF c i).card - 7) := by
  unfold profileCost
  congr 1

/-- **EVERY PROFILE OF SIX CLASSES OF `21` EDGES HAS RELAXED COST AT LEAST 36 > C(7,4) = 35.**
This is the whole content of §3 with admissibility removed: it is a statement about the six
integers `|E_1|, …, |E_6|` summing to `21` only. -/
theorem sum_profileCost_seven_six (c : Col 7 6) : 36 ≤ ∑ i : Fin 6, profileCost 7 c i := by
  have h1 : (∑ i : Fin 6, profileCost 7 c i)
      = ∑ i : Fin 6, (Nat.choose (classF c i).card 2 + 3 * (2 * (classF c i).card - 7)) :=
    Finset.sum_congr (s₁ := (Finset.univ : Finset (Fin 6))) rfl fun i _ => profileCost_seven c i
  have h2 := sum_choose_two_seven c
  have h3 := sum_surplus_seven c
  rw [h1, Finset.sum_add_distrib, ← Finset.mul_sum]
  omega

/-! ### §5  the exclusion misses by one four-set -/

/-- **THE RELAXED COST OF A CLASS OF SIZE 3 ON SEVEN VERTICES IS 3.** -/
theorem cost_three : Nat.choose 3 2 + 3 * (2 * 3 - 7) = 3 := by decide

/-- **THE RELAXED COST OF A CLASS OF SIZE 4 ON SEVEN VERTICES IS 9.** -/
theorem cost_four : Nat.choose 4 2 + 3 * (2 * 4 - 7) = 9 := by decide

/-- **THE BALANCED PROFILE `(4,4,4,3,3,3)` ATTAINS THE BOUND `36`.**  Both halves of
`sum_profileCost_seven_six` are tight simultaneously: the pair count `27 = 3·9` and the charge
`3 = 3·1`.  So `36` is exactly the minimum of the relaxed cost over the profiles of `21` edges in
six classes, and it exceeds `C(7,4) = 35` by **one**. -/
theorem balanced_cost_is_36 :
    3 * (Nat.choose 4 2 + 3 * (2 * 4 - 7)) + 3 * (Nat.choose 3 2 + 3 * (2 * 3 - 7)) = 36 := by
  rw [cost_four, cost_three]

/-- **THE MARGIN IS EXACTLY ONE FOUR-SET.** -/
theorem margin_is_one : Nat.choose 7 4 + 1 = 36 := by decide

end

end JSP140
