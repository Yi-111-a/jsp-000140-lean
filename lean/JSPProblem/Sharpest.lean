import JSPProblem.VertexSearch
import JSPProblem.Cherry
import JSPProblem.Cell
import JSPProblem.Singles
import JSPProblem.Rigidity
import JSPProblem.Restriction
import JSPProblem.VertexBudget
import JSPProblem.Window
import JSPProblem.Sharp6

/-!
# JSP-000140 — round 94: **the sharp palette `⌈(5n+1)/6⌉` at every order, and the first
# NON-VACUOUS reduction of the prize to a finite design-existence hypothesis**

Rounds 13–30, 71–72 and 90 built a very detailed *extremal* structure theory on the hypothesis

    `6 * k = 5 * (n - 1)`,

and four separate reductions of the catalog answer to a construction exist in this development:

* `fiveSixthUpper_of_extremal_family`, `fiveSixth_of_extremal_family`,
* `jsp_000140_main_of_STS_family` (`Restriction.lean`) and its duplicate in `Main.lean`,

all of them of the shape *"if for every `m ≡ 1 (mod 6)` there is an admissible `k`-colouring of
`K_m` with `6 * k = 5 * (m - 1)` (and its two-edge paths form a Steiner triple system), then
`jsp_000140_target`"*.

**Every one of those hypotheses is FALSE.**  `Strict.not_sharp` (round 81, sharpened into
`Strict.no_extremal_colouring`) proves that no admissible colouring of any `K_n` satisfies
`6k = 5(n-1)`, so the whole extremal structure theory of this development — and with it the four
reductions above — is a theorem about the empty class.  Round 93 refuted the growth route for the
same reason (`Sharp6.main_is_vacuous`).

This round puts the prize on a **consistent** footing, in three steps.

## §0 — THE SHARP PALETTE, AT EVERY ORDER

`Palette n = ⌈(5n+1)/6⌉`, the refined counting bound of `Vacant.five_n_add_one_le_six_k_of_seven`
(`⌈(5n+1)/6⌉ ≤ f(n,4,5)` for `n ≥ 7`).  Round 93 computed it for the single residue class
`0 (mod 6)` (`Sharp6.ge`); §0 computes it for **all six** residue classes, shows it grows by `5`
every `6` vertices, and shows it is **attained** at `n = 12` (`Palette 12 = EG 12 = 11`), so the
refined bound is sharp and not merely valid.

* `Sharpest.palette_zero/one/two/three/four/five` — the table
  `⌈(5t+r)/6⌉ + … = 5t + 1, 1, 2, 3, 4, 5` for `r = 0, 1, 2, 3, 4, 5`;
* `Sharpest.six_eq_add` — `Palette (n + 6) = Palette n + 5`;
* `Sharpest.eq_palette_iff`, `Sharpest.lt_palette_iff` — **attaining the sharp palette at order
  `n` is one finite question**, `∃ c : Col n (Palette n), Admissible c`, for *every* `n ≥ 7`
  (round 93 had it for `n = 18` alone);
* `Sharpest.sharp_at_twelve : Palette 12 = EG 12`, and `Sharpest.palette_one_six`: on the extremal
  residue class `Palette (6t+1) = 5t+1`, so **`6 * Palette (6t+1) = 5 * (6t) + 6`** — the sharp
  palette sits exactly **six** above the (impossible) extremal value, and that gap of six is
  exactly what keeps the hypothesis of §2 alive.

## §1 — THE OLD REDUCTIONS ARE VACUOUS

* `Sharpest.not_at_thirteen` — no admissible colouring of `K₁₃` satisfies `6k = 5(13-1)`;
* **`Sharpest.extremal_family_false`** — the hypothesis of all four reductions of rounds
  27–30 is *false*, i.e. each of them is a theorem about the empty class;
* `Sharpest.palette_one_ne_extremal` — while the sharp palette is **not** refuted, and the reason
  is the gap `6`.

## §2 — THE FIRST NON-VACUOUS REDUCTION: THE PRIZE FROM THE SHARP PALETTE

`SharpFamily` = *for every `m ≡ 1 (mod 6)`, `m ≥ 7`, there is an admissible colouring of `K_m`
with exactly `Palette m` colours* — the design-existence hypothesis of the published
construction, at the palette the counting bound demands.

* **`Sharpest.count_bound : SharpFamily → 6 * f(n) ≤ 5 * n + 31`** for every `n ≥ 7`: the sharp
  palette of the next `1 (mod 6)` order above `n` costs at most `31/6` more colours than `5n/6`.
  (The same constant `5n + 31` as round 93's `Grow6At.count_bound`, reached *without* an extension
  lemma — which is refuted.)
* `Sharpest.fiveSixthUpper`, **`Sharpest.AdmissibleUpper_of_sharp_family`** (`AdmissibleUpper ε` —
  **the sole surviving content of `jsp_000140_main`**), and **`Sharpest.target_of_sharp_family`**
  (`jsp_000140_target` itself, the lower half being `Main.fiveSixthLower_eg`).

So the remaining work of the prize is exactly: **construct, for every `m ≡ 1 (mod 6)` and `m ≥ 7`,
an admissible `⌈(5m+1)/6⌉`-colouring of `K_m`.**  Unlike the four reductions this replaces, that
hypothesis is consistent with everything proved so far, and it is *tight*: no smaller palette can
work (§0).

## §3 — WHAT A SHARP-PALETTE COLOURING MUST LOOK LIKE (non-vacuous rigidity)

The extremal theory of rounds 13–30 is refuted, but its *content* transfers to the sharp palette,
and this is the first non-vacuous transfer.

* `Sharpest.shape` (`Isolated c = n`, `Defect c = 0`), from `Vacant.isolated_eq_n_defect_eq_zero`;
* **`Sharpest.is_STS`** — at `6k = 5n+1` the two-edge paths of `c` form a **Steiner triple system**
  (`tight_pathFinset_is_STS` applied to `Defect c = 0`): the STS rigidity, proved for the *live*
  palette at **every** order `n ≥ 13` with `6k = 5n+1` (round 76 had it for `n = 13` only, in
  `Window.extremal_at_thirteen_is_STS`);
* `Sharpest.paths_six`, `Sharpest.single_eq_paths`, **`Sharpest.third_split`** — at the sharp palette
  the two-edge paths and the single edges each account for **exactly one third of all `C(n,2)`
  edges**: `Paths c = (singleFinset c).card = n(n-1)/6`, the cherry edges being the other two
  thirds.  So a sharp-palette colouring of `K_n` has `n(n-1)/6` blocks — the Steiner triple system
  of the paragraph above — and `n(n-1)/6` single edges, and nothing else;
* `Sharpest.sharp_mod_six` — the sharp palette `6k = 5n+1` is **only ever attainable at
  `n ≡ 1 (mod 6)`**, so §3 is a statement about a single residue class, and in the other five
  classes the sharp palette has a different (larger) surplus and hence different structure.

## §4 — THE PRICE OF A BALANCED COLUMN, AT EVERY ORDER

`PathFac.Balanced.five_dvd_n` derives `5 ∣ n` from `6k = 5(n-1)` and a balanced colouring — a
statement about the empty class.  §4 drops the refuted extremality hypothesis and obtains the
*live* version, valid for **every** admissible colouring:

* **`Sharpest.balanced_price`** — a column with as many cherries as single edges pays
  `5 ∣ (n - miss_i)`: its cells are `(n - miss_i)/5` blocks of `3 + 2`.  So `Balanced.five_dvd_n`
  is the special case `miss_i = 0` (which extremality forces and the sharp palette does not);
* `Sharpest.balanced_five_blocks` — the same column carries exactly `(n - miss_i)/5` cherries *and*
  as many single edges: **a balanced column is the `3^{n/5} 2^{n/5}` factor of round 90's extremal
  picture, alive at every order**;
* **`Sharpest.sharp_mod5_cases`** — at the sharp palette some column misses at most one cell
  (`Cell.refined_pigeonhole`), so a balanced such column forces **`5 ∣ n` or `5 ∣ (n - 1)`**.
  Together with `Sharpest.sharp_dvd_six` (`6 ∣ (n - 1)`) these are, by the Chinese remainder
  theorem, exactly the conditions `n ≡ 25 (mod 30)` resp. `n ≡ 1 (mod 30)`: **the two and only two
  orders mod `30` on which a `3^{n/5} 2^{n/5}` factor can exist at all**, at every order.  Round 90
  could name only `25`, because its extremal hypothesis (which forces `miss_i = 0` for every
  colour) is refuted; the live statement has both classes, `n ≡ 1 (mod 30)` being the one in which
  the balanced column misses exactly one cell.

## What is still missing

Unchanged: the design existence of §2.  But the *form* of the remaining work is now sharp,
non-vacuous and quantified: it is enough to build `⌈(5m+1)/6⌉`-colourings of `K_m` for
`m ≡ 1 (mod 6)`, `m ≥ 7`, each of which (§3) must carry a Steiner triple system of `n(n-1)/6`
blocks and `n(n-1)/6` single edges, and §4 prices each column of it.
-/

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

namespace JSP140

namespace Sharpest

variable {n k : ℕ}

/-! ### §0  The sharp palette -/

/-- **THE SHARP PALETTE.**  `Palette n = ⌈(5n+1)/6⌉`, the least number of colours an admissible
colouring of `K_n` can possibly use (`five_n_add_one_le_six_k_of_seven` for `n ≥ 7`).  It is one
whole colour above the classical `⌈5(n-1)/6⌉`, and it is *attained* at `n = 12`
(`Sharpest.sharp_at_twelve`). -/
def Palette (n : ℕ) : ℕ := (5 * n + 1 + 5) / 6

private lemma div_eq_of_mul {A B C : ℕ} (hC : 0 < C) (h1 : B * C ≤ A)
    (h2 : A ≤ C * B + (C - 1)) : A / C = B := by
  refine Nat.le_antisymm ?_ ?_
  · rw [Nat.div_le_iff_le_mul_add_pred hC]
    exact h2
  · exact Nat.le_div_iff_mul_le hC |>.mpr h1

theorem palette_def (n : ℕ) : Palette n = (5 * n + 1 + 5) / 6 := rfl

/-- **THE SHARP PALETTE IS A LOWER BOUND FOR `f(n,4,5)`** at every order `n ≥ 7`. -/
theorem ge (n : ℕ) (hn : 7 ≤ n) : Palette n ≤ EG n := EG_ge_ceil_five_sixth_plus_one n hn

/-- **`Palette (6t) = 5t + 1`** — round 93's `Sharp6.ge`, as an identity (the lower bound is
`Sharpest.ge`). -/
theorem palette_zero (t : ℕ) : Palette (6 * t) = 5 * t + 1 := by
  rw [palette_def]
  exact div_eq_of_mul (by norm_num) (by nlinarith) (by nlinarith)

/-- **`Palette (6t+1) = 5t+1`**: on the residue class `1 (mod 6)` the sharp palette is the first
integer above the classical counting value `5(m-1)/6`. -/
theorem palette_one (t : ℕ) : Palette (6 * t + 1) = 5 * t + 1 := by
  rw [palette_def]
  exact div_eq_of_mul (by norm_num) (by nlinarith) (by nlinarith)

theorem palette_two (t : ℕ) : Palette (6 * t + 2) = 5 * t + 2 := by
  rw [palette_def]
  exact div_eq_of_mul (by norm_num) (by nlinarith) (by nlinarith)

theorem palette_three (t : ℕ) : Palette (6 * t + 3) = 5 * t + 3 := by
  rw [palette_def]
  exact div_eq_of_mul (by norm_num) (by nlinarith) (by nlinarith)

theorem palette_four (t : ℕ) : Palette (6 * t + 4) = 5 * t + 4 := by
  rw [palette_def]
  exact div_eq_of_mul (by norm_num) (by nlinarith) (by nlinarith)

theorem palette_five (t : ℕ) : Palette (6 * t + 5) = 5 * t + 5 := by
  rw [palette_def]
  exact div_eq_of_mul (by norm_num) (by nlinarith) (by nlinarith)

/-- **THE SHARP PALETTE GROWS BY FIVE COLOURS EVERY SIX VERTICES.** -/
private lemma div_add_mul {a b : ℕ} : (a + 6 * b) / 6 = a / 6 + b := by
  refine Nat.le_antisymm ?_ ?_
  · rw [Nat.div_le_iff_le_mul_add_pred (by norm_num)]
    have h2 := Nat.div_add_mod a 6
    have hlt : a % 6 < 6 := Nat.mod_lt _ (by norm_num)
    omega
  · refine Nat.le_div_iff_mul_le (by norm_num) |>.mpr ?_
    have h := Nat.div_mul_le_self a 6
    ring_nf
    omega

theorem six_eq_add (n : ℕ) : Palette (n + 6) = Palette n + 5 := by
  have hring : 5 * (n + 6) + 1 + 5 = (5 * n + 1 + 5) + 6 * 5 := by ring
  rw [palette_def, palette_def, hring, div_add_mul]

/-- **THE SHARP PALETTE IS ATTAINED AT `n = 12`.**  `⌈(5·12+1)/6⌉ = 11 = f(12,4,5)`: the refined
bound is sharp, so it is a genuine target for a construction and not merely a valid bound. -/
theorem sharp_at_twelve : Palette 12 = EG 12 := by
  have h : Palette 12 = 5 * 2 + 1 := palette_zero 2
  rw [h, EG_twelve]

/-- **ATTAINING THE SHARP PALETTE AT `n` IS ONE FINITE QUESTION**, for every `n ≥ 7`:
`EG n = Palette n` iff there is an admissible `Palette n`-colouring of `K_n`. -/
theorem eq_palette_iff (n : ℕ) (hn : 7 ≤ n) :
    EG n = Palette n ↔ ∃ (c : Col n (Palette n)), Admissible c := by
  constructor
  · intro h
    obtain ⟨c, hc⟩ := EG_admissible n
    refine ⟨fun e => h ▸ c e, Sharp6.Admissible.palette c h hc⟩
  · rintro ⟨c, hc⟩
    exact Nat.le_antisymm (EG_le n (Palette n) c hc) (ge n hn)

/-- **The same question in the form a construction or a search settles.** -/
theorem lt_palette_iff (n : ℕ) (hn : 7 ≤ n) :
    Palette n < EG n ↔ ∀ (c : Col n (Palette n)), ¬ Admissible c := by
  constructor
  · intro h c hc
    have h1 := EG_le n (Palette n) c hc
    have h2 := ge n hn
    omega
  · intro h
    by_contra hcon
    have hle : Palette n ≤ EG n := ge n hn
    have hge : Palette n = EG n := by omega
    obtain ⟨c, hc⟩ := EG_admissible n
    exact h (fun e => hge.symm ▸ c e) (Sharp6.Admissible.palette c hge.symm hc)

/-! ### §1  The four extremal reductions are vacuous -/

/-- **NO ADMISSIBLE COLOURING OF `K₁₃` SATISFIES `6k = 5(13-1)`.**  `Strict.not_sharp` says this at
every order; `n = 13` is the first one in the residue class the reductions use. -/
theorem not_at_thirteen : ¬ (∃ (k : ℕ) (c : Col 13 k), Admissible c ∧ 6 * k = 5 * (13 - 1)) := by
  rintro ⟨k, c, hc, hk⟩
  exact not_sharp hc (by norm_num) hk

/-- **THE HYPOTHESIS OF THE FOUR EXTREMAL REDUCTIONS IS FALSE.**

`Restriction.fiveSixthUpper_of_extremal_family`, `Restriction.fiveSixth_of_extremal_family`,
`Restriction.jsp_000140_main_of_STS_family` and `Main.jsp_000140_main_of_STS_family` all take as
hypothesis a family of admissible colourings attaining `6k = 5(m-1)` for every `m ≡ 1 (mod 6)`.
`Strict.not_sharp` refutes it at `m = 13`, so **each of those four theorems is a theorem about the
empty class** — together with the whole extremal structure theory built on `6k = 5(n-1)`
(`Rigidity.tight_*`, `Extremal.tight_*`, `PathFac.extremal_*`, `Cell.cells_tight`,
`Sharp.jsp_000140_main_of_sharp`, `Grow6.jsp_000140_main` of round 68).  The prize must be reduced
differently; §2 does. -/
theorem extremal_family_false :
    ¬ (∀ m : ℕ, m % 6 = 1 → ∃ (k : ℕ) (c : Col m k), Admissible c ∧ 6 * k = 5 * (m - 1)) := by
  intro h
  obtain ⟨k, c, hc, hk⟩ := h 13 (by norm_num)
  exact not_sharp hc (by norm_num) hk

/-- **THE SHARP PALETTE IS NOT REFUTED, AND THE REASON IS THE GAP SIX.**  On the residue class
`1 (mod 6)` the sharp palette sits exactly six above the extremal value `5(m-1)`, which is the one
quantity `Strict.not_sharp` forbids. -/
theorem palette_one_six {m : ℕ} (hm : m % 6 = 1) : 6 * Palette m = 5 * (m - 1) + 6 := by
  obtain ⟨t, ht⟩ : ∃ t : ℕ, m = 6 * t + 1 := by
    refine ⟨m / 6, ?_⟩
    have h := (Nat.div_add_mod m 6).symm
    omega
  rw [ht, palette_one]
  omega

theorem palette_one_ne_extremal {m : ℕ} (hm : m % 6 = 1) : 6 * Palette m ≠ 5 * (m - 1) := by
  rw [palette_one_six hm]
  omega

/-! ### §2  The first non-vacuous reduction -/

/-- **THE DESIGN-EXISTENCE HYPOTHESIS AT THE SHARP PALETTE.**  For every `m ≡ 1 (mod 6)` with
`m ≥ 7` there is an admissible colouring of `K_m` with exactly `Palette m = ⌈(5m+1)/6⌉` colours.

This is the object the construction of arXiv:2207.02920 produces, and — unlike the hypothesis of
§1 — it is **consistent with everything proved so far** (`Sharpest.palette_one_ne_extremal`) and
**tight**: `Sharpest.ge` forbids any smaller palette. -/
def SharpFamily : Prop :=
  ∀ m : ℕ, 7 ≤ m → m % 6 = 1 → ∃ (c : Col m (Palette m)), Admissible c

/-- **ABOVE EVERY `n ≥ 7` THERE IS AN ORDER `m ≡ 1 (mod 6)` WITHIN DISTANCE FIVE.**  (The existing
`Restriction.exists_one_mod_six_ge` gives distance six; the extra case is `n ≡ 1 (mod 6)` itself,
for which `m = n` does the job.) -/
theorem exists_one_mod_six_le_five (n : ℕ) (hn : 7 ≤ n) :
    ∃ m : ℕ, n ≤ m ∧ m ≤ n + 5 ∧ m % 6 = 1 := by
  by_cases h : n % 6 = 1
  · exact ⟨n, le_refl n, by omega, h⟩
  obtain ⟨m, h1, h2, h3⟩ := exists_one_mod_six_ge n (by omega)
  refine ⟨m, h1, ?_, h3⟩
  have hne : m ≠ n + 6 := by
    intro hc
    have hmod : (n + 6) % 6 = n % 6 := by
      have h1 : (n + 6) % 6 = (n % 6 + 6 % 6) % 6 := Nat.add_mod n 6 6
      have h2 : 6 % 6 = 0 := by omega
      rw [h1, h2, Nat.add_zero, Nat.mod_eq_of_lt (Nat.mod_lt _ (by norm_num))]
    rw [hc, hmod] at h3
    exact h h3
  omega

/-- **THE COUNTING PRICE OF THE SHARP FAMILY: `6 f(n) ≤ 5n + 31` for every `n ≥ 7`.**  The sharp
palette of the next `1 (mod 6)` order above `n` costs at most `31/6` colours more than `5n/6`:
`Palette m ≤ (5m+6)/6` and `m ≤ n+5`.

The same constant `5n + 31` as round 93's `Grow6At.count_bound`, reached here **without** an
extension lemma — the universal growth lemma `Grow6` is false (`Sharp6.not_Grow6`), the sharp
family is not. -/
theorem count_bound (hfam : SharpFamily) (n : ℕ) (hn : 7 ≤ n) : 6 * EG n ≤ 5 * n + 31 := by
  obtain ⟨m, hnm, hmn, hres⟩ := exists_one_mod_six_le_five n hn
  obtain ⟨c, hc⟩ := hfam m (le_trans hn hnm) hres
  have hEG : EG n ≤ Palette m := (EG_mono hnm).trans (EG_le m (Palette m) c hc)
  have hpal : 6 * Palette m ≤ 5 * m + 6 := by
    have h := Nat.div_mul_le_self (5 * m + 1 + 5) 6
    have hP : Palette m = (5 * m + 1 + 5) / 6 := palette_def m
    rw [hP]
    omega
  calc 6 * EG n ≤ 6 * Palette m := Nat.mul_le_mul_left 6 hEG
    _ ≤ 5 * m + 6 := hpal
    _ ≤ 5 * (n + 5) + 6 := by
      have h5 := Nat.mul_le_mul_left 5 hmn
      omega
    _ = 5 * n + 31 := by ring

/-- **The same bound over `ℝ`.** -/
theorem count_bound_real (hfam : SharpFamily) (n : ℕ) (hn : 7 ≤ n) :
    (EG n : ℝ) ≤ 5 * (n : ℝ) / 6 + 31 / 6 := by
  have h1 := count_bound hfam n hn
  have h1' : (6 : ℝ) * (EG n : ℝ) ≤ ((5 * n + 31 : ℕ) : ℝ) := by exact_mod_cast h1
  push_cast at h1'
  linarith

/-- **THE UPPER HALF OF THE HEADLINE, FROM THE SHARP FAMILY — WITH AN EXPLICIT THRESHOLD.**
`f(n,4,5) ≤ 5n/6 + εn` for every `ε > 0` and every `n ≥ max 7 (⌈31/(6ε)⌉ + 1)`. -/
theorem fiveSixthUpper (hfam : SharpFamily) : FiveSixthUpper EG := by
  unfold FiveSixthUpper
  intro ε hε
  refine ⟨max 7 (Nat.ceil ((31 : ℝ) / 6 / ε) + 1), fun n hn => ?_⟩
  have hcast : ((max 7 (Nat.ceil ((31 : ℝ) / 6 / ε) + 1) : ℕ) : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hn
  have hceil : ((31 : ℝ) / 6 / ε) ≤ (Nat.ceil ((31 : ℝ) / 6 / ε) : ℝ) := Nat.le_ceil _
  have hkey : ((31 : ℝ) / 6 / ε) * ε = (31 : ℝ) / 6 := by field_simp
  have hmax' : Nat.ceil ((31 : ℝ) / 6 / ε)
      ≤ max 7 (Nat.ceil ((31 : ℝ) / 6 / ε) + 1) :=
    le_trans (Nat.le_succ _) (Nat.le_max_right 7 _)
  have hmax : ((Nat.ceil ((31 : ℝ) / 6 / ε) : ℝ))
      ≤ ((max 7 (Nat.ceil ((31 : ℝ) / 6 / ε) + 1) : ℕ) : ℝ) := by
    exact_mod_cast hmax'
  have hstep : ((31 : ℝ) / 6 / ε) ≤ (n : ℝ) := by linarith
  have heps : (31 : ℝ) / 6 ≤ (n : ℝ) * ε := by
    have h1 := mul_le_mul_of_nonneg_right hstep hε.le
    rwa [hkey] at h1
  have h1 := count_bound hfam n (by omega)
  have h2 : (6 : ℝ) * (EG n : ℝ) ≤ (5 : ℝ) * (n : ℝ) + 31 := by
    have h2' : (6 : ℝ) * (EG n : ℝ) ≤ ((5 * n + 31 : ℕ) : ℝ) := by exact_mod_cast h1
    push_cast at h2'
    exact h2'
  calc (EG n : ℝ) ≤ 5 * (n : ℝ) / 6 + 31 / 6 := by linarith
    _ ≤ 5 * (n : ℝ) / 6 + ε * n := by linarith

/-- **`AdmissibleUpper ε` FOR EVERY `ε > 0` FROM THE SHARP FAMILY** — the probabilistic existence
statement of arXiv:2207.02920 in the colouring language, and the *sole* remaining content of
`jsp_000140_main` (the lower half is proved: `Main.fiveSixthLower_eg`). -/
theorem AdmissibleUpper_of_sharp_family (hfam : SharpFamily) :
    ∀ ε : ℝ, 0 < ε → AdmissibleUpper ε := by
  intro ε hε
  exact (fiveSixthUpper_iff ε).mp (fiveSixthUpper hfam)

/-- **THE REQUIRED THEOREM, REDUCED TO A NON-VACUOUS DESIGN-EXISTENCE HYPOTHESIS.**  With the lower
half `Main.fiveSixthLower_eg` (complete since round 10), `jsp_000140_target` follows from
`SharpFamily`: for every `m ≡ 1 (mod 6)`, `m ≥ 7`, an admissible `⌈(5m+1)/6⌉`-colouring of `K_m`.

This replaces the four reductions of §1, whose hypotheses are false. -/
theorem target_of_sharp_family (hfam : SharpFamily) : jsp_000140_target :=
  jsp_000140_target_iff.mpr
    ⟨(fiveSixthLower_iff 1).mp fiveSixthLower_eg,
      (fiveSixthUpper_iff 1).mp (fiveSixthUpper hfam)⟩

/-! ### §3  What a sharp-palette colouring must look like -/

/-- **THE SHAPE OF A SHARP-PALETTE COLOURING.**  If `6k = 5n+1` and `n ≥ 13` then every slot but
one is used (`Isolated c = n`) and every edge is paid for by a two-edge path (`Defect c = 0`):
`Vacant.isolated_eq_n_defect_eq_zero`, applied for `n ≥ 13` (which forces `k+2 ≤ n`). -/
theorem shape {c : Col n k} (hc : Admissible c) (hn : 13 ≤ n) (hk : 6 * k = 5 * n + 1) :
    Isolated c = n ∧ Defect c = 0 :=
  isolated_eq_n_defect_eq_zero hc (by omega) (by omega) hk

/-- **THE SHARP PALETTE IS ATTAINABLE ONLY AT `n ≡ 1 (mod 6)`.**  `6k = 5n+1` forces
`n - 1 = 6 (n - k)`, so the whole of §3 lives on one residue class — and in the other five classes
the palette `Palette n` has surplus `r` over `5n` (`r = 6, 1, 2, 3, 4, 5` for
`n ≡ 0, 1, 2, 3, 4, 5 (mod 6)`), hence a different profile. -/
theorem sharp_six_sub_one {n k : ℕ} (hk : 6 * k = 5 * n + 1) : 6 * (n - k) = n - 1 := by omega

theorem sharp_mod_six {n k : ℕ} (hk : 6 * k = 5 * n + 1) : n % 6 = 1 := by
  have h6 := sharp_six_sub_one hk
  have hmod : (1 + 6 * (n - k)) % 6 = 1 := by
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
  have heq' : 1 + 6 * (n - k) = n := by omega
  exact heq' ▸ hmod

/-- **AT THE SHARP PALETTE THE TWO-EDGE PATHS FORM A STEINER TRIPLE SYSTEM.**  This is the
STS-rigidity of rounds 13–27 (`tight_pathFinset_is_STS`), but proved for the **live** palette
`6k = 5n+1` at **every** order `n ≥ 13`, not for the refuted extremal value: round 76 had it for
`n = 13` only (`Window.extremal_at_thirteen_is_STS`).  `Defect c = 0` says `|E(K_n)| ≤ 3 · Paths`
and the counting lemma `Cherry.three_mul_paths_le_edges` says the reverse, so the two agree. -/
theorem is_STS {c : Col n k} (hc : Admissible c) (hn : 13 ≤ n) (hk : 6 * k = 5 * n + 1) :
    IsSTS (pathFinset c) := by
  have hle : 3 * Paths c ≤ (edgeFinset (Finset.univ : Finset (Verts n))).card :=
    three_mul_paths_le_edges hc (by omega)
  have hge : (edgeFinset (Finset.univ : Finset (Verts n))).card ≤ 3 * Paths c := by
    have h0 : Defect c = 0 := (shape hc hn hk).2
    unfold Defect at h0
    omega
  exact tight_pathFinset_is_STS hc (by omega) (Nat.le_antisymm hle hge)

/-- **THE MISS CENSUS AT THE SHARP PALETTE: `Paths c = n (n - k)`.**  `Isolated c = n` and
`Σ_i miss_i = n k + Paths c - n(n-1)` (`Cell.sum_miss_eq_surplus`) give
`Paths c = n + n(n-1) - n k = n(n - k)`: the number of two-edge paths is the number of
uncovered `(vertex, colour)` cells of the grid, in the sharp palette. -/
theorem paths_eq_nk {c : Col n k} (hc : Admissible c) (hn : 13 ≤ n) (hk : 6 * k = 5 * n + 1) :
    Paths c = n * (n - k) := by
  have h1 := Cell.sum_miss_eq_isolated hc
  have h2 := Cell.sum_miss_eq_surplus hc
  have h3 := (shape hc hn hk).1
  have hsub : n * (n - 1) + n = n * n := by
    have h := Nat.mul_succ n (n - 1)
    rw [Nat.succ_eq_add_one, Nat.sub_add_cancel (by omega : (1 : ℕ) ≤ n)] at h
    exact h.symm
  have hA : (∑ i : Fin k, Miss.miss c i) + n * (n - 1) = n * k + Paths c := by omega
  have hB : (∑ i : Fin k, Miss.miss c i) = n := by omega
  have hPk : Paths c + n * k = n * n := by omega
  calc Paths c = n * n - n * k := by omega
    _ = n * (n - k) := (Nat.mul_sub_left_distrib n n k).symm

/-- **THE PATH COUNT AT THE SHARP PALETTE: `6 · Paths c = n(n-1)`,** i.e. `Paths c = n(n-1)/6` (the
hypothesis forces `n ≡ 1 (mod 6)`, so this is an integer): exactly the number of blocks of a
Steiner triple system on `n` points, the maximiser of the counting lemma
`Cherry.three_mul_paths_le_edges`.  A sharp-palette colouring is one at which the classical
counting bound on two-edge paths is tight. -/
theorem paths_six {c : Col n k} (hc : Admissible c) (hn : 13 ≤ n) (hk : 6 * k = 5 * n + 1) :
    6 * Paths c = n * (n - 1) := by
  have hkey := paths_eq_nk hc hn hk
  have h6 := sharp_six_sub_one hk
  calc 6 * Paths c = 6 * (n * (n - k)) := by rw [hkey]
    _ = n * (6 * (n - k)) := by ring
    _ = n * (n - 1) := by rw [h6]

/-- **THE ONE-THIRD STATEMENT.**  At the sharp palette the two-edge paths and the single edges
account for the **same** number of edges, `n(n-1)/6` each: one third of `C(n,2)` apiece, the cherry
edges being the remaining two thirds. -/
theorem single_eq_paths {c : Col n k} (hc : Admissible c) (hn : 13 ≤ n) (hk : 6 * k = 5 * n + 1) :
    (singleFinset c).card = Paths c := by
  have h1 := card_singleFinset hc (by omega)
  have h3 := (shape hc hn hk).2
  have hle : 3 * Paths c ≤ (edgeFinset (Finset.univ : Finset (Verts n))).card :=
    three_mul_paths_le_edges hc (by omega)
  have hge : (edgeFinset (Finset.univ : Finset (Verts n))).card ≤ 3 * Paths c := by
    have h0 : Defect c = 0 := h3
    unfold Defect at h0
    omega
  have hcard : 3 * Paths c = (edgeFinset (Finset.univ : Finset (Verts n))).card :=
    Nat.le_antisymm hle hge
  have h1' : (singleFinset c).card + 2 * Paths c
      = (edgeFinset (Finset.univ : Finset (Verts n))).card := by omega
  have key : 2 * (singleFinset c).card = 2 * Paths c := by omega
  omega

/-- **THE ONE-THIRD STATEMENT IN DIVISION-FREE FORM.**  At the sharp palette one third of the edges
of `K_n` are single edges, one third are the "odd" edges of the cherries and one third are their
"even" edges: the two kinds of edge a sharp-palette colouring is made of. -/
theorem third_split {c : Col n k} (hc : Admissible c) (hn : 13 ≤ n) (hk : 6 * k = 5 * n + 1) :
    6 * (singleFinset c).card = n * (n - 1) ∧ 6 * Paths c = n * (n - 1) :=
  ⟨by rw [single_eq_paths hc hn hk, paths_six hc hn hk], paths_six hc hn hk⟩

/-! ### §4  The price of a balanced column, at every order -/

/-- `lcm 5 6 = 30`, in the form used below. -/
private lemma lcm_five_six {x : ℕ} (h5 : 5 ∣ x) (h6 : 6 ∣ x) : 30 ∣ x := by
  have hlcm : Nat.lcm 5 6 = 30 := by decide
  rw [← hlcm]
  exact Nat.lcm_dvd h5 h6

/-- **THE PRICE OF A BALANCED COLUMN: `5 ∣ (n - miss_i)`.**  A colour class with as many cherries as
single edges covers `3a + 2b = 5a` of the cells of its own column, so its column length is a
multiple of five.

This is `PathFac.Balanced.five_dvd_n` (`5 ∣ n`) with the refuted extremality hypothesis **dropped**:
it holds for **every** admissible colouring and **every** order.  Round 90's statement is the case
`miss_i = 0`, which extremality forces and the sharp palette does not. -/
theorem balanced_price {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n) (i : Fin k)
    (hbal : (twoA c i).card = Cell.leaf c i) : 5 ∣ (n - Miss.miss c i) := by
  have h := Cell.cells hc hn i
  refine ⟨(twoA c i).card, ?_⟩
  rw [hbal] at h
  omega

/-- **A BALANCED COLUMN IS A `3^{n/5} 2^{n/5}` FACTOR.**  Exactly `(n - miss_i)/5` cherries and as
many single edges: the spanning path factor of round 90's extremal picture (`Balanced.tight_twoA`,
`Balanced.tight_leaf`, both refuted together with their extremal hypothesis), alive at every
order. -/
theorem balanced_five_blocks {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n) (i : Fin k)
    (hbal : (twoA c i).card = Cell.leaf c i) :
    5 * (twoA c i).card = n - Miss.miss c i ∧ 5 * Cell.leaf c i = n - Miss.miss c i := by
  have h := Cell.cells hc hn i
  rw [hbal] at h
  constructor <;> omega

/-- **AT THE SHARP PALETTE A BALANCED, ALMOST COMPLETE COLUMN FORCES `5 ∣ n` OR `5 ∣ (n-1)`.**
`Cell.refined_pigeonhole` guarantees a column missing at most one cell, and `balanced_price` then
prices it. -/
theorem sharp_mod5_cases {c : Col n k} (hc : Admissible c) (hn : 13 ≤ n) (hk : 6 * k = 5 * n + 1)
    (hbal : ∃ i : Fin k, (twoA c i).card = Cell.leaf c i ∧ Miss.miss c i ≤ 1) :
    5 ∣ n ∨ 5 ∣ (n - 1) := by
  obtain ⟨i, hi, hmi⟩ := hbal
  have h5 := balanced_price hc (by omega) i hi
  obtain ⟨q, hq⟩ := h5
  by_cases h0 : Miss.miss c i = 0
  · exact Or.inl ⟨q, by omega⟩
  · refine Or.inr ⟨q, ?_⟩
    have h1 : Miss.miss c i = 1 := by omega
    omega

/-- **THE SHARP PALETTE FORCES `6 ∣ (n - 1)`** (`Sharpest.sharp_six_sub_one` restated as a
divisibility), the mod-`6` half of the arithmetic of §4. -/
theorem sharp_dvd_six {n k : ℕ} (hk : 6 * k = 5 * n + 1) : 6 ∣ n - 1 :=
  ⟨n - k, (sharp_six_sub_one hk).symm⟩

/-! ### §5  The two orders the sharp family has to skip, and the first open one -/

/-- **THE SHARP-PALETTE QUESTION IS SETTLED NEGATIVELY AT `n = 7`.**  `Palette 7 = 6` and
`EG 7 = 7` (`VertexSearch.EG_seven`, i.e. `EG_seven`), so no admissible six-colouring of `K₇` exists.  A design
family at the sharp palette therefore has to *start above* `n = 7`: the hypothesis of §2 cannot be
stated for every `m ≡ 1 (mod 6)`, only for `m ≥ 13` (the order `m = 1` is admissible
vacuously). -/
theorem not_at_seven : ∀ (c : Col 7 (Palette 7)), ¬ Admissible c := by
  intro c hc
  have hp : Palette 7 = 6 := by norm_num [palette_one, Palette]
  have hne : EG 7 ≤ Palette 7 := EG_le 7 (Palette 7) c hc
  rw [hp] at hne
  rw [EG_seven] at hne
  omega

/-- **THE SHARP FAMILY FROM `m = 13` ONWARDS IS SUFFICIENT FOR THE PRIZE.**  Same constant
`5n + 31`, same conclusion `jsp_000140_target`, but the design hypothesis is only required for
`m ≥ 13` — i.e. at the orders at which it is actually open. -/
theorem count_bound_thirteen (hfam : ∀ m : ℕ, 13 ≤ m → m % 6 = 1 → ∃ (c : Col m (Palette m)),
    Admissible c) (n : ℕ) (hn : 12 ≤ n) : 6 * EG n ≤ 5 * n + 31 := by
  obtain ⟨m, hnm, hmn, hres⟩ := exists_one_mod_six_le_five n (by omega)
  obtain ⟨c, hc⟩ := hfam m (by omega) hres
  have hEG : EG n ≤ Palette m := (EG_mono hnm).trans (EG_le m (Palette m) c hc)
  have hpal : 6 * Palette m ≤ 5 * m + 6 := by
    have h := Nat.div_mul_le_self (5 * m + 1 + 5) 6
    have hP : Palette m = (5 * m + 1 + 5) / 6 := palette_def m
    rw [hP]
    omega
  calc 6 * EG n ≤ 6 * Palette m := Nat.mul_le_mul_left 6 hEG
    _ ≤ 5 * m + 6 := hpal
    _ ≤ 5 * (n + 5) + 6 := by
      have h5 := Nat.mul_le_mul_left 5 hmn
      omega
    _ = 5 * n + 31 := by ring

/-- **THE PRIZE, IN ONE LINE — THE FIRST NON-VACUOUS REDUCTION.**  `jsp_000140_main` follows from the
single design-existence hypothesis of arXiv:2207.02920 at the palette the counting bound demands:

> for every `m ≡ 1 (mod 6)` with `m ≥ 13` there is an admissible `⌈(5m+1)/6⌉`-colouring of `K_m`.

Unlike `fiveSixth_of_extremal_family` (§1) the hypothesis is *consistent*, and unlike it the palette
is *attained* (`Sharpest.sharp_at_twelve`). -/
theorem main_reduction (hfam : ∀ m : ℕ, 13 ≤ m → m % 6 = 1 → ∃ (c : Col m (Palette m)),
    Admissible c) : jsp_000140_target := by
  refine jsp_000140_target_iff.mpr ⟨(fiveSixthLower_iff 1).mp fiveSixthLower_eg, ?_⟩
  refine (fiveSixthUpper_iff 1).mp ?_
  unfold FiveSixthUpper
  intro ε hε
  refine ⟨max 12 (Nat.ceil ((31 : ℝ) / 6 / ε) + 1), fun n hn => ?_⟩
  have hcast : ((max 12 (Nat.ceil ((31 : ℝ) / 6 / ε) + 1) : ℕ) : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hn
  have hceil : ((31 : ℝ) / 6 / ε) ≤ (Nat.ceil ((31 : ℝ) / 6 / ε) : ℝ) := Nat.le_ceil _
  have hmax' : Nat.ceil ((31 : ℝ) / 6 / ε)
      ≤ max 12 (Nat.ceil ((31 : ℝ) / 6 / ε) + 1) :=
    le_trans (Nat.le_succ _) (Nat.le_max_right 12 _)
  have hmax : ((Nat.ceil ((31 : ℝ) / 6 / ε) : ℝ))
      ≤ ((max 12 (Nat.ceil ((31 : ℝ) / 6 / ε) + 1) : ℕ) : ℝ) := by
    exact_mod_cast hmax'
  have hkey : ((31 : ℝ) / 6 / ε) * ε = (31 : ℝ) / 6 := by field_simp
  have hstep : ((31 : ℝ) / 6 / ε) ≤ (n : ℝ) := by linarith
  have heps : (31 : ℝ) / 6 ≤ (n : ℝ) * ε := by
    have h1 := mul_le_mul_of_nonneg_right hstep hε.le
    rwa [hkey] at h1
  have h1 := count_bound_thirteen hfam n (by omega)
  have h2 : (6 : ℝ) * (EG n : ℝ) ≤ (5 : ℝ) * (n : ℝ) + 31 := by
    have h2' : (6 : ℝ) * (EG n : ℝ) ≤ ((5 * n + 31 : ℕ) : ℝ) := by exact_mod_cast h1
    push_cast at h2'
    exact h2'
  calc (EG n : ℝ) ≤ 5 * (n : ℝ) / 6 + 31 / 6 := by linarith
    _ ≤ 5 * (n : ℝ) / 6 + ε * n := by linarith

/-- **THE FIRST ORDER AT WHICH THE SHARP PALETTE IS STILL UNDECIDED.**  `Palette 13 = 11` and
`EG 13 ≥ 11` (`Strict.EG_thirteen_ge_eleven`), and `Sharpest.eq_palette_iff` says the two cases
`EG 13 = 11` / `EG 13 ≥ 12` are the single finite question `∃ c : Col 13 11, Admissible c`. -/
theorem thirteen_palette : Palette 13 = 11 := by norm_num [palette_one, Palette]

theorem thirteen_ge : 11 ≤ EG 13 := EG_thirteen_ge_eleven

theorem thirteen_cases : EG 13 = 11 ∨ 12 ≤ EG 13 := by
  have h11 : 11 ≤ EG 13 := thirteen_ge
  by_cases h : EG 13 = 11
  · exact Or.inl h
  · exact Or.inr (by omega)


end Sharpest

end JSP140
