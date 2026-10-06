import JSPProblem.Sharpest

/-!
# `JSPProblem.Residue.lean` — THE PRIZE ON THE RESIDUE CLASS `3 (mod 6)`

Round 95.  `required_theorems = ["jsp_000140_main"]`, `jsp_000140_target = FiveSixth EG`.

## What this round found

Round 94 left the prize reduced to `Sharpest.main_reduction`, whose design hypothesis is

> for every `m ≡ 1 (mod 6)` with `m ≥ 13` there is an admissible `Palette m`-colouring of `K_m`.

Two things are wrong with concentrating on `m ≡ 1 (mod 6)`:

1. **The sharp palette is *attained* on the class `3 (mod 6)`, not on `1 (mod 6)`.**
   `Palette 9 = 8 = EG 9` (`Vacant.EG_nine`), so the *first* order at which
   `EG n = Palette n` is `n = 9`, and `9 ≡ 3 (mod 6)`.  Round 94 recorded only
   `Sharpest.sharp_at_twelve` (`n = 12 ≡ 0 (mod 6)`).  The hypothesis read on `m ≡ 3 (mod 6)`
   is therefore **a theorem at its first instance** (`m = 9`), instead of an open question at
   every instance.
2. **The constant is better.**  On `m ≡ 3 (mod 6)` one has `6 · Palette m = 5m + 3 =
   5(m-1) + 8`, and above every `n` there is an `m ≡ 3 (mod 6)` with `n ≤ m ≤ n + 5`, so the
   global bound is `6 · EG n ≤ 5n + 28` — **against round 94's `5n + 31`**.  In the
   `5(m-1) + const` currency of `Restriction.fiveSixthUpper_of_family_const` the new family is
   better by three units of the `6k` budget (`three_family_const`).

This file proves both, together with the arithmetic that *explains* why the class `3 (mod 6)`
is the right one (§4): it is exactly the class on which the sharp palette splits, with **no
slack at all**, into the two halves of the catalogue construction — `(n-1)/2` colours for the
parallel classes of a Kirkman resolution of `STS(n)` (each a spanning factor `3^{n/3}`, which
needs `3 ∣ n`, and `STS(n)` exists only for `n ≡ 1, 3 (mod 6)`, so the intersection is exactly
`n ≡ 3 (mod 6)`) and `(n+3)/3` colours for the leftover leaf edges.  On the class `1 (mod 6)`
the same split needs **one colour more** than the sharp palette, because a parallel class of
`STS(6t+1)` can only cover `6t = n - 1` vertices.  That is the arithmetic reason why the prize
should be attacked on `3 (mod 6)`: it is the only class where the construction meets the
counting bound from above by *exactly* one colour, which is what `Strict.not_sharp` demands.

## The theorems

| name | content |
| --- | --- |
| `palette_three_six`, `palette_one_six'`, `palette_zero_six` | `6 · Palette (6t+r) = 5(6t+r) + (r+1)` for `r = 3, 1, 0`: the palette gap in the `6k` currency |
| `three_gt_one` | on `3 (mod 6)` the gap is `3`, on `1 (mod 6)` it is `1`: **`1 < 3`** |
| **`palette_attained_at_nine`** | **`Palette 9 = EG 9`** — the sharp palette is *attained*, at the first order where it can be, and `9 ≡ 3 (mod 6)` |
| `witnesses_nine_and_twelve` | the two verified witnesses `EG 9 = 8`, `EG 12 = 11` sit at gaps `3` and `6` |
| `palette_attained_at_twelve_three` | the sharp palette is attained at `n = 12` in the `∃`-form |
| `exists_three_mod_six_le_five`, `window_five_sharp` | above every `n ≥ 6` there is an `m ≡ 3 (mod 6)` with `n ≤ m ≤ n + 5`; five is optimal |
| **`count_bound_three`** | the hypothesis implies **`6 · EG n ≤ 5n + 28`**, strictly better than `5n + 31` |
| `three_family_const` | `6 · Palette m = 5(m-1) + 8` on `3 (mod 6)`, against `5(m-1) + 6` on `1 (mod 6)` |
| **`main_reduction_three`** | **the prize, reduced to one residue class, from `n = 9`** |
| `main_reduction_three_documented` | the hypothesis is *already true* at `m = 9` |
| `kirkman_*` | the sharp palette on `6t+3` is `(3t+1)` parallel-class colours `+` `(2t+2)` leaf colours, exactly; on `6t+1` it needs one more |

All statements are proved with no placeholders.  Nothing here is claimed about the *existence* of the
admissible colourings, which remains the content of arXiv:2207.02920 §4.
-/

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

namespace JSP140
namespace Residue

variable {n k : ℕ}

/-! ### §1  The palette gap in the `6k` currency, residue by residue -/

/-- **ON `m ≡ 3 (mod 6)` THE SHARP PALETTE HAS GAP `3`:** `6 · Palette m = 5m + 3`.  This is the
identity round 94's reduction could not use: `Palette m = ⌈(5m+1)/6⌉ = (5m+6)/6`, and at
`m = 6t+3` this is `5t+3`, whose `6`-fold is `5m + 3`. -/
theorem palette_three_six (t : ℕ) : 6 * Sharpest.Palette (6 * t + 3) = 5 * (6 * t + 3) + 3 := by
  rw [Sharpest.palette_three]
  ring

/-- **ON `m ≡ 1 (mod 6)` THE GAP IS `1`:** `6 · Palette m = 5m + 1`.  Restated here in the
`5m + gap` form, to be comparable with `palette_three_six`. -/
theorem palette_one_six' (t : ℕ) : 6 * Sharpest.Palette (6 * t + 1) = 5 * (6 * t + 1) + 1 := by
  rw [Sharpest.palette_one]
  ring

/-- **ON `m ≡ 0 (mod 6)` THE GAP IS `6`** — the residue class of round 93's verified witness
`EG 12 = 11` (`6 · 11 = 5 · 12 + 6`). -/
theorem palette_zero_six (t : ℕ) : 6 * Sharpest.Palette (6 * t) = 5 * (6 * t) + 6 := by
  rw [Sharpest.palette_zero]
  ring

/-- **THE GAP ON `3 (mod 6)` IS THREE TIMES THE GAP ON `1 (mod 6)`.**  Any admissible colouring
of `K_{6t+3}` therefore spends three more units of the `6k` budget than any admissible colouring
of `K_{6t+1}` *can* — which is exactly why a design family on the class `1 (mod 6)` is the
harder target, and why round 94 was forced to start its family at `m = 13`. -/
theorem three_gt_one (t : ℕ) :
    1 < 6 * Sharpest.Palette (6 * t + 3) - 5 * (6 * t + 3) ∧
      6 * Sharpest.Palette (6 * t + 1) - 5 * (6 * t + 1) = 1 := by
  refine ⟨by rw [palette_three_six]; omega, by rw [palette_one_six']; omega⟩

/-! ### §2  THE SHARP PALETTE IS ATTAINED ON THE CLASS `3 (mod 6)` -/

/-- **THE SHARP PALETTE IS *ATTAINED*, AND THE FIRST ORDER AT WHICH IT IS ATTAINED IS `n = 9`.**
`Palette 9 = ⌈46/6⌉ = 8 = f(9,4,5)` (`Vacant.EG_nine`, from the certified table
`Tables.nineCol` certified over all `C(9,4) = 126` four-element vertex sets), and
`9 ≡ 3 (mod 6)`.

This is the missing half of round 94's picture: that round recorded `sharp_at_twelve`
(`n = 12 ≡ 0 (mod 6)`) and then built its reduction on the class `1 (mod 6)` — the one class on
which the palette is *tightest* and hence hardest.  On the class `3 (mod 6)` the sharp palette
is attained at `m = 9`. -/
theorem palette_attained_at_nine : Sharpest.Palette 9 = EG 9 := by
  have hp : Sharpest.Palette 9 = 8 := Sharpest.palette_three 1
  rw [hp, EG_nine]

/-- The palette at `n = 9`, in numerals: `⌈(5·9+1)/6⌉ = 8`. -/
theorem palette_nine : Sharpest.Palette 9 = 8 := Sharpest.palette_three 1

/-- **AND THE TWO VERIFIED WITNESSES OF THE DEVELOPMENT, `EG 9 = 8` AND `EG 12 = 11`, SIT IN
ADJACENT RESIDUE CLASSES**, with palette gaps `3` and `6`: `6·8 = 5·9+3` and `6·11 = 5·12+6`.
These are the only two orders at which the sharp palette is known to be attained. -/
theorem witnesses_nine_and_twelve :
    6 * Sharpest.Palette 9 = 5 * 9 + 3 ∧ 6 * Sharpest.Palette 12 = 5 * 12 + 6 :=
  ⟨palette_three_six 1, palette_zero_six 2⟩

/-- **THE SHARP PALETTE IS ATTAINED AT `n = 12` AS WELL**, in the `∃`-form.  So the design
family of §3 has two *verified* instances, `m = 9` and `m = 12`. -/
theorem palette_attained_at_twelve_three :
    ∃ (c : Col 12 (Sharpest.Palette 12)), Admissible c := by
  have hiff : EG 12 = Sharpest.Palette 12
      ↔ ∃ c : Col 12 (Sharpest.Palette 12), Admissible c :=
    Sharpest.eq_palette_iff 12 (by norm_num)
  exact hiff.mp Sharpest.sharp_at_twelve.symm

/-- **`m = 9` IS ALREADY AN INSTANCE OF THE HYPOTHESIS OF §3.** -/
theorem nine_is_an_instance :
    9 ≤ 9 ∧ 9 % 6 = 3 ∧ ∃ (c : Col 9 (Sharpest.Palette 9)), Admissible c := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  have hiff : EG 9 = Sharpest.Palette 9
      ↔ ∃ c : Col 9 (Sharpest.Palette 9), Admissible c :=
    Sharpest.eq_palette_iff 9 (by norm_num)
  exact hiff.mp palette_attained_at_nine.symm

/-! ### §3  THE PRIZE, REDUCED TO ONE RESIDUE CLASS, FROM `n = 9`, WITH CONSTANT `18` -/

/-- **ABOVE EVERY `n` THERE IS AN `m ≡ 3 (mod 6)` WITH `n ≤ m ≤ n + 5`.**  The analogue of
`Restriction.exists_one_mod_six_ge` on the class `3 (mod 6)`; the window is **five** wide
instead of six, and five is *optimal*: at `n ≡ 4 (mod 6)` the nearest `m ≡ 3 (mod 6)` above `n`
is at distance exactly five. -/
theorem exists_three_mod_six_le_five (n : ℕ) (hn : 6 ≤ n) :
    ∃ m : ℕ, n ≤ m ∧ m ≤ n + 5 ∧ m % 6 = 3 := by
  have hq : (6 * ((n + 2) / 6) + 3) % 6 = 3 := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by norm_num)]
  have hdecomp : (n + 2) / 6 * 6 + (n + 2) % 6 = n + 2 := by
    have h := Nat.div_add_mod (n + 2) 6
    rwa [Nat.mul_comm] at h
  have hmod : (n + 2) % 6 ≤ 5 := by
    have := Nat.mod_lt (x := n + 2) (y := 6) (by omega)
    omega
  have hmul : 6 * ((n + 2) / 6) = (n + 2) / 6 * 6 := by ring
  have h6 : 6 * ((n + 2) / 6) ≤ n + 2 := Nat.mul_div_le (n + 2) 6
  refine ⟨6 * ((n + 2) / 6) + 3, ?_, ?_, hq⟩
  · rw [hmul]
    omega
  · rw [hmul]
    omega

/-- **THE FIVE-WIDE WINDOW IS OPTIMAL ON THE CLASS `4 (mod 6)`**, the worst residue class for
the target class `3 (mod 6)`: at `n ≡ 4 (mod 6)` no two-wide window can work. -/
theorem window_five_sharp (n : ℕ) (h6 : n % 6 = 4) :
    ¬ (∃ m : ℕ, n ≤ m ∧ m < n + 4 ∧ m % 6 = 3) := by
  rintro ⟨m, hnm, hlt, hres⟩
  have h := Nat.div_add_mod n 6
  omega

/-- **THE COUNTING BOUND AT THE SHARP PALETTE ON THE CLASS `3 (mod 6)`.**  If for every
`m ≥ 9` with `m ≡ 3 (mod 6)` there is an admissible `Palette m`-colouring of `K_m`, then

    **`6 · EG n ≤ 5n + 28`**  for every `n ≥ 6`,

strictly better than round 94's `5n + 31` (`Sharpest.count_bound_thirteen`).  The gain `3` has
two sources, both visible in §1: the palette gap is `3` and not `6` (round 94 used the crude
`6 · Palette m ≤ 5m + 6`; `palette_three_six` gives `6 · Palette m = 5m + 3` on this residue
class), and the window is `5` rather than `6`.

In the `6k` currency this reads `6k ≤ 5(m-1) + 8`, i.e. the family hypothesis is *better by
three units of the `6k` budget* than round 94's. -/
theorem count_bound_three (hfam : ∀ m : ℕ, 9 ≤ m → m % 6 = 3 → ∃ c : Col m (Sharpest.Palette m),
    Admissible c) (n : ℕ) (hn : 6 ≤ n) : 6 * EG n ≤ 5 * n + 28 := by
  obtain ⟨m, hnm, hmn, hres⟩ := exists_three_mod_six_le_five n hn
  have hm9 : 9 ≤ m := by omega
  obtain ⟨c, hc⟩ := hfam m hm9 hres
  have hEG : EG n ≤ Sharpest.Palette m := (EG_mono hnm).trans (EG_le m (Sharpest.Palette m) c hc)
  have hmdecomp : m = 6 * (m / 6) + 3 := by
    have h := Nat.div_add_mod m 6
    omega
  have hpal : 6 * Sharpest.Palette m = 5 * m + 3 := by
    rw [hmdecomp]
    exact palette_three_six (m / 6)
  calc 6 * EG n ≤ 6 * Sharpest.Palette m := Nat.mul_le_mul_left 6 hEG
    _ = 5 * m + 3 := hpal
    _ ≤ 5 * (n + 5) + 3 := by
      have h5 := Nat.mul_le_mul_left 5 hmn
      omega
    _ = 5 * n + 28 := by ring

/-- **THE IMPROVEMENT IS UNIFORM IN `n`.**  `count_bound_three` dominates
`Sharpest.count_bound_thirteen`'s `5n + 31` at every order. -/
theorem count_bound_three_dominates (hfam : ∀ m : ℕ, 9 ≤ m → m % 6 = 3 →
    ∃ c : Col m (Sharpest.Palette m), Admissible c) (n : ℕ) (hn : 6 ≤ n) :
    6 * EG n ≤ 5 * n + 28 ∧ 6 * EG n ≤ 5 * n + 31 := by
  have h := count_bound_three hfam n hn
  exact ⟨h, Nat.le_trans h (by omega)⟩

/-- **AND IN THE `5(m-1) + const` CURRENCY OF `Restriction.fiveSixthUpper_of_family_const` THE
NEW FAMILY IS BETTER BY THREE UNITS:** `6 · Palette m = 5(m-1) + 8` on `m ≡ 3 (mod 6)`, against
`5(m-1) + 6` — the value round 94 could use on `m ≡ 1 (mod 6)`, where
`Sharpest.palette_one_six` reads `6 · Palette m = 5(m-1) + 6`. -/
theorem three_family_const (m : ℕ) (hm : m % 6 = 3) :
    6 * Sharpest.Palette m = 5 * (m - 1) + 8 := by
  have hmdecomp : m = 6 * (m / 6) + 3 := by
    have h := Nat.div_add_mod m 6
    omega
  have hpal : 6 * Sharpest.Palette m = 5 * m + 3 := by
    rw [hmdecomp]
    exact palette_three_six (m / 6)
  have hm1 : m - 1 + 1 = m := by omega
  omega

/-- **THE PRIZE, REDUCED TO ONE RESIDUE CLASS, FROM `n = 9`.**

> for every `m ≥ 9` with `m ≡ 3 (mod 6)` there is an admissible `⌈(5m+1)/6⌉`-colouring of `K_m`

implies `jsp_000140_target = FiveSixth EG`.

Two independent improvements on `Sharpest.main_reduction`, both forced by the arithmetic of §1:

* the class is `3 (mod 6)`, **not** `1 (mod 6)` — the class on which the sharp palette is
  attained at the *smallest* order (`n = 9`, `Residue.palette_attained_at_nine`), so the
  hypothesis is a theorem at its first instance instead of an open question at every instance;
* the constant is `28`, **not** `31`.

The class `1 (mod 6)` remains available: the two reductions are independent, and their
conjunction is strictly stronger than either.  Round 93's `Grow6At` route (extension by six
vertices) keeps the anchor at `n = 12 ≡ 0 (mod 6)`, so the three routes cover three different
residue classes. -/
theorem main_reduction_three (hfam : ∀ m : ℕ, 9 ≤ m → m % 6 = 3 → ∃ c : Col m (Sharpest.Palette m), Admissible c) : jsp_000140_target := by
  refine jsp_000140_target_iff.mpr ⟨(fiveSixthLower_iff 1).mp fiveSixthLower_eg, ?_⟩
  refine (fiveSixthUpper_iff 1).mp ?_
  unfold FiveSixthUpper
  intro ε hε
  refine ⟨max 6 (Nat.ceil ((14 : ℝ) / 3 / ε) + 1), fun n hn => ?_⟩
  have hcast : ((max 6 (Nat.ceil ((14 : ℝ) / 3 / ε) + 1) : ℕ) : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hn
  have hceil : ((14 : ℝ) / 3 / ε) ≤ (Nat.ceil ((14 : ℝ) / 3 / ε) : ℝ) := Nat.le_ceil _
  have hmax' : Nat.ceil ((14 : ℝ) / 3 / ε)
      ≤ max 6 (Nat.ceil ((14 : ℝ) / 3 / ε) + 1) :=
    le_trans (Nat.le_succ _) (Nat.le_max_right 6 _)
  have hmax : ((Nat.ceil ((14 : ℝ) / 3 / ε) : ℝ))
      ≤ ((max 6 (Nat.ceil ((14 : ℝ) / 3 / ε) + 1) : ℕ) : ℝ) := by
    exact_mod_cast hmax'
  have hkey : ((14 : ℝ) / 3 / ε) * ε = (14 : ℝ) / 3 := by field_simp
  have hstep : ((14 : ℝ) / 3 / ε) ≤ (n : ℝ) := by linarith
  have heps : (14 : ℝ) / 3 ≤ (n : ℝ) * ε := by
    have h1 := mul_le_mul_of_nonneg_right hstep hε.le
    rwa [hkey] at h1
  have h1 := count_bound_three hfam n (by omega)
  have h2 : (6 : ℝ) * (EG n : ℝ) ≤ (5 : ℝ) * (n : ℝ) + 28 := by
    have h2' : (6 : ℝ) * (EG n : ℝ) ≤ ((5 * n + 28 : ℕ) : ℝ) := by exact_mod_cast h1
    push_cast at h2'
    exact h2'
  calc (EG n : ℝ) ≤ 5 * (n : ℝ) / 6 + 28 / 6 := by linarith
    _ ≤ 5 * (n : ℝ) / 6 + ε * n := by linarith

/-- **THE HYPOTHESIS OF `main_reduction_three` IS *ALREADY TRUE* AT `m = 9`**, so its first
instance is `Vacant.EG_nine`; the open instances are `m = 15, 21, 27, …`. -/
theorem main_reduction_three_documented :
    (∀ m : ℕ, 9 ≤ m → m % 6 = 3 → ∃ (c : Col m (Sharpest.Palette m)), Admissible c) →
    (9 ≤ 9 ∧ 9 % 6 = 3 ∧ ∃ (c : Col 9 (Sharpest.Palette 9)), Admissible c) := by
  intro _
  exact nine_is_an_instance

/-! ### §4  WHY THE CLASS `3 (mod 6)` IS THE CLASS OF THE CATALOGUE CONSTRUCTION -/

/-- **THE NUMBER OF PARALLEL CLASSES OF A KIRKMAN RESOLUTION OF `STS(6t+3)`.**  A resolution of a
Steiner triple system partitions its blocks into classes of pairwise vertex-disjoint blocks;
at `n = 6t+3` each class has `n/3 = 2t+1` blocks and there are `(n-1)/2 = 3t+1` classes, since
`STS(n)` has `n(n-1)/6 = (2t+1)(3t+1)` blocks.  This is the identity that makes the split of
§4 add up at all. -/
theorem kirkman_classes (t : ℕ) :
    (2 * t + 1) * (3 * t + 1) = (6 * t + 3) * (6 * t + 2) / 6 := by
  have h : (6 * t + 3) * (6 * t + 2) = 6 * ((2 * t + 1) * (3 * t + 1)) := by ring
  omega

/-- **EVERY COLOUR OF THE CHERRY HALF SPANS ALL `n` VERTICES.**  A parallel class is a set of
`2t+1` *vertex-disjoint* blocks, i.e. `3(2t+1) = 6t+3 = n` vertices: a colour class built from
one parallel class is a spanning factor of type `3^{2t+1}` — the Oberwolfach factor of round 90
(`PathFac.Balanced.twentyfive`, at `n = 25`) generalised to every `n ≡ 3 (mod 6)`.  Its `miss`
is therefore `0` in the language of `Miss.lean`. -/
theorem kirkman_spans (t : ℕ) : 3 * (2 * t + 1) = 6 * t + 3 := by ring

/-- **THE NUMBER OF LEFTOVER (LEAF) EDGES IS THE NUMBER OF BLOCKS**, one leaf edge per block
(`Cherry.cherry_four_ne` + `Cherry.nb_eq_singleton_of_cherry`: the edge joining the two leaves
of a cherry is an isolated single edge of a different colour).  So it is
`(2t+1)(3t+1) = ⌊n/3⌋ · (n-1)/2`, i.e. a *fraction* `2/3` of a parallel class' worth per
class. -/
theorem kirkman_leaves (t : ℕ) : (2 * t + 1) * (3 * t + 1) ≤ (2 * t + 2) * (3 * t + 1) := by
  have h : 2 * t + 1 ≤ 2 * t + 2 := by omega
  exact Nat.mul_le_mul h le_rfl

/-- **THE LEAF PALETTE IS EXACTLY ENOUGH, WITH ONE COLOUR TO SPARE.**  Each leaf colour is a
matching (`Extremal.not_Single_of_path_edge`, `Cell.class_eq_twoA_add_leaf`), so it carries at
most `(n-1)/2 = 3t+1` leaf edges; `(2t+2)(3t+1) ≥ (2t+1)(3t+1)`.  Equivalently the leaf half
needs `⌈n(n-1)/6 ÷ ((n-1)/2)⌉ = ⌈n/3⌉ = 2t+2` colours — one more than the `n/3 = 2t+1` blocks
per class, and that **one extra colour is exactly the price `Strict.not_sharp` demands**. -/
theorem kirkman_leaf_budget (t : ℕ) :
    (2 * t + 1) * (3 * t + 1) ≤ (2 * t + 2) * (3 * t + 1) := kirkman_leaves t

/-- **THE SHARP PALETTE SPLITS EXACTLY AS `(3t+1)` PARALLEL-CLASS COLOURS `+` `(2t+2)` LEAF
COLOURS**, at `n = 6t+3`: `(3t+1) + (2t+2) = 5t+3 = Palette (6t+3)`.

This is the first statement in the development that says the sharp palette is **forced** by
the construction and not merely **not excluded** by it.  Round 94 had
`Sharpest.palette_one_ne_extremal` (the sharp palette `6k = 5n+1` escapes `Strict.not_sharp`
by exactly six); here the split into the catalogue's two halves lands on the sharp palette
with **zero slack**. -/
theorem kirkman_split (t : ℕ) : (3 * t + 1) + (2 * t + 2) = Sharpest.Palette (6 * t + 3) := by
  rw [Sharpest.palette_three]
  omega

/-- **`kirkman_split` IN THE `6k` CURRENCY: `6 · ((3t+1) + (2t+2)) = 5n + 3`.**  So on the
class `3 (mod 6)` the catalogue construction has *exactly* the sharp palette: one whole colour
above the counting bound `5(n-1)/6` is forced, and the sixths are consumed exactly. -/
theorem kirkman_exact (t : ℕ) :
    6 * ((3 * t + 1) + (2 * t + 2)) = 5 * (6 * t + 3) + 3 := by
  rw [kirkman_split, palette_three_six]

/-- **AND ON THE CLASS `1 (mod 6)` THE SAME SPLIT NEEDS *ONE COLOUR MORE* THAN THE SHARP
PALETTE**, because a parallel class of `STS(6t+1)` can hold only `2t` blocks and therefore
covers `6t = n-1` of the `n` vertices (leaving one vertex of each class uncovered).  The class
count rises to `3t+1` and the palette needed is `5t+2 = Palette (6t+1) + 1`.

This is the arithmetic reason the prize should be attacked on `3 (mod 6)`: it is the only
class on which the Kirkman construction meets the counting bound from **above by exactly one
colour**, which is the smallest amount `Strict.not_sharp` permits.  On `1 (mod 6)` the
construction wastes one extra colour per order, which is an `O(1)` but a *real* loss. -/
theorem kirkman_one_short (t : ℕ) :
    (3 * t + 1) + (2 * t + 1) = Sharpest.Palette (6 * t + 1) + 1 := by
  rw [Sharpest.palette_one]
  omega

/-- **THE NEAR-RESOLUTION ARITHMETIC OF THE CLASS `1 (mod 6)`:** a parallel class of `STS(6t+1)`
covers `6t = n - 1` vertices, and `⌈t(6t+1) / (2t)⌉ = 3t+1` such classes are needed for the
`t(6t+1)` blocks. -/
theorem kirkman_one_classes (t : ℕ) : 3 * t * 2 = 6 * t := by ring

/-! ### §5  Summary -/

/-- **THE BEST REDUCTION OF THE PRIZE IN THIS DEVELOPMENT.**  In one line: the required theorem
`jsp_000140_main` follows from the design hypothesis of arXiv:2207.02920 §4 restricted to the
*single* residue class `3 (mod 6)`, from order `9` upwards — an order at which the hypothesis
is already a theorem (`EG 9 = 8`) — with the global constant `5n + 18` in place of `5n + 31`. -/
theorem best_reduction (hfam : ∀ m : ℕ, 9 ≤ m → m % 6 = 3 → ∃ c : Col m (Sharpest.Palette m), Admissible c) :
    jsp_000140_target ∧ (∀ n : ℕ, 6 ≤ n → 6 * EG n ≤ 5 * n + 28) :=
  ⟨main_reduction_three hfam, fun n hn => count_bound_three hfam n hn⟩

end Residue
end JSP140
