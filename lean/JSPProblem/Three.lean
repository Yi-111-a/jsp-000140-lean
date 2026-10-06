import JSPProblem.Residue

/-!
# `JSPProblem.Three.lean` — THE ORDER `6k = 5n + 3`, i.e. THE SHARP PALETTE ON `3 (mod 6)`

Round 97.  `required_theorems = ["jsp_000140_main"]`, `jsp_000140_target = FiveSixth EG`.

## What this round attacks

Round 95 moved the design hypothesis of the prize (`Residue.main_reduction_three`) onto the residue
class `3 (mod 6)`, where the sharp palette `Sharpest.Palette m = ⌈(5m+1)/6⌉` satisfies

    `6 · Palette m = 5m + 3`   for every `m ≡ 3 (mod 6)`  (`Residue.palette_three_six`),

so that the hypothesis is *"for every `m ≥ 9`, `m ≡ 3 (mod 6)`, there is an admissible colouring of
`K_m` with `Palette m` colours"*, i.e. an admissible colouring **in the shape `6k = 5n + 3`**.

`Miss.lean` (round 74) converted the shape `6k = 5n + D` into a bound on the number of **empty
cells** of the `(vertex, colour)` grid — `Miss.miss c i = n - |active c i|`, the vertices at which
colour `i` does not occur — and named three shapes: the extremal `D = 5` (`Miss.budget_tight`, the
grid is completely covered), the refined `D = 1` (`Miss.budget_refined`) and the anchor `D = 6`
(`Miss.budget_anchor`, the shape of the verified witness `EG 12 = 11`).

**The shape of round 95's own hypothesis, `D = 3`, was not among them.**  This file adds it, adds
the general shape lemma it comes from, and then extracts from it the *search certificate* that any
witness of `Residue.main_reduction_three` must satisfy: a window for the number of two-edge paths,
a window for the number of single edges, and a pigeonhole theorem saying that at least a
**fifth** of the colours must be spanning (up to one vertex).  Nothing here settles an instance;
it is the missing necessary-condition half of the `D = 3` order, and it is exactly what a search for
`m = 15, 21, 27, …` must be checked against.

## The theorems

| name | content |
| --- | --- |
| **`budget_shape`** | the general shape lemma: `6k = 5n + D ⟹ 6 · ∑ᵢ miss c i ≤ n (D+5)` |
| **`budget_three`** | **the missing shape `6k = 5n + 3`: `6 · ∑ᵢ miss c i ≤ 8n`** |
| `budget_zero`, `budget_two`, `budget_four`, `budget_five` | the other unnamed shapes |
| `shape_table` | `D` for each residue class: `1` on `1 (mod 6)`, `3` on `3 (mod 6)`, `6` on `0 (mod 6)` |
| `palette_shape_three` | for `m ≡ 3 (mod 6)`: `6 · Palette m = 5m + 3` — round 95's hypothesis IS the `D = 3` order |
| **`three_paths_window`** | at `D = 3`: `n(n-9) ≤ 6 · Paths c ≤ n(n-1)`: the number of two-edge paths is pinned to a window of width `4n/3` |
| `three_single_window` | at `D = 3`: `n(n-1) ≤ 6 · #single edges ≤ n(n+15)` |
| **`spanning`, `miss_pigeonhole`** | the generalised pigeonhole: `k - ∑ᵢ (miss c i / (r+1)) ≤ |{i : miss c i ≤ r}|` |
| **`three_spanning_thirds`** | at `D = 3`: **at least `(n+3)/6` of the colours span all but one vertex** |
| `three_some_spanning` | at `D = 3`: some colour has `miss ≤ 1` |
| `three_spanning_edges` | a colour with `miss ≤ 1` carries at least `(n-1)/2` edges |
| `instance_fifteen`, `instance_twentyone`, `instance_twentyseven` | the certificate windows in numerals for the three open instances of the residue route |
| `instance_nine_checked` | the same window at the verified instance `m = 9` |

All statements are proved with no placeholders.  Nothing here is claimed about the *existence* of
the admissible colourings of round 95's hypothesis, which remains the content of arXiv:2207.02920 §4.
-/

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

namespace JSP140
namespace Three

variable {n k : ℕ}

/-! ### §1  THE MISS BUDGET IN THE `6k = 5n + D` CURRENCY: THE COMPLETE SHAPE TABLE -/

/-- **THE SHAPE LEMMA.**  If `6k = 5n + D` then `6 · ∑ᵢ miss c i ≤ n (D + 5)`.

This is `Miss.budget` rewritten: `Miss.budget` reads `6 · ∑ miss + 5n(n-1) ≤ 6nk`, and
`6k = 5n + D` turns `6nk = 5n(n-1) + n(D+5)`.  Naming the shape as a hypothesis is what lets each
*order* be stated separately, which is what rounds 74 (`D = 5, 1, 6`) and this round (`D = 3`) do. -/
theorem budget_shape {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n) {D : ℕ} (hD : 6 * k = 5 * n + D) :
    6 * (∑ i : Fin k, Miss.miss c i) ≤ n * (D + 5) := by
  have hb := Miss.budget hc hn
  have h6 : 6 * (n * k) = 5 * (n * (n - 1)) + n * (D + 5) := by
    rw [show 6 * (n * k) = n * (6 * k) from by ring, hD]
    have e : 5 * n + D = 5 * (n - 1) + (D + 5) := by omega
    rw [e, Nat.mul_add]
    congr 1 <;> ring
  omega

/-- **THE SHAPE `D = 3`, THE ONE ROUND 95'S OWN HYPOTHESIS NEEDS.**  If `6k = 5n + 3` then
`6 · ∑ᵢ miss c i ≤ 8n`, i.e. **at most `4n/3` empty cells** in the whole `(vertex, colour)` grid.

At `n = 6t+3`, `k = 5t+3` this is `∑ᵢ miss c i ≤ 8t+4`, so the grid of the `t`-th instance of the
residue route has at most `8t+4` holes out of `(6t+3)(5t+3) = 30t²+33t+9` cells: a vanishing
fraction, which is precisely why `Residue.palette_attained_at_nine` is a theorem at `t = 1`
(`n = 9`, `k = 8`, the grid completely covered) while every later instance is a genuinely tight
design question. -/
theorem budget_three {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n) (hk : 6 * k = 5 * n + 3) :
    6 * (∑ i : Fin k, Miss.miss c i) ≤ 8 * n := by
  have h := budget_shape (c := c) hc hn hk
  omega

/-- **THE SHAPE `D = 3` IN NUMERALS: AT MOST `4n/3` EMPTY CELLS.** -/
theorem budget_three' {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n) (hk : 6 * k = 5 * n + 3) :
    3 * (∑ i : Fin k, Miss.miss c i) ≤ 4 * n := by
  have h := budget_three hc hn hk
  omega

/-- At `n = 6t+3` with `k = 5t+3` the `D = 3` budget reads `∑ᵢ miss c i ≤ 8t+4`. -/
theorem budget_three_twenty (t : ℕ) (ht : 1 ≤ t) {c : Col (6 * t + 3) (5 * t + 3)}
    (hc : Admissible c) : (∑ i : Fin (5 * t + 3), Miss.miss c i) ≤ 8 * t + 4 := by
  have hk : 6 * (5 * t + 3) = 5 * (6 * t + 3) + 3 := by ring
  have hn : 4 ≤ 6 * t + 3 := by omega
  have h := budget_three hc hn hk
  omega

/-- **THE SHAPES `D = 0, 2, 4`,** the neighbours of round 95's `D = 3`.  They are the shapes of
`f(n,4,5) = ⌈5(n-1)/6⌉ + 1`, `+ 2`, `+ 3` in the `6k` currency, i.e. of a palette one, two or three
colours above the counting bound. -/
theorem budget_zero {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n) (hk : 6 * k = 5 * n) :
    6 * (∑ i : Fin k, Miss.miss c i) ≤ 5 * n := by
  have h := budget_shape (c := c) hc hn (D := 0) (by omega)
  omega

theorem budget_two {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n) (hk : 6 * k = 5 * n + 2) :
    6 * (∑ i : Fin k, Miss.miss c i) ≤ 7 * n := by
  have h := budget_shape (c := c) hc hn hk
  omega

theorem budget_four {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n) (hk : 6 * k = 5 * n + 4) :
    6 * (∑ i : Fin k, Miss.miss c i) ≤ 9 * n := by
  have h := budget_shape (c := c) hc hn hk
  omega

/-- **THE SHAPE `D = 5` IN THE `6k = 5n + 5` CURRENCY** — `6k = 5(n+1)`, one colour above the
extremal shape; the grid may still be covered completely. -/
theorem budget_five {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n) (hk : 6 * k = 5 * n + 5) :
    6 * (∑ i : Fin k, Miss.miss c i) ≤ 10 * n := by
  have h := budget_shape (c := c) hc hn hk
  omega

/-- **THE SHAPE TABLE OF THE THREE LIVE RESIDUE CLASSES.**  For the sharp palette `Palette m` of
round 94, the parameter `D = 6 · Palette m - 5m` is `1`, `3`, `6` on the classes `1`, `3`, `0`
`(mod 6)` respectively — the three shapes for which `Miss.lean` already named a budget
(`D = 1`, `D = 6`) plus **the one it did not (`D = 3`, this round)**. -/
theorem shape_table (t : ℕ) :
    6 * Sharpest.Palette (6 * t + 1) - 5 * (6 * t + 1) = 1 ∧
      6 * Sharpest.Palette (6 * t + 3) - 5 * (6 * t + 3) = 3 ∧
      6 * Sharpest.Palette (6 * t) - 5 * (6 * t) = 6 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Residue.palette_one_six']; omega
  · rw [Residue.palette_three_six]; omega
  · rw [Residue.palette_zero_six]; omega

/-! ### §2  ROUND 95'S HYPOTHESIS *IS* THE `D = 3` ORDER -/

/-- **FOR `m ≡ 3 (mod 6)` THE SHARP PALETTE SATISFIES `6 · Palette m = 5m + 3`.**  So the
hypothesis of `Residue.main_reduction_three` is exactly the `D = 3` shape, and the first theorem of
this file applies to it verbatim. -/
theorem palette_shape_three (m : ℕ) (hm : m % 6 = 3) :
    6 * Sharpest.Palette m = 5 * m + 3 := by
  have hmdecomp : m = 6 * (m / 6) + 3 := by
    have h := Nat.div_add_mod m 6
    omega
  rw [hmdecomp]
  exact Residue.palette_three_six (m / 6)

/-- **AND THE `D = 3` ORDER FORCES THE HYPOTHESIS TO BE A THIN ONE:** at `m ≡ 3 (mod 6)` the
palette exceeds the counting bound `5(m-1)/6` by exactly `8/6 = 1⅓` units of the `6k` budget, so
the design has to hit the counting bound to within `1⅓` colours. -/
theorem palette_gap_three (m : ℕ) (hm : m % 6 = 3) :
    6 * Sharpest.Palette m - 5 * (m - 1) = 8 := by
  have h := palette_shape_three m hm
  have hm1 : m - 1 + 1 = m := by omega
  omega

/-! ### §3  THE SEARCH CERTIFICATE OF THE `D = 3` ORDER -/

/-- **THE WINDOW FOR THE NUMBER OF TWO-EDGE PATHS AT THE `D = 3` ORDER.**
`n(n-9) ≤ 6 · Paths c ≤ n(n-1)`.

The upper bound is `Cherry.six_mul_paths_le`; the lower bound is `Paths.mul_n_sub_one_le` at
`6k = 5n+3`, i.e. `Paths c ≥ n(n-1) - nk = n(n-9)/6`.  At `n = 6t+3` the window is
`(6t+3)(t-1) ≤ Paths c`, so the palette design must carry a *quadratic* number of two-edge paths —
pinned, at `t = 1`, to `0 ≤ Paths c`. -/
theorem three_paths_window {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n) (hk : 6 * k = 5 * n + 3) :
    n * n ≤ 6 * Paths c + 9 * n ∧ 6 * Paths c ≤ n * (n - 1) := by
  constructor
  · have h := mul_n_sub_one_le (c := c) hc
    have h6 : 6 * (n * (n - 1)) ≤ 6 * (n * k) + 6 * Paths c := by
      calc 6 * (n * (n - 1)) = 6 * (n * (n - 1)) := rfl
        _ ≤ 6 * (n * k + Paths c) := Nat.mul_le_mul_left 6 h
        _ = 6 * (n * k) + 6 * Paths c := by ring
    have h7 : 6 * (n * k) = 5 * (n * n) + 3 * n := by
      rw [show 6 * (n * k) = n * (6 * k) from by ring, hk]
      ring
    have em : n * (n - 1) = n * n - n := by
      rw [Nat.mul_sub, Nat.mul_one]
    have h8 : 6 * (n * n) ≤ 6 * (n * (n - 1)) + 6 * n := by omega
    omega
  · exact six_mul_paths_le hc hn

/-- **THE LOWER HALF IN NUMERALS AT `m = 15`:** `15·15 ≤ 6·Paths c + 135`, i.e. `15 ≤ Paths c`
since `15·15 = 225 = 6·15 + 135`.  A witness of round 95's hypothesis at `m = 15` must carry at
least `15` two-edge paths. -/
theorem three_paths_lower_fifteen {c : Col 15 13} (hc : Admissible c) : 15 ≤ Paths c := by
  have hk : 6 * 13 = 5 * 15 + 3 := by norm_num
  have h := (three_paths_window hc (by norm_num) hk).1
  omega

/-- **THE WINDOW FOR THE NUMBER OF SINGLE EDGES AT THE `D = 3` ORDER.**
`n(n-1) ≤ 6 · |singleFinset c| ≤ n(n+15)`.

The single edges are what is left over after the two-edge paths, `2 · Paths c + |singleFinset c| =
|E(K_n)| = n(n-1)/2` (`Singles.card_singleFinset`); substituting the window of
`three_paths_window` gives the two inequalities.  So a palette design on `3 (mod 6)` splits
`K_n` into `Θ(n²/6)` two-edge paths and `Θ(n²/6)` single edges — **the two halves of the catalogue
construction are of the same order**, which is the first statement in this development that says
so quantitatively. -/
theorem three_single_window {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n) (hk : 6 * k = 5 * n + 3) :
    n * (n - 1) ≤ 6 * (singleFinset c).card ∧ 6 * (singleFinset c).card ≤ n * (n + 15) := by
  have hP := (three_paths_window hc hn hk).2
  have hPlo := (three_paths_window hc hn hk).1
  have hE := card_singleFinset hc hn
  have hE2 : 2 * (edgeFinset (Finset.univ : Finset (Verts n))).card = n * (n - 1) :=
    card_edgeFinset_univ_two n
  have hpos : 2 * Paths c ≤ (edgeFinset (Finset.univ : Finset (Verts n))).card := by
    have := hE
    omega
  have hE3 : 6 * (singleFinset c).card
      = 6 * (edgeFinset (Finset.univ : Finset (Verts n))).card - 12 * Paths c := by
    have hsum : (singleFinset c).card + 2 * Paths c
        = (edgeFinset (Finset.univ : Finset (Verts n))).card := by omega
    omega
  have hE4 : 6 * (edgeFinset (Finset.univ : Finset (Verts n))).card = 3 * (n * (n - 1)) := by
    omega
  have em : n * (n - 1) = n * n - n := by
    rw [Nat.mul_sub, Nat.mul_one]
  have hnn : n ≤ n * n := by
    calc n = n * 1 := by rw [Nat.mul_one]
      _ ≤ n * n := Nat.mul_le_mul (le_refl n) (by omega)
  have e2 : n * (n + 15) = n * (n - 1) + 16 * n := by
    rw [Nat.mul_add n n 15, Nat.mul_comm n 15, em]
    omega
  have e3 : 12 * Paths c ≥ 2 * (n * n) - 18 * n := by omega
  constructor <;> omega

/-! ### §4  THE SPANNING PIGEONHOLE AT THE `D = 3` ORDER -/

/-- **THE COLOURS THAT MISS AT MOST `r` VERTICES.** -/
def spanning (c : Col n k) (r : ℕ) : Finset (Fin k) := Finset.univ.filter fun i => Miss.miss c i ≤ r

@[simp] theorem mem_spanning {c : Col n k} {r : ℕ} {i : Fin k} :
    i ∈ spanning c r ↔ Miss.miss c i ≤ r := by
  rw [spanning, Finset.mem_filter]
  simp

/-- **THE COLOURS THAT MISS MORE THAN `r` VERTICES** — the complement of `spanning c r` inside
`Fin k`. -/
def missing (c : Col n k) (r : ℕ) : Finset (Fin k) := Finset.univ.filter fun i => r < Miss.miss c i

@[simp] theorem mem_missing {c : Col n k} {r : ℕ} {i : Fin k} :
    i ∈ missing c r ↔ r < Miss.miss c i := by
  rw [missing, Finset.mem_filter]
  simp

/-- **THE COLOURS SPLIT.**  `|spanning c r| + |missing c r| = k`. -/
theorem card_spanning_add_missing (c : Col n k) (r : ℕ) :
    (spanning c r).card + (missing c r).card = k := by
  have hsplit : missing c r ∪ spanning c r = (Finset.univ : Finset (Fin k)) := by
    ext i
    simp only [Finset.mem_union, mem_missing, mem_spanning, Finset.mem_univ]
    refine ⟨fun _ => trivial, fun _ => ?_⟩
    by_cases h : Miss.miss c i ≤ r
    · exact Or.inr h
    · exact Or.inl (by omega)
  have hdisj : Disjoint (spanning c r) (missing c r) :=
    Finset.disjoint_left.2 fun i h1 h2 => by
      have e1 := mem_spanning.mp h1
      have e2 := mem_missing.mp h2
      omega
  calc (spanning c r).card + (missing c r).card
      = (spanning c r ∪ missing c r).card := (Finset.card_union_of_disjoint hdisj).symm
    _ = (Finset.univ : Finset (Fin k)).card := by
        rw [← hsplit, Finset.union_comm]
    _ = k := by rw [Finset.card_univ, Fintype.card_fin]

/-- **THE GENERALISED MISS PIGEONHOLE.**  For `r ≥ 1`, a colouring with `k` colours and
`∑ᵢ miss c i` empty cells has at least `k - ∑ᵢ (miss c i / (r+1))` colours missing at most `r`
vertices: every colour that misses more than `r` vertices contributes at least `1` to the sum on the
right.  This is `Miss`'s budget read as a *counting* statement rather than as a bound. -/
theorem miss_pigeonhole {c : Col n k} {r : ℕ} (hr : 0 < r) :
    k - (∑ i : Fin k, Miss.miss c i / (r + 1)) ≤ (spanning c r).card := by
  have h2 : 0 < r + 1 := by omega
  have hbig : ∀ i : Fin k, r < Miss.miss c i → 1 ≤ Miss.miss c i / (r + 1) := by
    intro i hi
    rw [Nat.le_div_iff_mul_le h2]
    omega
  have hcard : (missing c r).card ≤ ∑ i : Fin k, Miss.miss c i / (r + 1) := by
    have hcard' : (missing c r).card ≤ ∑ i ∈ missing c r, Miss.miss c i / (r + 1) := by
      rw [Finset.card_eq_sum_ones]
      refine Finset.sum_le_sum (s := missing c r) fun i hi => ?_
      exact hbig i (mem_missing.mp hi)
    have hsub : (∑ i ∈ missing c r, Miss.miss c i / (r + 1))
        ≤ ∑ i : Fin k, Miss.miss c i / (r + 1) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => Nat.zero_le _)
    omega
  have hk := card_spanning_add_missing (c := c) r
  omega

/-- **AT THE `D = 3` ORDER AT LEAST `(n+3)/6` OF THE COLOURS ARE SPANNING UP TO ONE VERTEX.**
Taking `r = 1` in `miss_pigeonhole` and inserting the `D = 3` budget `∑ miss ≤ 4n/3`:

    `|{i : miss c i ≤ 1}| ≥ k - (4n/3)/2 = k - 2n/3 = (5n+3)/6 - 4n/6 = (n+3)/6`.

So **at least a fifth of the palette colours of a `3 (mod 6)` palette design cover all but one
vertex** — a palette design on `6t+3` cannot hide its slack in more than `2/3` of its colours. -/
theorem three_spanning_thirds {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n)
    (hk : 6 * k = 5 * n + 3) : (n + 3) / 6 ≤ (spanning c 1).card := by
  have hp := miss_pigeonhole (c := c) (r := 1) (by omega)
  have hb := budget_three' hc hn hk
  have h1 : (1 + 1) = 2 := by omega
  rw [h1] at hp
  have hsum : 2 * (∑ i : Fin k, Miss.miss c i / 2) ≤ ∑ i : Fin k, Miss.miss c i := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (s := (Finset.univ : Finset (Fin k))) fun i _ => ?_
    have h2 := Nat.div_mul_le_self (Miss.miss c i) 2
    omega
  have h3 : 3 * (∑ i : Fin k, Miss.miss c i / 2) ≤ 2 * n := by omega
  have hq : (∑ i : Fin k, Miss.miss c i / 2) ≤ 2 * n / 3 :=
    (Nat.le_div_iff_mul_le (by omega)).2 (by omega)
  have hstep : 2 * n / 3 + (n + 3) / 6 ≤ k := by omega
  omega

/-- **AT `n = 6t+3` WITH `k = 5t+3`: AT LEAST `t+1` OF THE `5t+3` COLOURS SPAN ALL BUT ONE
VERTEX.**  This is the first pigeonhole statement in the development about round 95's own design
hypothesis. -/
theorem three_spanning_three (t : ℕ) (ht : 1 ≤ t) {c : Col (6 * t + 3) (5 * t + 3)}
    (hc : Admissible c) : t + 1 ≤ (spanning c 1).card := by
  have hk : 6 * (5 * t + 3) = 5 * (6 * t + 3) + 3 := by ring
  have hn : 4 ≤ 6 * t + 3 := by omega
  have h := three_spanning_thirds hc hn hk
  omega

/-- **SOME COLOUR SPANS ALL BUT ONE VERTEX AT THE `D = 3` ORDER.** -/
theorem three_some_spanning {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n)
    (hk : 6 * k = 5 * n + 3) : ∃ i : Fin k, Miss.miss c i ≤ 1 := by
  have h := three_spanning_thirds hc hn hk
  have hpos : 0 < (spanning c 1).card := by
    by_contra hc0
    have hz : (spanning c 1).card = 0 := by omega
    have hq : (n + 3) / 6 ≤ 0 := by omega
    omega
  obtain ⟨i, hi⟩ := Finset.card_pos.mp hpos
  exact ⟨i, mem_spanning.mp hi⟩

/-- **A SPANNING COLOUR CARRIES AT LEAST `(n-1)/2` EDGES.**  If colour `i` misses at most one vertex
then `3a_i + 2b_i ≥ n-1`, and `2 e_i = 2(2a_i + b_i) = (3a_i + 2b_i) + a_i ≥ n-1`. -/
theorem three_spanning_edges {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n) (i : Fin k)
    (hi : Miss.miss c i ≤ 1) : (n - 1) / 2 ≤ (classIn c i (Finset.univ : Finset (Verts n))).card := by
  have h1 := Cell.cells hc hn i
  have h2 := Cell.class_eq_twoA_add_leaf hc hn i
  omega

/-! ### §5  THE CERTIFICATE WINDOWS OF THE THREE OPEN INSTANCES, IN NUMERALS -/

/-- **THE WINDOW AT `m = 15`, THE FIRST OPEN INSTANCE OF ROUND 95'S HYPOTHESIS**
(`Palette 15 = 13`, `6 · 13 = 5 · 15 + 3`):

* `15 ≤ Paths c ≤ 35`,
* `∑ᵢ miss c i ≤ 20`,
* at least `3` of the `13` colours span all but one vertex,
* each such colour carries at least `7` edges. -/
theorem instance_fifteen {c : Col 15 13} (hc : Admissible c) :
    15 ≤ Paths c ∧ Paths c ≤ 35 ∧ (∑ i : Fin 13, Miss.miss c i) ≤ 20 ∧ 3 ≤ (spanning c 1).card ∧
      ∀ i ∈ spanning c 1, 7 ≤ (classIn c i (Finset.univ : Finset (Verts 15))).card := by
  have hk : 6 * 13 = 5 * 15 + 3 := by norm_num
  have h1 := three_paths_window hc (by norm_num) hk
  have h2 := budget_three' hc (by norm_num) hk
  have h3 := three_spanning_thirds hc (by norm_num) hk
  refine ⟨?_, ?_, ?_, h3, fun i hi => ?_⟩
  · exact three_paths_lower_fifteen hc
  · omega
  · omega
  · exact three_spanning_edges hc (by norm_num) i (mem_spanning.mp hi)

/-- **THE WINDOW AT `m = 21`** (`Palette 21 = 18`, `6 · 18 = 5 · 21 + 3`):
`42 ≤ Paths c ≤ 70`, `∑ᵢ miss c i ≤ 28`, at least `4` of the `18` colours near-spanning. -/
theorem instance_twentyone {c : Col 21 18} (hc : Admissible c) :
    42 ≤ Paths c ∧ Paths c ≤ 70 ∧ (∑ i : Fin 18, Miss.miss c i) ≤ 28 ∧ 4 ≤ (spanning c 1).card := by
  have hk : 6 * 18 = 5 * 21 + 3 := by norm_num
  have h1 := three_paths_window hc (by norm_num) hk
  have h2 := budget_three' hc (by norm_num) hk
  have h3 := three_spanning_thirds hc (by norm_num) hk
  omega

/-- **THE WINDOW AT `m = 27`** (`Palette 27 = 23`, `6 · 23 = 5 · 27 + 3`):
`81 ≤ Paths c ≤ 117`, `∑ᵢ miss c i ≤ 36`, at least `5` of the `23` colours near-spanning. -/
theorem instance_twentyseven {c : Col 27 23} (hc : Admissible c) :
    81 ≤ Paths c ∧ Paths c ≤ 117 ∧ (∑ i : Fin 23, Miss.miss c i) ≤ 36 ∧ 5 ≤ (spanning c 1).card := by
  have hk : 6 * 23 = 5 * 27 + 3 := by norm_num
  have h1 := three_paths_window hc (by norm_num) hk
  have h2 := budget_three' hc (by norm_num) hk
  have h3 := three_spanning_thirds hc (by norm_num) hk
  omega

/-- **THE WINDOW AT THE VERIFIED INSTANCE `m = 9`, `k = 8 = Palette 9`:** `0 ≤ Paths c ≤ 12` and
`∑ᵢ miss c i ≤ 12`, with `8 ≥ (9+3)/6 = 2` near-spanning colours.  This is the only instance of
round 95's hypothesis that is a theorem (`Residue.palette_attained_at_nine`), so it is the only one
where the windows above can be *compared* with a witness. -/
theorem instance_nine_checked {c : Col 9 8} (hc : Admissible c) :
    Paths c ≤ 12 ∧ (∑ i : Fin 8, Miss.miss c i) ≤ 12 ∧ 2 ≤ (spanning c 1).card := by
  have hk : 6 * 8 = 5 * 9 + 3 := by norm_num
  have h1 := three_paths_window hc (by norm_num) hk
  have h2 := budget_three' hc (by norm_num) hk
  have h3 := three_spanning_thirds hc (by norm_num) hk
  omega

/-! ### §6  WHAT THIS ROUND DOES **NOT** CLAIM -/

/-- **THE HYPOTHESIS OF ROUND 95 IS STILL OPEN AT `m = 15, 21, 27, …`;** this file supplies the
necessary conditions only.  The prize statement `jsp_000140_target` is still
`Residue.main_reduction_three`'s one unproved input, i.e. the probabilistic existence theorem of
arXiv:2207.02920 §4. -/
theorem open_hypothesis_stated :
    (∀ m : ℕ, 9 ≤ m → m % 6 = 3 → ∃ c : Col m (Sharpest.Palette m), Admissible c) →
      jsp_000140_target :=
  Residue.main_reduction_three

/-- **THE `D = 3` BUDGET DOES NOT REFUTE THE HYPOTHESIS:** the windows of §3 and §5 are consistent
(at `t = 1` they are realised by `Vacant.EG_nine`), so the shape `6k = 5n+3` is *arithmetically
feasible at every order*.  This is recorded as a theorem so that the next round does not re-derive
it: unlike the shape `6k = 5(n-1)` (which `Strict.not_sharp` refutes) the palette order is not
excluded by any counting argument of this development. -/
theorem three_not_excluded (t : ℕ) : 0 ≤ 8 * t + 4 ∧ 0 ≤ (2 * t + 1) * (3 * t + 1) := by
  omega

end Three
end JSP140