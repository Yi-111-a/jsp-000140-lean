import JSPProblem.Vacant
import JSPProblem.Surplus
import JSPProblem.Rigidity
import JSPProblem.Ghost

/-!
# JSP-000140 — ROUND 66: the window closes at `n = 12`: `f(12,4,5) = 11`, and the structure at
# `k = n-2` and `k = n-1`

## What round 65 left, and what was wrong with it

Round 65 (`Vacant.lean`) proved the **per-vertex** instrument

    `6k ≥ 5n + 1`  for every admissible colouring with `4 ≤ n` and `k + 2 ≤ n`,

hence `⌈(5n+1)/6⌉ ≤ f(n,4,5)` for every `n ≥ 7`, and it registered as the cheapest open item of
the whole development:

> `EG 12 = 11` is NOT proved: the lower half (`11 ≤ EG 12`) is now a theorem of counting, but no
> admissible 11-COLOURING of `K_12` is known.  EVERY search of rounds 45-46 / 60 was run at
> `⌈5(n-1)/6⌉` colours, i.e. ONE BELOW the new bound — they must be re-run one colour higher.

**The premise "no admissible 11-colouring of `K_12` is known" is false, and this round closes that
blocker with no search at all.**  `n = 12` is *even* with `3 ∤ (n-1)`, exactly the regime of the
ghost colouring of `Ghost.lean` (a 1-factorisation of `K₁₂` with `11` colours, admissible by
`Ghost.admissible_ghost`), so `EG 12 ≤ 11`, and `Vacant.EG_twelve_ge_eleven` gives the other side:

* **`Window.EG_twelve : EG 12 = 11`** — the **ninth exact value** of `f(n,4,5)` in this
  development, and the first one obtained by *combining* a construction of `Ghost.lean` with a bound
  of `Vacant.lean`: the ghost colouring attains the refined bound;
* the shape of the combination, `Window.window_even` (`⌈(5n+1)/6⌉ ≤ f(n,4,5) ≤ n-1` for even
  `n ≥ 7` with `3 ∤ (n-1)`) and its collapse to a single point, `Window.window_collapse` (the
  window is a singleton exactly at `n = 8` and `n = 12`);
* `Window.window_separated` (from `n = 13` on the two ends are separated by at least one colour,
  so no exact value follows from them), `Window.first_nine_exact` (the first nine exact values in one statement)
  and `Window.next_three_open` (the three smallest open orders with their intervals).

## The structure at `k = n-2` and at `k = n-1` (new)

`Surplus.global_identity` says `n(n-1) + Isolated c = nk + Paths c`, so at a fixed order the two
defects are pinned by `Paths c`.  Combined with the **per-vertex** reading of the same data — at a
vertex `v` the `n-1` incident edges use each colour at most twice (`Counting.nb_card_le_two`), and
use it twice exactly for the colours of the two-edge paths centred at `v` — one gets the exact
count

* **`Window.missing_at`: the colours missing at `v` are `k - (n-1)` plus the number of two-edge
  paths centred at `v`** (`Window.handshake` + `Window.three_way`),

with the two consequences that matter at the orders the constructions of this development reach:

* **`Window.centre_of_paths`: if `k = n-2`, EVERY VERTEX IS THE CENTRE OF A TWO-EDGE PATH** — the
  identity reads `#{i : v ∈ zeroA c i} = #{i : v ∈ twoA c i} - 1 ≥ 0` — hence
  **`Window.paths_ge_n : n ≤ Paths c`**, the pigeonhole of round 65 isolated as a statement about
  the colouring;
* **`Window.isolated_eq_paths`: at `k = n-1` the two defects COINCIDE, `Isolated c = Paths c`**, and
  **`Window.isolated_add_n_eq_paths`: at `k = n-2`, `Isolated c + n = Paths c`**.  So the `K₁₂`
  witness of §1, being a 1-factorisation, has `Paths = Isolated = 0`, and the extremal shape at
  `n = 13` (`Window.thirteen_shape`) has `Paths = 26` exactly.

## Benchmark B5 is a Steiner triple system

`n = 13, k = 11` is the first order at which the refined bound can be *attained*
(`6 · 11 = 5 · 13 + 1`), and `Vacant.extremal_at_thirteen_shape` gives `Isolated c = 13` and
`Defect c = 0`.  With `Isolated c + n = Paths c` this yields `Paths c = 26 = n(n-1)/6`, i.e. the
counting lemma `Cherry.three_mul_paths_le_edges` is an *equality*, hence

* **`Window.extremal_at_thirteen_is_STS`: an admissible 11-colouring of `K₁₃` would have its
  two-edge paths forming a Steiner triple system of order 13** (`Rigidity.IsSTS`).

So the exhaustive searches of rounds 49–56 on benchmark B5
(`discovery/JSP-000140/sts212b.c`: 4 seeds × 2200 s over `(2,1)`-block assignments on the cyclic
`STS(13)`) were — as this theorem now says — searching exactly the right space; their negative
outcome says B5 is very likely unattainable, but no bound above `11` is proved here.

The prize hypothesis `Main.AdmissibleUpper ε` is untouched: it is still the probabilistic existence
theorem of arXiv:2207.02920 §4.  This file is counting plus one verified construction.
-/

namespace JSP140

variable {n k : ℕ} {c : Col n k}

/-! ### §0  Two counting tools: indicator sums are cardinalities -/

private theorem ite_sum_card {p : Fin k → Prop} [DecidablePred p] :
    (∑ i : Fin k, if p i then (1 : ℕ) else 0) = ((Finset.univ : Finset (Fin k)).filter p).card := by
  rw [(Finset.sum_filter p (fun _ => (1 : ℕ))).symm, Finset.card_eq_sum_ones]

private theorem ite_sum_two {p : Fin k → Prop} [DecidablePred p] :
    (∑ i : Fin k, if p i then (2 : ℕ) else 0) = 2 * (∑ i : Fin k, if p i then 1 else 0) := by
  rw [(Finset.sum_filter p (fun _ => (2 : ℕ))).symm, Finset.sum_const_nat (fun _ _ => rfl),
    ite_sum_card, Nat.mul_comm]

private theorem card_twoA_sum (c : Col n k) (i : Fin k) :
    (twoA c i).card = ∑ v : Verts n, if v ∈ twoA c i then (1 : ℕ) else 0 := by
  have hfilter : (Finset.univ : Finset (Verts n)).filter (fun v => v ∈ twoA c i) = twoA c i := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [(Finset.sum_filter (fun v => v ∈ twoA c i) (fun _ => (1 : ℕ))).symm, hfilter,
    Finset.card_eq_sum_ones]

/-- **THE TRICHOTOMY AT ONE VERTEX.**  Exactly one of `zeroA`, `oneB`, `twoA` holds of `(v, i)`,
because the colour-`i` neighbourhood of `v` has size `0`, `1` or `2` (`Counting.nb_card_le_two`
bounds it by `2`). -/
private theorem ite_trichotomy (hc : Admissible c) (i : Fin k) (v : Verts n) :
    (if v ∈ zeroA c i then 1 else 0) + (if v ∈ oneB c i then 1 else 0)
      + (if v ∈ twoA c i then 1 else 0) = 1 := by
  have hle := nb_card_le_two hc i v (Finset.univ : Finset (Verts n))
  have hcases : (nb c i v (Finset.univ : Finset (Verts n))).card = 0 ∨
      (nb c i v (Finset.univ : Finset (Verts n))).card = 1 ∨
      (nb c i v (Finset.univ : Finset (Verts n))).card = 2 := by omega
  rcases hcases with h0 | h1 | h2
  · have hz : v ∈ zeroA c i := (mem_zeroA).2 h0
    have hno : v ∉ oneB c i := fun h => absurd ((mem_oneB).1 h) (by rw [h0]; omega)
    have hnt : v ∉ twoA c i := fun h => absurd ((mem_twoA).1 h) (by rw [h0]; omega)
    rw [if_pos hz, if_neg hno, if_neg hnt]
  · have ho : v ∈ oneB c i := (mem_oneB).2 h1
    have hnz : v ∉ zeroA c i := fun h => absurd ((mem_zeroA).1 h) (by rw [h1]; omega)
    have hnt : v ∉ twoA c i := fun h => absurd ((mem_twoA).1 h) (by rw [h1]; omega)
    rw [if_neg hnz, if_pos ho, if_neg hnt]
  · have ht : v ∈ twoA c i := (mem_twoA).2 h2
    have hnz : v ∉ zeroA c i := fun h => absurd ((mem_zeroA).1 h) (by rw [h2]; omega)
    have hno : v ∉ oneB c i := fun h => absurd ((mem_oneB).1 h) (by rw [h2]; omega)
    rw [if_neg hnz, if_neg hno, if_pos ht]

/-- The colour-`i` neighbourhood of `v` has size `2` on `twoA`, `1` on `oneB` and `0` on `zeroA`. -/
private theorem card_nb_eq_twoA_oneB (hc : Admissible c) (i : Fin k) (v : Verts n) :
    (nb c i v (Finset.univ : Finset (Verts n))).card
      = (if v ∈ twoA c i then (2 : ℕ) else 0) + (if v ∈ oneB c i then 1 else 0) := by
  have hle := nb_card_le_two hc i v (Finset.univ : Finset (Verts n))
  have hcases : (nb c i v (Finset.univ : Finset (Verts n))).card = 0 ∨
      (nb c i v (Finset.univ : Finset (Verts n))).card = 1 ∨
      (nb c i v (Finset.univ : Finset (Verts n))).card = 2 := by omega
  rcases hcases with h0 | h1 | h2
  · have hnz : v ∉ twoA c i := fun h => absurd ((mem_twoA).1 h) (by rw [h0]; omega)
    have hno : v ∉ oneB c i := fun h => absurd ((mem_oneB).1 h) (by rw [h0]; omega)
    rw [h0, if_neg hnz, if_neg hno]
  · have hnz : v ∉ twoA c i := fun h => absurd ((mem_twoA).1 h) (by rw [h1]; omega)
    have ho : v ∈ oneB c i := (mem_oneB).2 h1
    rw [h1, if_neg hnz, if_pos ho]
  · have ht : v ∈ twoA c i := (mem_twoA).2 h2
    have hno : v ∉ oneB c i := fun h => absurd ((mem_oneB).1 h) (by rw [h2]; omega)
    rw [h2, if_pos ht, if_neg hno]

/-- **EVERY COLOUR IS MISSED, USED ONCE OR USED TWICE** at a given vertex: `zeroA`, `oneB`,
`twoA` partition the palette as seen from `v`. -/
private theorem three_way (hc : Admissible c) (v : Verts n) :
    (∑ i : Fin k, if v ∈ zeroA c i then 1 else 0) + (∑ i : Fin k, if v ∈ oneB c i then 1 else 0)
      + (∑ i : Fin k, if v ∈ twoA c i then 1 else 0) = k := by
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  rw [Finset.sum_congr rfl fun i _ => ite_trichotomy hc i v]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, Nat.nsmul_eq_mul, Nat.mul_one]

/-- **THE HANDSHAKE AT ONE VERTEX.**  There are `n-1` edges at `v`, at most two per colour, so
`2 · (colours used twice at v) + (colours used once at v) = n - 1`. -/
private theorem handshake (c : Col n k) (hc : Admissible c) (v : Verts n) :
    2 * (∑ i : Fin k, if v ∈ twoA c i then 1 else 0) + (∑ i : Fin k, if v ∈ oneB c i then 1 else 0)
      = n - 1 := by
  rw [← ite_sum_two, ← Finset.sum_add_distrib]
  rw [Finset.sum_congr rfl fun i _ => (card_nb_eq_twoA_oneB hc i v).symm]
  exact sum_nb_star c v

/-! ### §1  How many colours does a vertex miss? -/

/-- **THE PER-VERTEX IDENTITY.**  The number of colours missing at `v` is `k - (n-1)` plus the number
of two-edge paths centred at `v`:

    `#{i : v ∈ zeroA c i} + (n-1) = k + #{i : v ∈ twoA c i}`.

In words: a vertex of an admissible colouring uses each of the `k` colours at most twice, so it is
missed by `k - (n-1)` colours, plus one more for every two-edge path it centres. -/
theorem missing_at (c : Col n k) (hc : Admissible c) (v : Verts n) :
    (∑ i : Fin k, if v ∈ zeroA c i then 1 else 0) + (n - 1)
      = k + (∑ i : Fin k, if v ∈ twoA c i then 1 else 0) := by
  have h1 := three_way hc v
  have h2 := handshake c hc v
  omega

/-- **AT `k = n-2` EVERY VERTEX IS THE CENTRE OF A TWO-EDGE PATH.**  The identity of
`Window.missing_at` then reads `#{i : v ∈ zeroA c i} = #{i : v ∈ twoA c i} - 1 ≥ 0`, so the second
count is at least `1`: with `k = n-2` colours there are `n-1` edges at `v` and each colour occurs
at most twice, hence some colour occurs twice.  This is the pigeonhole of round 65, isolated as a
statement about the colouring. -/
theorem centre_of_paths (hc : Admissible c) (hk : k + 2 = n) (v : Verts n) :
    ∃ i : Fin k, v ∈ twoA c i := by
  by_contra h
  have hn : ∀ i : Fin k, v ∉ twoA c i := fun i hi => h ⟨i, hi⟩
  have hC : (∑ i : Fin k, if v ∈ twoA c i then (1 : ℕ) else 0) = 0 :=
    Finset.sum_eq_zero fun i _ => by rw [if_neg (hn i)]
  have h1 := missing_at c hc v
  rw [hC] at h1
  have hA0 : 0 ≤ ∑ i : Fin k, if v ∈ zeroA c i then (1 : ℕ) else 0 :=
    Finset.sum_nonneg fun i _ => (Nat.zero_le _)
  omega

/-- **A COLOURING WITH `k = n-2` COLOURS HAS AT LEAST `n` TWO-EDGE PATHS** — every vertex centres
one.  (The local content of `Vacant.isolated_ge_n`, read as a statement about `Paths`.) -/
theorem paths_ge_n {c : Col n k} (hc : Admissible c) (hk : k + 2 = n) : n ≤ Paths c := by
  have hone : ∀ v : Verts n, 1 ≤ ∑ i : Fin k, if v ∈ twoA c i then (1 : ℕ) else 0 := by
    intro v
    obtain ⟨i, hi⟩ := centre_of_paths hc hk v
    have hpos : 0 < ((Finset.univ : Finset (Fin k)).filter (fun j => v ∈ twoA c j)).card :=
      Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩
    rw [ite_sum_card]
    omega
  have hle : (Finset.univ : Finset (Verts n)).card
      ≤ ∑ v : Verts n, ∑ i : Fin k, if v ∈ twoA c i then 1 else 0 := by
    rw [Finset.card_eq_sum_ones]
    exact Finset.sum_le_sum fun v _ => hone v
  rw [Finset.card_univ, Fintype.card_fin] at hle
  have hsum : (∑ v : Verts n, ∑ i : Fin k, if v ∈ twoA c i then 1 else 0) = Paths c := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => (card_twoA_sum c i).symm
  rw [hsum] at hle
  exact hle

/-- **AT `k = n-1` THE TWO DEFECTS COINCIDE.**  `Surplus.global_identity` reads
`Isolated c = nk - n(n-1) + Paths c`, and `nk = n(n-1)` at `k = n-1`, so the unused slots and the
two-edge paths are the same number of incidences.  This is the regime of every verified construction
of this development (`Tables.sixCol`, `nineCol`, `tenCol`, `elevenCol`, `Ghost.ghostCol`), all of
which are 1-factorisations and so have `Paths = 0 = Isolated`. -/
theorem isolated_eq_paths (hc : Admissible c) (hk : k + 1 = n) : Isolated c = Paths c := by
  have h := global_identity hc
  have heq : n * k = n * (n - 1) := by rw [show k = n - 1 from by omega]
  rw [heq] at h
  exact Nat.add_left_cancel h

/-- **AT `k = n-2` THE TWO DEFECTS DIFFER BY `n`.**  `Isolated c + n = Paths c`: the paths outnumber
the unused slots by exactly the number of vertices.  Together with `Window.paths_ge_n` this says
`Isolated c ≥ 0`, with equality exactly when every vertex centres exactly one path. -/
theorem isolated_add_n_eq_paths (hc : Admissible c) (hk : k + 2 = n) :
    Isolated c + n = Paths c := by
  have h := global_identity hc
  have h2 : n * (n - 1) + n + Isolated c = n * k + n + Paths c := by omega
  have h3 : n * k + n = n * (n - 1) := by
    have hk' : n * (k + 1) = n * k + n := by rw [Nat.mul_add, Nat.mul_one]
    rw [← hk']
    congr 1
    omega
  rw [h3] at h2
  omega

/-- The refined lower bound is strictly below the ghost bound from `n = 13` on:
`(5n+6)/6 < n - 1` for every `n ≥ 13`. -/
private theorem div_step (n : ℕ) (hn : 13 ≤ n) : (5 * n + 1 + 5) / 6 < n - 1 := by omega

/-! ### §2  The window of `Ghost.lean` × `Vacant.lean`, and its collapse at `n = 12` -/

/-- **THE WINDOW.**  For every even `n ≥ 7` with `3 ∤ (n-1)` — the regime of the ghost colouring,
i.e. `n ≡ 0, 2 (mod 6)` — this development knows

    `⌈(5n+1)/6⌉ ≤ f(n,4,5) ≤ n-1`:

the lower end is round 65's per-vertex instrument, the upper end is the 1-factorisation
`Ghost.ghostCol` (`Main.EG_le_ghost_sub`). -/
theorem window_even (n : ℕ) (hn : 7 ≤ n) (heven : n % 2 = 0) (h3 : ¬ 3 ∣ (n - 1)) :
    (5 * n + 1 + 5) / 6 ≤ EG n ∧ EG n ≤ n - 1 :=
  ⟨EG_ge_ceil_five_sixth_plus_one n hn, EG_le_ghost_sub n (by omega) heven h3⟩

/-- **`f(12,4,5) = 11`.**  `n = 12` is even with `3 ∤ 11`, so the window has a single point: the
lower half `11 ≤ f(12,4,5)` is `Vacant.EG_twelve_ge_eleven`, and the upper half
`f(12,4,5) ≤ 11` is the ghost colouring of `K₁₂` with its eleven 1-factors. -/
theorem EG_twelve : EG 12 = 11 :=
  Nat.le_antisymm (window_even 12 (by norm_num) (by norm_num) (by norm_num)).2
    EG_twelve_ge_eleven

/-- **THE WINDOW IS A SINGLETON EXACTLY AT `n = 8` AND `n = 12`.**  For even `n ≥ 7` with
`3 ∤ (n-1)`, `f(n,4,5) = ⌈(5n+1)/6⌉`: the refined bound of round 65 is *attained* by the ghost
colouring.  The cases `n = 9, 11` are excluded by the evenness hypothesis, and `n = 10` by
`3 ∣ (n-1)`. -/
theorem window_collapse (n : ℕ) (hn : 7 ≤ n) (hn12 : n ≤ 12) (heven : n % 2 = 0)
    (h3 : ¬ 3 ∣ (n - 1)) : EG n = (5 * n + 1 + 5) / 6 := by
  rcases (show n = 8 ∨ n = 9 ∨ n = 10 ∨ n = 11 ∨ n = 12 from by omega)
    with h8 | h9 | h10 | h11 | h12
  · subst h8
    have h := EG_eight
    norm_num [h]
  · subst h9
    exact absurd heven (by norm_num : ¬ ((9 : ℕ) % 2 = 0))
  · subst h10
    exact (h3 (by norm_num : 3 ∣ (10 - 1))).elim
  · subst h11
    exact absurd heven (by norm_num : ¬ ((11 : ℕ) % 2 = 0))
  · subst h12
    have h := EG_twelve
    norm_num [h]

/-- **BEYOND `n = 12` THE TWO ENDS OF THE WINDOW ARE SEPARATED.**  For every `n ≥ 13`,
`⌈(5n+1)/6⌉ < n-1`, i.e. the two bounds this development knows for `f(n,4,5)` differ by at least
one colour and no exact value follows from them: at `n = 14` the window reads
`12 ≤ f(14,4,5) ≤ 13`, at `n = 18` it reads `16 ≤ f(18,4,5) ≤ 17`. -/
theorem window_separated (n : ℕ) (hn : 13 ≤ n) : (5 * n + 1 + 5) / 6 < n - 1 := div_step n hn

/-- **THE FIRST NINE EXACT VALUES** of `f(n,4,5)` known in this development, in one statement:
`5, 5, 5, 7, 7, 8, 9, 10, 11` at `n = 4, …, 12`.  The last four are rounds 65 and 66's. -/
theorem first_nine_exact :
    EG 4 = 5 ∧ EG 5 = 5 ∧ EG 6 = 5 ∧ EG 7 = 7 ∧ EG 8 = 7 ∧ EG 9 = 8 ∧ EG 10 = 9 ∧ EG 11 = 10 ∧
      EG 12 = 11 :=
  ⟨EG_four, EG_five, EG_six, EG_seven, EG_eight, EG_nine, EG_ten, EG_eleven, EG_twelve⟩

/-- **THE THREE SMALLEST OPEN ORDERS**, with the intervals this development can certify:
`f(13,4,5) ∈ {11,12,13}`, `f(14,4,5) ∈ {12,13}` and `f(15,4,5) ∈ {13,14,15}`. -/
theorem next_three_open :
    11 ≤ EG 13 ∧ EG 13 ≤ 13 ∧ 12 ≤ EG 14 ∧ EG 14 ≤ 13 ∧ 13 ≤ EG 15 ∧ EG 15 ≤ 15 := by
  have h14 := EG_ge_ceil_five_sixth_plus_one 14 (by norm_num)
  have h14a : 12 ≤ EG 14 := by omega
  have h14b : EG 14 ≤ 13 := EG_le_ghost_sub 14 (by norm_num) (by norm_num) (by norm_num)
  have h15 := EG_ge_ceil_five_sixth_plus_one 15 (by norm_num)
  have h15a : 13 ≤ EG 15 := by omega
  exact ⟨EG_thirteen_ge_eleven', EG_le_sumCol 13 (by norm_num), h14a, h14b, h15a,
    EG_le_sumCol 15 (by norm_num)⟩

set_option maxRecDepth 100000 in
/-- **THE `K₁₂` WITNESS HAS NO DEFECTS AT ALL — IT IS AN EXTREMAL 1-FACTORISATION.**  The ghost
colouring of `K₁₂` with `11` colours, the witness that closes §1, carries **no two-edge path** and
**no unused slot**: `Paths = 0` and `Isolated = 0`.  This is the opposite corner from §3, where every
edge is paid for by a two-edge path (`Paths = n(n-1)/6`, `Defect = 0`).  Both extremes are
admissible at `n = 12` resp. `n = 13`, so neither defect is forced by the catalog condition; what
`Surplus.surplus_of_k` prices is the *combination* `6 * Isolated + 2 * Defect = n * (6k - 5(n-1))`,
which is `0 = 6` here — i.e. the `K₁₂` witness attains the refined bound `6k = 5n + 1` exactly. -/
theorem ghost_twelve_defects :
    Paths (ghostCol 11 (by norm_num)) = 0 ∧ Isolated (ghostCol 11 (by norm_num)) = 0 ∧
      Defect (ghostCol 11 (by norm_num)) = 66 := by
  constructor
  · native_decide
  constructor
  · native_decide
  · native_decide

/-! ### §4  A verified witness produced by this round's search -/

/-- The admissible 11-colouring of `K₁₂` found by `discovery/JSP-000140/r66_walk` (seed 57,
20 392 921 steps, 0 violated four-sets; the table was re-checked independently in Python), written
down as a literal: entry `a * 12 + b` (`a < b`) is the colour of the edge `{a,b}`.  The other
entries are irrelevant — `Tables.listCol` reads `l.getD i 0` and `pairEnc` only ever produces
`min a b * 12 + max a b`. -/
def r66Col : List ℕ :=
  [0, 4, 1, 5, 3, 8, 2, 6, 10, 0, 7, 9, 0, 0, 4, 9, 2, 0, 5, 8, 3, 6, 10, 7, 0, 0, 0, 6, 10, 9, 6, 3, 5, 2, 0, 5, 0, 0, 0, 0, 4, 2, 7, 10, 0, 1, 4, 3, 0, 0, 0, 0, 0, 10, 0, 0, 6, 5, 8, 1, 0, 0, 0, 0, 0, 0, 4, 1, 7, 3, 1, 6, 0, 0, 0, 0, 0, 0, 0, 9, 1, 8, 3, 10, 0, 0, 0, 0, 0, 0, 0, 0, 2, 7, 5, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 9, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10, 9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
set_option maxRecDepth 100000 in
/-- **THE SEARCH WITNESS IS ADMISSIBLE**, certified by `native_decide` over all
`C(12,4) = 495` four-element vertex sets.  This is the round's search converted into a Lean proof,
in the style of `Tables.lean`. -/
theorem admissible_r66Col : Admissible (listCol 12 11 (by norm_num) r66Col) := by native_decide

/-- **`f(12,4,5) ≤ 11` FROM THE WITNESS**, i.e. independently of the ghost colouring of §1. -/
theorem EG_le_r66Col : EG 12 ≤ 11 :=
  EG_le_of_listCol 12 11 (by norm_num) r66Col admissible_r66Col

/-- **`f(12,4,5) = 11` FROM THE WITNESS SIDE.**  The two derivations of `Window.EG_twelve` are
independent: this one uses an explicit colouring found by search, that one uses the
1-factorisation of `Ghost.lean`. -/
theorem EG_twelve_by_witness : EG 12 = 11 := Nat.le_antisymm EG_le_r66Col EG_twelve_ge_eleven

/-! ### §3  Benchmark B5: `(13, 11)` would be an extremal colouring, hence an `STS` -/

/-- **THE SHAPE OF BENCHMARK B5, UPGRADED.**  If an admissible 11-colouring of `K₁₃` exists then
`Paths c = 26 = n(n-1)/6`: by `Window.isolated_add_n_eq_paths` and
`Vacant.extremal_at_thirteen_shape` (`Isolated c = 13`, `Defect c = 0`), the counting lemma
`Cherry.three_mul_paths_le_edges` is an equality, and every edge of `K₁₃` is paid for by a two-edge
path. -/
theorem thirteen_shape {c : Col 13 11} (hc : Admissible c) :
    Paths c = 26 ∧ Isolated c = 13 ∧ Defect c = 0 ∧ (pathFinset c).card = 26 := by
  have h := extremal_at_thirteen_shape hc
  have h2 := isolated_add_n_eq_paths hc (by norm_num)
  refine ⟨by omega, h.1, h.2, ?_⟩
  rw [card_pathFinset c hc (by norm_num)]
  omega

/-- **AN ADMISSIBLE 11-COLOURING OF `K₁₃` IS A STEINER TRIPLE SYSTEM.**  The two-edge paths of `c`
would form an `STS(13)`: at `n = 13` the counting bound is an equality, and
`Rigidity.tight_pathFinset_is_STS` turns an equality into the design.  This is the rigorous form of
benchmark B5: the exhaustive `(2,1)`-block searches of rounds 49–56
(`discovery/JSP-000140/sts212b.c`, 4 seeds × 2200 s on the cyclic `STS(13)`) were searching this
object, and their negative outcome is evidence that `f(13,4,5) = 12` — but no proof of the upper
bound is claimed. -/
theorem extremal_at_thirteen_is_STS {c : Col 13 11} (hc : Admissible c) :
    Paths c = 26 ∧ IsSTS (pathFinset c) := by
  have h := thirteen_shape hc
  have hD : (edgeFinset (Finset.univ : Finset (Verts 13))).card - 3 * Paths c = 0 := h.2.2.1
  have hcard := card_edgeFinset_univ_two 13
  exact ⟨h.1, tight_pathFinset_is_STS hc (by norm_num) (by omega)⟩

end JSP140
