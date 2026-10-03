## Status (round 66)

`lake build`: **OK** (3154 jobs; the new file `lean/JSPProblem/Window.lean` — 26 declarations,
17 public theorems, 0 placeholders — is on the default build path).  `sorry`/`admit`: **0**.
`harness/score.py --strict-prize problems/JSP-000140/lean`: `build_ok = true`, `partial_ok = true`,
`prize_ready = false`, `missing_theorems = ["jsp_000140_main"]`.

**ROUND 66 CLOSES ROUND 65'S OWN CHEAPEST BLOCKER: `f(12,4,5) = 11`, THE NINTH EXACT VALUE (TWICE —
once from the ghost colouring, once from a witness found by this round's new search and certified by
`native_decide`); IT READS THE PER-VERTEX VACANCY OF ROUND 65 AS AN EXACT STRUCTURE THEOREM; AND IT
TURNS BENCHMARK B5 INTO A STEINER TRIPLE SYSTEM.**

### 1. The premise of blocker B2 was false: `EG 12 = 11`

Round 65 recorded as the cheapest open item of the whole development

> `EG 12 = 11` is NOT proved: … but **no admissible 11-colouring of `K₁₂` is known**.  EVERY search
> of rounds 45-46 / 60 was run at `⌈5(n-1)/6⌉` colours, i.e. ONE BELOW the new bound.

`n = 12` is **even** with `3 ∤ (n-1)`, i.e. exactly the regime of `Ghost.lean`: the ghost colouring
`Ghost.ghostCol 11` is a 1-factorisation of `K₁₂` with `11` colours and is admissible by
`Ghost.admissible_ghost`.  So `Main.EG_le_ghost_sub 12` gives the upper half and
`Vacant.EG_twelve_ge_eleven` the lower one:

| new theorem | statement |
|---|---|
| **`window_even`** | `⌈(5n+1)/6⌉ ≤ f(n,4,5) ≤ n-1` for every **even** `n ≥ 7` with `3 ∤ (n-1)` (`n ≡ 0, 2 mod 6`) |
| **`EG_twelve`** | **`f(12,4,5) = 11`** |
| **`window_collapse`** | for even `7 ≤ n ≤ 12` with `3 ∤ (n-1)`: `f(n,4,5) = ⌈(5n+1)/6⌉` — the window is a singleton **exactly** at `n = 8, 12` |
| **`window_separated`** | for `n ≥ 13`: `⌈(5n+1)/6⌉ < n-1`, so the two ends differ by ≥ 1 colour and no exact value follows |
| **`first_nine_exact`** | `f(4..12,4,5) = 5, 5, 5, 7, 7, 8, 9, 10, 11` |
| **`next_three_open`** | `f(13,4,5) ∈ {11,12,13}`, `f(14,4,5) ∈ {12,13}`, `f(15,4,5) ∈ {13,14,15}` |

The first exact value obtained in this development by **combining** a construction (`Ghost.lean`)
with a lower bound (`Vacant.lean`): the ghost colouring attains round 65's refined bound.

### 2. Round 65's pigeonhole as an exact per-vertex identity (new)

`Surplus.global_identity` says `n(n-1) + Isolated c = nk + Paths c`, so at a fixed order the two
defects are pinned by `Paths c`.  Read per vertex — `n-1` edges at `v`, at most two per colour, and
twice exactly for the colours of the two-edge paths centred at `v` — one gets an exact count:

| new theorem | statement |
|---|---|
| `missing_at` | **`#{i : v ∈ zeroA c i} + (n-1) = k + #{i : v ∈ twoA c i}`** — the colours missing at `v` are `k-(n-1)` plus one per two-edge path centred at `v` |
| `centre_of_paths` | **`k = n-2 ⇒` every vertex is the centre of a two-edge path** (`Vacant.exists_twoA_of_le`, isolated as a theorem) |
| **`paths_ge_n`** | **`k = n-2 ⇒ n ≤ Paths c`** |
| `isolated_eq_paths` | `k = n-1 ⇒ Isolated c = Paths c` — **the two defects coincide** at the order of every verified construction here |
| `isolated_add_n_eq_paths` | `k = n-2 ⇒ Isolated c + n = Paths c` |

The two private counting tools behind them (`three_way`: `zeroA`/`oneB`/`twoA` partition the palette
as seen from `v`; `handshake`: `2·(twice) + (once) = n-1`) are the per-vertex analogues of
`Pairs.sum_nb_card_eq_two_mul_classIn_card`.

### 3. Benchmark B5 (`(13,11)`) reduces to a Steiner triple system

`Vacant.extremal_at_thirteen_shape` gives `Isolated c = 13`, `Defect c = 0`; with §2 this pins the
paths:

| new theorem | statement |
|---|---|
| `thirteen_shape` | an admissible 11-colouring of `K₁₃` has `Paths c = 26 = n(n-1)/6`, `Isolated c = 13`, `Defect c = 0`, `(pathFinset c).card = 26` — i.e. **`Cherry.three_mul_paths_le_edges` is an EQUALITY** |
| **`extremal_at_thirteen_is_STS`** | **its two-edge paths form an `STS(13)`** (`Rigidity.IsSTS`) |

So the exhaustive `(2,1)`-block searches of rounds 49–56 (`discovery/JSP-000140/sts212b.c`, 4 seeds ×
2200 s on the cyclic `STS(13)`) were searching exactly this space; their negative outcome is
evidence that `f(13,4,5) = 12`, but no upper bound above `11` is proved.

### 4. A new search instrument, and a witness certified in Lean

New solvers `discovery/JSP-000140/r66_walk.c` (incremental-mask WalkSAT: `mask[t]` is the colour
bitmask of a four-set, a move's delta is evaluated **exactly** over the `C(n-2,2)` four-sets
containing the edge, best move over the six edges of a random violated four-set, 4 % noise),
`r66_ils.c` (the same plus iterated local search) and `r66_2opt.c` / `r66_3opt.c` (exhaustive 2-opt
and restricted 3-opt repair around the best state).  They are **an order of magnitude better than the
round-57 min-conflicts code**: `r66_walk` finds the `(9,8)` witness in **915 steps**, where the old
code stalled at 63–111 violated four-sets out of 495 at the *easier* `(12,11)`.

* **`r66_walk` FOUND an admissible 11-colouring of `K₁₂`** (seed 57, 20 392 921 steps,
  `r66_w_12_11_57.out`), re-checked independently in Python (11 colours, 0 of 495 four-sets
  violated), and it is now a Lean theorem: **`Window.admissible_r66Col`** (`native_decide` over all
  `C(12,4) = 495` four-sets), hence **`Window.EG_le_r66Col : EG 12 ≤ 11`** and
  **`Window.EG_twelve_by_witness : EG 12 = 11`** — the second, independent derivation of §1 (the
  first uses the 1-factorisation of `Ghost.lean`).  This is the round's search converted into a
  certificate exactly as `Tables.lean` prescribes.
* **No witness at `(13,12)`, `(14,12)`, `(15,13)`, `(16,14)`** (see `r66_search_log.txt`): five
  runs at `(13,12)` reach **one** violated four-set of 715 and stay there, and both the exhaustive
  2-opt and the restricted 3-opt fail from there.  So `(13,12)` is either unattainable or needs a
  deeper repair; the residual is very likely a genuine obstruction, and `f(13,4,5) = 12` is the
  expected value.

### 5. NOT proved this round

The prize hypothesis `Main.AdmissibleUpper ε` (`0 < ε < 1/6`), the probabilistic existence theorem
of arXiv:2207.02920 §4, is untouched, so `jsp_000140_main` was again NOT declared: declaring it with
the hypothesis as an assumption would falsify the prize.

Lean 4.34.0 pitfalls recorded this round: `rw [mem_twoA]` FAILS when the goal contains
`if v ∈ twoA c i then …` (the `Decidable` instance depends on the rewritten term) — build the
positive/negative forms by hand from `hcases` instead; `Finset.sum_filter` is stated *filter-side =
if-side*, so indicator sums need `rw [(Finset.sum_filter p _).symm, Finset.card_eq_sum_ones]`; a
`∑` over `Fin k` is NOT an atom for `omega` when the summand involves `n % 2` or `3 ∣` hypotheses
in the context (supply `Finset.sum_nonneg` explicitly); `∑ i ∈ s, f i` may not span several lines
inside a `calc` step; `absurd h h'` needs `h' : ¬ p` when `h : ¬ p` is the *first* argument
(`exact (h (by norm_num : p)).elim` is the robust form).

## Status (round 65)

`lake build`: **OK** (3153 jobs; the new file `lean/JSPProblem/Vacant.lean` — 395 lines, 34 public
theorems + the `extremal_at_thirteen_shape` instance of §4, 0 placeholders — is on the default build
path).  `sorry`/`admit`: **0**.
`harness/score.py --strict-prize problems/JSP-000140/lean`: `build_ok = true`, `partial_ok = true`,
`prize_ready = false`, `missing_theorems = ["jsp_000140_main"]`.

**ROUND 65 LEAVES THE CENSUS FAMILY ENTIRELY AND IMPROVES THE PUBLISHED LOWER BOUND:
`f(n,4,5) ≥ ⌈(5n+1)/6⌉ = ⌈5(n-1)/6⌉ + 1` FOR EVERY `n ≥ 7` — AND CLOSES BENCHMARK B4.**
Rounds 63–64 established that the four-set census family is exhausted: every one of its instruments
(Cauchy–Schwarz on the colour-class profile, the per-class charge, the sharp balanced profile) reads
only the profile `(|E_i|)` and `Paths c`, and is silent at `(9,7)`.  This round uses the *one* input
the profile cannot see — a **per-vertex** one.

### 1. The new input: the leaf colour is VACANT at the centre of a two-edge path

| new theorem | statement |
|---|---|
| **`twoA_zeroA`** | if `v` is the centre of a two-edge path `a - v - b` of colour `i`, then `v ∈ zeroA c (c s(a,b))`: **the colour of the leaf edge occurs on no edge at `v`** |
| **`exists_zeroA_of_card_nb_eq_two`** | `|nb c i v| = 2 ⇒ ∃ j, v ∈ zeroA c j` |
| **`card_centres_le_isolated`** | the number of distinct two-edge-path centres is at most `Isolated c` |
| **`exists_twoA_of_le`** | `k + 2 ≤ n ⇒` **every** vertex is a two-edge-path centre (`Star.sum_nb_star` pigeonhole) |
| **`isolated_ge_n`** | **`n ≤ Isolated c` whenever `n ≥ 4` and `k ≤ n - 2`** |

The first row is `Strict.apex_zeroA` (round 53, stated for a labelled triangle of a `(2,1)`-block
colouring) read for an arbitrary two-edge path: `j = c s(a,b) ≠ i`, and if some edge at `v` had
colour `j` the `K₄` on `{v,a,b,x}` would carry `i,i,j,j` plus two edges — **at most four** colours.
Every later row is pigeonhole plus `Finset.card_biUnion_le`; nothing here is a four-set census.

### 2. The refined counting bound (§3)

| new theorem | statement |
|---|---|
| **`five_n_add_one_le_six_k`** | admissible `k`-colouring of `K_n`, `n ≥ 4`, `k ≤ n-2` ⟹ **`5n + 1 ≤ 6k`** |
| **`five_n_add_one_le_six_k_of_seven`** | **`5n + 1 ≤ 6k` for every `n ≥ 7`, unconditionally** |
| **`EG_ge_ceil_five_sixth_plus_one`** | **`⌈(5n+1)/6⌉ ≤ f(n,4,5)`**, the integral form |
| **`no_colouring_of_refined`** | `6k < 5n + 1 ⇒ ¬ ∃ c : Col n k, Admissible c` |
| **`refined_half_eps`** | `5n/6 + 1/6 ≤ f(n,4,5)`, the real form in the shape of the headline |
| **`refined_dominates_eg_strict`** | the round-53 bound `Strict.eg_strict` (`6k ≥ 5(n-1)+1`) is implied |

`Surplus.surplus_identity` prices the unused slots at six units each, so `Isolated c ≥ n` buys
**six** units of `6k` where round 53's `Isolated c ≥ 1` bought **one**: `6k ≥ 5(n-1) + 6 = 5n + 1`.
Since `⌈(5n+1)/6⌉ - 1 = ⌊5n/6⌋ ≤ ⌈5(n-1)/6⌉`, the refinement is **exactly one colour** above the
catalog bound at every `n ≥ 7` (`ceil_five_sixth_le_refined`).

### 3. The instances (§4) — **B4 IS CLOSED**

| new theorem | statement |
|---|---|
| **`no_seven_of_nine`** | **`f(9,4,5) ≥ 8`** — no admissible 7-colouring of `K₉`, **no search** |
| **`no_eight_of_ten`** | **`f(10,4,5) ≥ 9`** |
| **`no_nine_of_eleven`**, **`no_ten_of_twelve`** | `f(11,4,5) ≥ 10`, `f(12,4,5) ≥ 11` |
| **`EG_nine`, `EG_ten`, `EG_eleven`** | **`f(9,4,5) = 8`, `f(10,4,5) = 9`, `f(11,4,5) = 10`** (with `Tables.nineCol/tenCol/elevenCol`) |
| `EG_twelve_ge_eleven`, `EG_thirteen_ge_eleven'` | `f(12,4,5) ≥ 11`, `f(13,4,5) ≥ 11` |

Three consequences worth recording:

* **the 80-minute search certificate `Nine.certD_nine_six` is redundant.**  `Nine.lean` is kept off
  the default build path *because* of it, so `EG 9 = 8` was not on the default build path; it now
  is, from counting alone (`Vacant.EG_nine`).  The certificate and this argument agree exactly —
  an independent confirmation of the new bound at `(9,7)`;
* **benchmark B4 (`f(10,4,5) ∈ {8,9}`) is closed: `f(10,4,5) = 9`.**  Rounds 45–46 could not separate
  8 from 9; the bound `6k ≥ 5n+1` excludes `k = 8` outright;
* **`f(11,4,5) = 10`** is likewise new.

### 4. The shape at the refined bound (§5) and non-vacuity (§6)

* **`isolated_eq_n_defect_eq_zero`** — at `6k = 5n + 1` with `k ≤ n-2` every slot but one is used:
  `Isolated c = n` (each vertex missed by exactly one colour) **and** `Defect c = 0` (every edge
  paid for by a two-edge path).  This is what a construction must achieve to attain the new bound;
* **`extremal_at_thirteen_shape`** — **benchmark B5**: `n = 13, k = 11` is the first order at which
  the refined bound can be *attained* (`6 · 11 = 5 · 13 + 1`), so an admissible 11-colouring of
  `K₁₃` — if one exists — must have `Isolated c = 13` (every vertex missed by exactly one colour) and
  `Defect c = 0` (every edge paid for).  Together with `Strict.no_admissible_ten_of_thirteen` this is
  the whole of `Main.extremal_at_thirteen_is_open` in the currency of the defects;
* **`leafVacant_sixCol`, `leafVacant_nineCol`, `leafVacant_tenCol`, `leafVacant_elevenCol`** —
  `native_decide` verification of the leaf-colour lemma on all four verified constructions
  (`K₆, K₉, K₁₀, K₁₁`), so the instrument does not contradict any witness this development has;
* **`isolated_sixCol = 0`, `isolated_nineCol = 4`, `isolated_tenCol = 8`, `isolated_elevenCol = 10`** —
  every verified construction uses `k = n - 1` colours, i.e. **exactly** the number of edges at a
  vertex, so `isolated_ge_n` (which needs `k ≤ n-2`) does not apply to them and the new instrument is
  consistent with all of them.  It bites exactly in the regime **no** construction of the development
  reaches: a colouring with two wasted slots at every vertex.

### 5. What it costs the prize, stated honestly

* **`Main.AdmissibleUpper ε` (`0 < ε < 1/6`) is UNCHANGED** and remains the sole content of
  `jsp_000140_main`: the probabilistic existence theorem of arXiv:2207.02920 §4 / arXiv:2208.12563
  §4.  It was again **not** declared — declaring it with the hypothesis as an assumption would falsify
  the prize, and a *lower*-bound instrument cannot supply an existence theorem.  The published
  statement `f(n,4,5) = 5n/6 + o(n)` is untouched; only the `O(1)` at every order improves, by
  **one whole colour**;
* `EG 12 … EG 19` upper bounds, and `EG 12 = 11` — **not** proved: that needs an admissible
  11-colouring of `K₁₂`, which no search of rounds 45–46/60 produced (the searches were run for
  `⌈5(n-1)/6⌉` colours, i.e. **one below** the new bound, and must now be re-run one colour higher);
* `EG 13 = 11` (`Strict.EG_thirteen_ge_eleven` + a construction) and the `(2,1)`-block price of
  `BlockCol.lean` remain open as before.

### 6. Abandoned in this round

* the Python brute-force confirmation (`discovery/JSP-000140/r65_brute.py`) reached its node cap at
  `n = 7` and confirmed only `(6,4)`; it is recorded as inconclusive rather than as evidence.  The
  real confirmation is the agreement with the independent 80-minute certificate
  `Nine.certD_nine_six` at `(9,7)` and the `native_decide` checks of §6;
* the sharper `Isolated c ≥ n + #{v : c_v ≥ 2}`-type refinements and the census-style refinement of
  `Defect c`: not attempted (the equality case `isolated_eq_n_defect_eq_zero` already forces
  `Defect c = 0` there).

### 7. Lean 4.34.0 pitfalls recorded this round

* **file names are not namespaces**: every declaration of `Counting/Cherry/Surplus/Strict/Rigidity/
  Star/Tables/Triangles` lives directly in `namespace JSP140`, so write `apex_zeroA`, `surplus_of_k`,
  `eg_strict`, `sum_nb_star`, `nb_card_le_two`, `cherry_leaf_pair`, `EG_nine_le` — **not**
  `Strict.apex_zeroA` (only `Moment`, `Profile`, `Pairs`, `Quad`, `Pack`, `BlockCol` declare nested
  namespaces);
* `Star.lean` and `Rigidity.lean` are **not** in `JSPProblem.lean`'s import list; `sum_nb_star` and
  `cherry_leaf_pair` need an explicit `import JSPProblem.Star` / `JSPProblem.Rigidity`;
* `Counting.nb_card_le_two` takes the vertex set `S` as a **last explicit argument** — leaving it a
  metavariable puts `card ≤ 2` about a *different atom* and `omega` then fails at the pigeonhole step;
* `Finset.card_biUnion_le` has `s` and `t` **implicit** and concludes with the two-binder notation
  `∑ a ∈ s, #(t a)`; to feed it to `omega` write that notation verbatim (`∑ _i ∈ (Finset.univ :
  Finset (Fin k)), (zeroA c _i).card`) and close the goal with `rfl` — `∑ i : Fin k, …` is defeq but
  `simpa` does not bridge the two;
* `Pairs.mul_sub_add : m * (m-1) + m = m * m` needs the *same* `m` twice, so it does not apply to
  `5 * n * (n-1) + 5 * n`; write a private `mul_sub_one_add (a b) (hb : 1 ≤ b)` (and note it is
  **false** for `b = 0`);
* `Surplus.surplus_identity` is stated as `6 * (n * k) = 5 * n * (n-1) + …` but `Nat.mul_assoc` turns
  its LHS's `5 * n * (n - 1)` into `5 * (n * (n - 1))`, which `omega` and `exact` treat as a
  *different atom* than your own `5 * n * (n - 1)`: bridge the two with `ac_rfl` (as
  `Pairs.lean`'s own header records for `omega`);
* `Nat.le_of_mul_le_mul_left` takes the **inequality first** and the positivity second
  (`Nat.le_of_mul_le_mul_left h (by omega)`), and `Nat.succ_mul` is the right lemma for
  `a * (m + 1) = a * m + a` (`Nat.mul_add` gives it in the other direction);
* `ring` does **not** prove `5 * n + 1 = 5 * (n - 1) + 6` — it cannot handle `n - 1` over `ℕ`; use
  `omega` with a `1 ≤ n` hypothesis.

## Status (round 64)

`lake build`: **OK** (3152 jobs; the new file `lean/JSPProblem/Profile.lean` — 429 lines, 29 public
theorems + the `extremal_at_thirteen_shape` instance of §4, 0 placeholders — is on the default build
path).  `sorry`/`admit`: **0**.
`harness/score.py --strict-prize problems/JSP-000140/lean`: `build_ok = true`, `partial_ok = true`,
`prize_ready = false`, `missing_theorems = ["jsp_000140_main"]`.

**ROUND 64 CLOSES THE LAST MEMBER OF THE CENSUS FAMILY — `no_six_of_seven` — AND PROVES
`f(7,4,5) ≥ 7` ANALYTICALLY, i.e. WITHOUT THE 38 654-NODE SEARCH.**  Round 63 recorded
`no_six_of_seven` as the one instance the census could not reach (`Moment.momentOK 7 6` holds: the
Cauchy–Schwarz relaxation of the profile does not see it).  The missing input is a **per-class**
one, and it is the one input all three counting arguments discard.

### 1. The per-class charge (`lean/JSPProblem/Profile.lean`, §0–§2)

The census of `Pairs.lean` charges colour `i` with `choose |E_i| 2 + (n-4) * |A_i|` four-sets, and
`Paths.two_mul_classIn_le_add` (round 4) says **per class**

      `2 * |E_i| ≤ n + |A_i|`,      i.e.      `|A_i| ≥ 2|E_i| - n`,

so a colour class with more than `n/2` edges *must* pay for itself in two-edge paths.  Deleting
the forced part of that term leaves the **relaxed census**

| new theorem | statement |
|---|---|
| **`card_classF_le`** | `|E_i| ≤ n` for every colour class (max degree `2`) |
| **`profileCost`** | `choose |E_i| 2 + (n-4) * (2|E_i| - n)` — the relaxed charge of one class |
| **`profileCost_le_census_term`**, **`sum_profileCost_le_fourSets`** | **`∑_i [ choose |E_i| 2 + (n-4) * (2|E_i| - n) ] ≤ C(n,4)`** |

Cauchy–Schwarz only sees `∑_i |E_i| = C(n,2)`; this sees the **shape** of the profile.

### 2. The parity device (§1) — a genuinely new arithmetic observation

If `n` is odd and `∑_i 2|E_i| = n·k`, then

      `k ≤ 2 * ∑_i (2|E_i| - n)`.

Two ingredients, both proved: **`sum_sub_eq_sum_sub_rev`** (the two truncated sums `∑ (2|E_i| - n)`
and `∑ (n - 2|E_i|)` coincide whenever the untruncated sums agree — the identity `a - b = max a b - b`
summed) and **`sub_add_sub_ge_one`** (each pair `(2|E_i| - n) + (n - 2|E_i|) = |2|E_i| - n|` is at
least `1`, because `n` odd forbids `2|E_i| = n` — `two_ne_odd`).  The colour classes of an
admissible colouring satisfy the hypothesis exactly at `k = n - 1`, since
`2C(n,2) = n(n-1) = n·k`: **`surplus_ge_odd`**.

### 3. The charge obstruction, and the two instances

| new theorem | statement |
|---|---|
| **`charge_census`** | `∑_i choose |E_i| 2 + (n-4) * ((n-1)/2) ≤ C(n,4)` for odd `n`, `k = n-1` |
| **`chargeOK`** (predicate on the order alone), **`charge_obstruction`** | every admissible `(n-1)`-colouring of an odd `K_n` satisfies `C(n,2)² - (n-1)C(n,2) + (n-4)(n-1)² ≤ 2(n-1)C(n,4)` |
| **`not_chargeOK_seven`** | `¬ chargeOK 7`: `423 > 420` |
| **`no_six_of_seven`** | **`¬ (∃ c : Col 7 6, Admissible c)`** — no admissible six-colouring of `K_7`, *no search* |
| **`not_chargeOK_five`**, **`charge_no_four_of_five`** | the second instance (`76 > 40`) |
| **`EG_seven_ge_seven`**, **`EG_seven_lower_half`** | **`7 ≤ EG 7`** — the lower half of `Main.EG_seven : EG 7 = 7` with no certificate |

Together with round 63's `Moment.EG_seven_ge_six_census` (which rules out `k ≤ 5`) the analytic
route to `f(7,4,5) ≥ 7` is complete; `VertexSearch.certC_seven` is now **redundant** for that value.

### 4. §4–§5: the profile-alone form, and the margin

`sum_choose_two_seven` (`∑_i choose |E_i| 2 ≥ 27` — Cauchy–Schwarz gives `26.25` and the
integrality of the pair count rounds it up; the first load-bearing use of that integrality in this
development), `sum_surplus_seven` (`∑_i (2|E_i| - 7) ≥ 3`) and **`sum_profileCost_seven_six`**
(`∑_i profileCost 7 c i ≥ 36` for **every** profile of six classes summing to `21`, with no
hypothesis of admissibility) give §3 directly from the six integers `|E_1| …, |E_6|`.  Both bounds
are attained by the balanced profile `(4,4,4,3,3,3)` (`cost_four`, `cost_three`,
`balanced_cost_is_36`), and the exclusion misses by **one four-set** (`margin_is_one`:
`C(7,4) + 1 = 36`).

### 5. NOT proved this round

* **`Main.AdmissibleUpper ε` (`0 < ε < 1/6`) is UNCHANGED** and remains the sole content of
  `jsp_000140_main`: the probabilistic existence theorem of arXiv:2207.02920 §4 / arXiv:2208.12563
  §4.  It was again **not** declared — declaring it with the hypothesis as an assumption would
  falsify the prize.
* **The charge is vacuous from `n = 9` on** (`chargeOK_nine`, `chargeOK_eleven` — machine-checked).
  `EG 9 = 8` therefore still rests on the search certificate `Nine.certD_nine_six`, and `EG 12`,
  `EG 13`, … are unchanged (no admissible colouring at or near the counting bound was found for
  `n = 9..17` in round 60's campaign).
* **The census family is now exhausted at large `n`.**  With the *exact* balanced profile the
  relaxed cost at `(9,7)` is `120 ≤ C(9,4) = 126`, so even the sharp profile (the convexity lemma
  still missing, see `policy.json.next_lemma`) adds nothing beyond `Moment.moment_obstruction`
  except at `n = 5` and `n = 7`.  A *new* instrument is needed for `f(9,4,5) ≥ 8` analytically.

### 6. Abandoned in this round

A second file, `lean/JSPProblem/SharpProfile.lean`, was drafted for the **exact balanced-profile
minimum** `∑_i choose f_i 2 ≥ (k-r) choose q 2 + r choose (q+1) 2` (the item policy.json had named as
`next_lemma`).  Its *mathematics* is verified and needs neither smoothing nor a second
Cauchy–Schwarz — over `ℤ`, with `x_i = f_i - q` one has `∑ x_i = r`, `x² ≥ max x 0 ≥ x` and
`f_i² = x_i² + 2q x_i + q²`, hence `∑ f_i² ≥ kq² + 2qr + r` — and the recipe is recorded in
`policy.json`.  It did **not** compile within the round budget (the only obstruction was the
Lean-side lifting of a truncated `Nat` subtraction through `Int`, `Int.ofNat_sub` rewriting to the
commuted form `↑(a*b)*2` so that the matching rewrite fails), and since the sharp profile was
checked numerically to add **no** bound beyond `Moment.moment_obstruction` for `n ≥ 9`, the file was
deleted rather than left half-finished; the default build is `3152` jobs, `0` placeholders.

### 7. Non-vacuity

`charge_nineCol` and `charge_elevenCol` check `charge_obstruction` on the verified constructions
`nineCol` (8 colours on `K_9`) and `elevenCol` (10 colours on `K_{11}`): the instrument agrees with
the witnesses the searches of rounds 45–46 produced.

## Status (round 63)

`lake build`: **OK** (3151 jobs; the new file `lean/JSPProblem/Moment.lean` — 460 lines, 38
declarations, 0 placeholders — is on the default build path).  `sorry`/`admit`: **0**.
`harness/score.py --strict-prize problems/JSP-000140/lean`: `build_ok = true`, `partial_ok = true`,
`prize_ready = false`, `missing_theorems = ["jsp_000140_main"]`.

**ROUND 63 TURNS THE EXACT FOUR-SET CENSUS OF ROUND 62 INTO A QUADRATIC NECESSARY CONDITION ON
`(n, k)`, AND DECIDES `f(8,4,5) ≥ 7` ANALYTICALLY.**  `Pairs.lean` left the census as an identity
in the profile `(|E_i|)` and in `Paths c`; nothing yet said what that identity *rules out*.

### 1. The pincer on `Paths c`

| new theorem | statement |
|---|---|
| **`card_fourSets`** (§0) | `|fourSets n| = C(n,4)` — the census gets a numerical form |
| **`card_edges`** (§0) | `|E(K_n)| = C(n,2)`, division-free, from `card_edgeFinset_univ_two` + `Pairs.choose_two_mul` |
| **`sum_sq_card_mul_ge`**, **`sum_sq_classF`** (§1) | Cauchy–Schwarz: `k * ∑_i |E_i|² ≥ |E(K_n)|²` |
| **`pairs_lower`** (§1) | **`2k * ∑_i choose |E_i| 2 + k * |E| ≥ |E|²`** — the *lower* second moment, mirror image of `Pairs.sum_sq_le` |
| **`paths_le_of_census`** (§2) | `2k(n-4)Paths c + |E|² ≤ 2k C(n,4) + k|E|` — the census as an **upper** bound on `Paths c` |
| **`paths_ge_of_surplus`** (§3) | `6n(n-1) ≤ 6nk + 6 Paths c` — the exact surplus identity as a **lower** bound on `Paths c` |

### 2. The theorem

**`Moment.moment_obstruction`** — every admissible `k`-colouring of `K_n` (`n ≥ 4`) satisfies

    `6n(n-1)k(n-4) + 3·C(n,2)² ≤ 6nk²(n-4) + 6k·C(n,4) + 3k·C(n,2)`,

i.e. `3|E|² ≤ k · (6n(n-4)(k - (n-1)) + 6C(n,4) + 3|E|)`.  `Cherry.five_sixth_lower :
5(n-1) ≤ 6k` is **linear** in `k`; this is **quadratic**, and for fixed `n` it excludes every `k`
below a root exceeding `5(n-1)/6` exactly when `5n² - 63n + 158 < 0`, i.e. for `n ≤ 9`.
`Moment.EG_moment` states it for `EG n` itself.

### 3. What it decides (§6)

* **`no_six_of_eight` — `f(8,4,5) ≥ 7`, WITH NO SEARCH CERTIFICATE.**  The classical counting
  bound gives only `⌈35/6⌉ = 6` there (`Moment.classical_misses_eight` makes the gap explicit);
  `Main.EG_eight : EG 8 = 7` had been obtained from the *search certificate* `certC_eight_six`
  plus the ghost colouring.  Round 63 proves the lower half of `EG 8 = 7` by counting.  This is the
  `no_six_of_eight` that `Census.lean`'s §3 has advertised since round ~37 **without existing**;
* `no_four_of_four`, `no_four_of_five`, `no_five_of_seven` — `f(4,4,5) ≥ 5`, `f(5,4,5) ≥ 5`,
  `f(7,4,5) ≥ 6`, where the counting bound gives `3, 4, 5`;
* `no_four_of_six`, `no_six_of_nine`, `no_seven_of_ten` — the same argument at `n = 6, 9, 10`;
* `EG_five_ge_five_census` … `EG_ten_ge_eight_census` — the `EG`-form of each.

### 4. What it does *not* decide, stated honestly (§5, machine-checked)

* **`no_six_of_seven` is NOT a consequence of the census.**  `Moment.momentOK 7 6` holds, so the
  obstruction is silent at `(7,6)`, and `EG 7 = 7` still rests on the search certificate.  The
  `profile_cost_seven` / `profile_cost_eight` bullets of `Census.lean`'s §3 have never existed; §3
  of that header is **corrected** this round and now points at `Moment.lean`;
* **`census_at_least_five_sixth_below_eleven`** (`native_decide`, all `n < 11`, `k < 20`): below
  `n = 11` the census obstruction is at least as strong as the counting bound;
* **`census_weaker_at_eleven`**: at `(11, 8)` the situation is *reversed* — `momentOK 11 8` holds
  while `50 ≤ 48` fails.  The two instruments are genuinely incomparable from `n = 11` on, because
  the census left-hand side is `Θ(n³)` at `k = Θ(n)` against a right-hand side of `Θ(n⁴)`.  **So the
  published lower bound `f(n,4,5) ≥ 5n/6 - o(n)` is untouched; only the `O(1)` at four small orders
  improves, analytically.**

### 5. Non-vacuity (§7)

`moment_sixCol`, `moment_nineCol`, `moment_tenCol`, `moment_elevenCol` — the obstruction is
satisfied by **all four** verified constructions of `Tables.lean` (`K₆, K₉, K₁₀, K₁₁`), so §2 does
not contradict the witnesses the searches of rounds 45–46 produced.

### 6. What it costs the prize, stated honestly

The prize hypothesis `Main.AdmissibleUpper ε` for `0 < ε < 1/6` is **untouched** and remains the
sole content of `jsp_000140_main`.  `jsp_000140_main` was again **not** declared: declaring it with
`AdmissibleUpper` as a hypothesis would falsify the prize, and a *lower*-bound instrument cannot
supply the existence theorem.  B4 (`f(10,4,5) ∈ {8,9}`) and `EG 12, EG 14, …, EG 19` — unchanged.

### 7. Lean 4.34.0 pitfalls recorded this round

* **`Decidable` does NOT see through a plain `def`**: `native_decide` on `¬ momentOK 8 6` reports
  *"failed to synthesize `Decidable (momentOK 8 6)`"* until the predicate is marked
  `@[reducible]` — typeclass resolution never delta-unfolds an ordinary definition;
* `Multiset.sq_sum_le_card_mul_sum_sq` (`Mathlib/Algebra/Order/Chebyshev.lean`) quantifies over the
  **multiset element type** (the semiring is `α` itself), *not* over a scalar; for `f : Fin k → ℕ`
  use the `Finset` version `sq_sum_le_card_mul_sum_sq`, whose `simpa` normalisation
  `∑ i ∈ univ, f i ↦ ∑ i : Fin k, f i` is exactly what is needed;
* `Finset.powersetCard` takes the size **first**: `(Finset.univ : Finset (Finset α)).powersetCard 4`
  silently has type `Finset (Finset (Finset α))`, and `Finset.card_powersetCard` then yields
  `choose (Fintype.card (Finset α))`, not `choose (Fintype.card α)`;
* `norm_num` does **not** evaluate `Nat.choose` (`Nat.choose 8 4 = 70` is left open) while `decide`
  and `native_decide` do — for small arguments;
* `Nat.choose_two_mul` does **not** exist in this Mathlib; the available pair arithmetic is
  `Nat.choose_two_right`, and the round's own `Pairs.choose_two_mul` is what turns
  `2 * |E| = n * (n-1)` into `|E| = C(n,2)` by `omega`;
* `Nat.mul_add` has only its **last** argument explicit (`{m n} (k)`) while `Nat.mul_le_mul_left`
  has only its **multiplier** explicit — the two families read alike and are written in opposite
  orders; `Nat.add_le_add` takes **two** inequalities;
* `omega` does **not** normalise `5 * n * (n-1)` into `5 * (n * (n-1))`, so a hypothesis and a goal
  writing the same product with different parentheses are *unrelated atoms*: hand it the `by ring`
  equalities first.  The same holds for `k * (n-4) * Paths c`, which is why
  `moment_obstruction_raw` generalises all six terms and then calls `omega` **once**;
* **editing a header comment of an early file invalidates the whole downstream import chain**:
  the round-63 edit of `Census.lean`'s §3 header forced a full rebuild in which `Seven.lean`
  alone takes **19 minutes**.  Header-only edits are *not* cheap here.

## Status (round 62)

`lake build`: **OK** (3146 jobs; `lean/JSPProblem/Pairs.lean` grew from 770 to **1736 lines**,
from 33 to **117 declarations**, 0 placeholders, on the default build path).
`sorry`/`admit`: **0**.  `harness/score.py --strict-prize problems/JSP-000140/lean`:
`build_ok = true`, `partial_ok = true`, `prize_ready = false`,
`missing_theorems = ["jsp_000140_main"]`.

**ROUND 62 CLOSES THE OPEN LEMMA OF ROUNDS 40, 58, 60 AND 61: THE EXACT FOUR-SET CENSUS.**  The
identity `Census.lean` §2* has named as missing since round ~40 —

    `|twoFourSets c i| = choose |E_i| 2 + (n - 4) * (twoA c i).card`
    `|fiveFourSets c|    = ∑_i choose |E_i| 2 + (n - 4) * Paths c`
    `∑_i choose |E_i| 2 + (n-4) * Paths c ≤ |fourSets n|`  (`census_obstruction`)

— is now **proved**.  The tight four-sets of an admissible colouring are counted *exactly* by the
pairs of same-coloured edges, and hence by the sizes of the colour classes alone.

### 1. The three ingredients the previous round named as missing

| new theorem | statement |
|---|---|
| **`meeting_of_triangle`** | two edges of one colour inside a **three**-element vertex set **meet** (the pigeonhole consequence of `sum_nb_card_eq_two_mul_classIn_card`: `∑_{v ∈ T} |nb c i v T| = 2·2 = 4` over three vertices, each `≤ 1` under the negation) |
| **`endsF`, `card_endsF`, `span_endsF_eq`** | the vertex set of an edge, and **the unique four-set containing two disjoint edges** — the union of their four endpoints |
| **`meeting_of_ne_classIn`** | two four-sets carrying the same two colour-`i` edges are **equal** unless those two edges meet, in which case both carry the two-edge path at the **unique** common vertex |

### 2. The bijection, and then the census

* **`nonMeetingFourSets`** — the four-sets doubled in colour `i` which carry **no** two-edge path;
* **`exists_nonMeeting_of_mem_disjPairs`** — every disjoint pair of colour-`i` edges spans
  **exactly one** four-set, namely `endsF e ∪ endsF f`, whose colour-`i` class is the pair;
* **`classIn_mem_disjPairs`** — conversely, the colour-`i` class of a four-set with no path is a
  disjoint pair (`meet_or_disj` + `pathFourSets_of_mem_common`);
* **`card_nonMeetingFourSets`** — the two maps are inverse, so
  `|nonMeetingFourSets c i| = |disjPairs c i|` exactly (`Finset.card_bij`, no `Classical.choose`);
* **`card_pathFourSets_eq` / `card_meetingFourSets`** — the path half, exactly: each two-edge path
  lies in exactly `n-3` tight four-sets (`pathFourSets = containing (pathVerts c i v)`), so
  `|meetingFourSets c i| = |twoA c i| * (n-3)`;
* **`card_twoFourSets_census`**, **`fiveFourSets_census`**, **`census_obstruction`** — the three
  statements above.

### 3. What the census gives that the development did not have

* **`sum_choose_two_le_fiveFourSets`** — the number of pairs of same-coloured edges is at most the
  number of tight four-sets;
* **`sum_card_classF`** — `∑_i |E_i| = |E(K_n)|`;
* **`sum_sq_le`** — **THE SECOND MOMENT**: `∑_i |E_i|² ≤ 2·C(n,4) + |E(K_n)|`.  This is a necessary
  condition on the colour-class profile which `Surplus.surplus_identity` **cannot see**: that
  identity knows only `∑_i |E_i|`, `Paths c` and `Isolated c`, while the census uses the *pair*
  census.  Together with `Census.census_obstruction` (the linear form) the two bound the profile
  `(|E_i|)` from both ends.


### 3b. The last bullet of `Census.lean` §2*: `card_adjPairs`

`Pairs.lean` §13 adds the **ordered** version of the same count:

* `eq_common` — **two distinct edges have at most one common endpoint**;
* `adjEdgePairs` — the ordered pairs of distinct colour-`i` edges with a common endpoint;
* `card_fiber_meetOrders` — the number of such pairs through a fixed vertex is
  `|nb c i v| * (|nb c i v| - 1)`, i.e. the ordered pairs of distinct members of `nb c i v`;
* **`card_adjEdgePairs_eq`** — **`|adjEdgePairs c i| = 2 * |twoA c i|`**: the number of *ordered*
  pairs of equally coloured edges sharing a vertex is **twice** the number of two-edge paths, and
  **`sum_card_adjEdgePairs : ∑_i |adjEdgePairs c i| = 2 * Paths c`** globally.  Four more
  `native_decide` instances (`K₆, K₉, K₁₀, K₁₁`).

**With this, every bullet of `Census.lean` §2\* is a theorem**: `sum_twoFourSets` (`Quad.lean`),
`card_twoFourSets` → `Pairs.card_twoFourSets_census`, `card_adjPairs` → `Pairs.card_adjEdgePairs_eq`,
`census_obstruction` → `Pairs.census_obstruction`.  (The theorem names differ because the statements
are phrased on `classF c i` and `adjEdgePairs c i`; the content is the one written down in §2\*.)

### 4. Machine-checked instances (§12)

The **per-colour** census and the **global** census are `native_decide`-verified on all four
constructions of `Tables.lean`: `card_twoFourSets_census_{six,nine,ten,eleven}Col` and
`fiveFourSets_census_{six,nine,ten,eleven}Col`.

### 5. Housekeeping

`Pairs.lean`'s sections were renumbered (`§7` the two kinds of pairs, `§8` endpoints and the
triangle pigeonhole, `§9` the key lemma and the bijection, `§10` the path half, `§11` the census
identity, `§12` the instances), and the file header now describes the sections that actually exist.

### 6. What it costs the prize, stated honestly

The prize hypothesis `Main.AdmissibleUpper ε` for `0 < ε < 1/6` is **untouched** and remains the
sole content of `jsp_000140_main`.  `jsp_000140_main` was again **not** declared: declaring it with
`AdmissibleUpper` as a hypothesis would falsify the prize, and the four-set census — however sharp a
*necessary* condition it gives — is not the existence theorem.  B4 (`f(10,4,5) ∈ {8,9}`) and
`EG 12, EG 14, …, EG 19` — unchanged.

### 7. Lean 4.34.0 pitfalls recorded this round

* **`mem_foo.mpr` does NOT work for a theorem whose `(i)`-like argument is explicit**: `mem_meetingFourSets.mpr`
  reports *Unknown constant*; write `(mem_meetingFourSets i).mpr`.  Any dot-notation on a
  partially-instantiated iff must be parenthesised;
* **`Sym2.Mem` has no `DecidableEq`-instance search, and `Finset.filter` on it needs the local
  instance in scope** — including inside a `noncomputable def`, and the instance must be declared
  in the *same* section;
* **`h ▸ t` replaces the LEFT side of `h` by the right side** (not the other way round), and it
  silently picks the other direction when the expected type demands it — use it only where the
  expected type is known;
* **`congrArg` and `rw` both FAIL when the rewritten variable occurs in the type of another local
  hypothesis** (e.g. rewriting the edge `e` in `e ∈ edgeFinset (endsF e)`): "motive is not type
  correct".  The painless fix is to define `endsF e` as a `filter` (proof-irrelevant) instead of
  `insert e.out.1 (insert e.out.2 ∅)`, so no `Sym2.out` is needed at all;
* **`Finset.eq_of_subset_of_card_le (h : s ⊆ t) (h₂ : #t ≤ #s) : s = t`** — the card bound is on
  the *superset*; getting the direction wrong silently reinterprets the subset;
* **`Finset.card_bij (i : ∀ a ∈ s, β) (hi) (i_inj) (i_surj) : #s = #t`** — the dependent-function
  form (`fun a _ => …`), and `i_surj` returns `∃ a ha, i a ha = b` (an `And`, not `p`-`p`);
* **`Finset.card_eq_sum_card_fiberwise (H : (s : Set ι).MapsTo f t)`** is the *fiber* version, not the
  image version: the side goal is `∀ a ∈ s, f a ∈ t`, and the summand is
  `((s.filter fun a => f a = b) : Finset _).card`, which is `classF c i` up to `rfl`;
* **`Finset.sdiff` / `Nat.add_sub_of_le`** — `omega` cannot derive `t.card = s.card + (t \ s).card`
  from `(t \ s).card = t.card - s.card` (truncating subtraction); go through
  `Nat.add_sub_of_le` explicitly;
* **`Finset.mem_sym2_iff : m ∈ s.sym2 ↔ ∀ a ∈ m, a ∈ s`** is the painless way to prove
  `e ∈ edgeFinset (A ∪ B)` from `e ∈ edgeFinset A` (`mem_edgeFinset.mpr ⟨…, hd⟩`);
* `Nat.le_trans`, `Nat.mul_sub_one : m * n - m = m * (n-1)` (so `m*(m-1) + m = m*m` is
  `mul_sub_add`), `Finset.Subset.symm`, `Finset.Subset.antisymm`, `and_true`, `Finset.not_mem_empty`
  — the first two of these behave as documented, the last three **do not exist** in this version;
* chained projections `h.1.2` are **not** allowed (`Unexpected term`); bind `have h3 := h2.1` first;
* `rcases` tries `subst` on an `Eq` inside an `∃`, and the substitution can fail on
  filter-defined finsets ("Dependent elimination failed"): package the step in a lemma that
  returns `∃ v, …` instead of destructuring inline.

## Status (round 61)

`lake build`: **OK** (3146 jobs; the new file `lean/JSPProblem/Pairs.lean` builds in 8.1 s).
`sorry`/`admit`: **0**.  `harness/score.py --strict-prize problems/JSP-000140/lean`:
`build_ok = true`, `partial_ok = true`, `prize_ready = false`,
`missing_theorems = ["jsp_000140_main"]`.

**ROUND 61 ATTACKS THE EXACT PAIR CENSUS OF THE TIGHT FOUR-SETS — THE "DISJOINT-PAIR HALF" THAT
ROUNDS 58/60 NAME AS THE OPEN LEMMA OF THE DEVELOPMENT.**

### 0. Housekeeping: `Quad.lean` is now on the build path

Round 60 wrote `lean/JSPProblem/Quad.lean` but **never added `import JSPProblem.Quad`** to
`JSPProblem.lean`, so the file was never compiled by `lake build` and never appeared in any build
log.  `JSPProblem.lean` now imports `Quad` and `Pairs`.  `Quad.lean` closes the *counted-once* half of
the four-set census (`sum_twoFourSets`, `∑_i |twoFourSets c i| = |fiveFourSets c|`, the step
`Census.lean` §2* names) and its *inequality* half (`card_twoFourSets_ge_paths_mul`,
`(twoA c i).card * (n-3) ≤ |twoFourSets c i|`), with four `native_decide` instances.

### 1. What is missing, in one formula

A tight `K₄` (five colours, one of them doubled) is counted by **a pair of same-coloured edges**.
There are exactly two kinds of pair:

* **path pairs** — the two edges meet at a path centre `v ∈ twoA c i`; such a pair lies in exactly
  `n-3` four-sets (the three vertices of the path plus one more vertex);
* **disjoint pairs** — the two edges are vertex-disjoint; such a pair spans all four vertices, so it
  lies in **exactly one** four-set.

Hence the exact census is

    `|twoFourSets c i| = (n-3) * |twoA c i| + (choose |classF c i| 2 - |twoA c i|) = choose |classF c i| 2 + (n-4) * |twoA c i|`,

and, summing over the colours (`Paths c = ∑_i |twoA c i|`),

    `|fiveFourSets c| = ∑_i choose |classF c i| 2 + (n-4) * Paths c`.

### 2. New file `lean/JSPProblem/Pairs.lean` — the whole counting apparatus

| new | statement |
|---|---|
| **`sum_nb_card_eq_two_mul_classIn_card`** | **the handshaking lemma for a colour class**: `∑_{v ∈ S} |nb c i v S| = 2 * |classIn c i S|` — the pigeonhole engine that will decide "two edges of one colour inside a triangle meet" |
| `card_containing` | a **three-element** vertex set lies in **exactly `n-3`** four-sets |
| `pairsOf`, **`card_pairsOf`** | the two-element subsets of a finset: `T` has exactly `choose |T| 2` pairs (and `choose_two_mul`, `mul_sub_add` for the division-free form) |
| `classF`, `pairOf`, `spanFourSets`, **`card_pairOf`** | the colour class as a finset of edges, its pairs (`choose |classF c i| 2` of them) and the four-sets a pair spans |
| **`exists_fourSet_of_pair`** | **two distinct edges of `K_n` lie in a common four-set** (`n ≥ 4`): the only place endpoints of a `Sym2` value are needed |
| `iEdgesAt`, **`card_meetPairs`** | the colour-`i` edges at a vertex; **injectivity of `v ↦ iEdgesAt c i v` on `twoA c i`** (from `Sym2.eq_of_ne_mem`: two distinct edges have at most one common endpoint), so `|meetPairs c i| = |twoA c i|` |
| **`card_disjPairs`** | **`|disjPairs c i| = choose |classF c i| 2 - |twoA c i|`**: every two-element subset of a colour class is either the pair of edges of a two-edge path or a disjoint pair |
| `meetingFourSets`, **`mem_meetingFourSets_iff`** | the four-sets carrying a path: `S.card = 4 ∧ |classIn c i S| = 2 ∧ ∃ v ∈ S, |nb c i v S| = 2` |
| **`sum_card_meet_disj`** | `|meetPairs c i| + |disjPairs c i| = choose |classF c i| 2`, `native_decide`-verified on **all four** `Tables` constructions (`sum_card_meet_disj_sixCol`, `…nineCol`, `…tenCol`, `…elevenCol`) |

### 3. What is NOT finished, stated exactly

The census identity itself is **not** proved.  The single remaining mathematical ingredient is

* **`meeting_of_triangle`** — two edges of one colour inside a **three-element** vertex set must
  meet.  It is a pigeonhole consequence of `sum_nb_card_eq_two_mul_classIn_card`
  (`∑_{v ∈ T} |nb c i v T| = 2 |classIn c i T| ≥ 4` over three vertices, each `≤ 1` under the
  negation),

after which the rest is bookkeeping: `meeting_of_ne_classIn` (a vertex of `S \ S'` is on no `i`-edge,
so both `i`-edges of `S` lie in the triangle `S \ {x}`), the uniqueness of the four-set spanned by a
disjoint pair, and the two injective maps between the non-meeting four-sets and `disjPairs`.
`card_pathFourSets_eq` / `card_meetingFourSets` (each path lies in exactly `n-3` four-sets) were
drafted and cut for budget; `Quad.card_pathFourSets_ge` remains the only proved form.

### 4. What it costs the prize, stated honestly

The prize hypothesis `Main.AdmissibleUpper ε` for `0 < ε < 1/6` is **untouched** and remains the sole
content of `jsp_000140_main`.  `jsp_000140_main` was again **not** declared.  B4
(`f(10,4,5) ∈ {8,9}`) and `EG 12, EG 14, …, EG 19` — unchanged.

### 5. Lean 4.34.0 pitfalls recorded this round

* `Decidable (Sym2.Mem v e)` is **not** instance-searchable in this Mathlib: every finset filter on
  it needs a local instance (`local instance (n) (e) : DecidablePred (fun v => Sym2.Mem v e) := fun _ =>
  Classical.propDecidable _`) inside a `noncomputable section`;
* the `{x, y} : Finset α` notation **needs `[DecidableEq α]`**, so general-type lemmas must carry it;
* `Finset.mem_empty`, `Finset.not_mem_empty`, `Finset.mem_diff_singleton_eq`,
  `Finset.inter_subset_right` (it is a *Set* lemma), `Finset.exists_mem_not_mem_of_ne`,
  `Nat.mul_sub_left`, `Function.InjectiveOn` / `Set.InjOn`'s alias, `Nat.choose_zero` **do not exist**
  in this version — use `Finset.eq_empty_iff_forall_notMem`, `simp`,
  `fun v hv => (Finset.mem_inter.mp hv).2`, `Finset.sdiff_nonempty.mpr` with `¬ s ⊆ t`,
  `Finset.Subset.antisymm (Finset.subset_univ _) h`, `Nat.sub_mul`, `Nat.choose_one_right`;
* `Sym2.mem_iff` **cannot** used with `rw` (`Sym2.Mem` is a reducible `def`): `rw [h]` then
  `exact Sym2.mem_iff'`.  `Sym2.exists` has the shape `(∃ x, f x) ↔ ∃ x y, f s(x,y)`, so endpoints come
  from `Sym2.exists.mp (show ∃ z : Sym2 α, e = z from ⟨e, rfl⟩)`; there is no `Sym2.destructure`, but
  `e.out.1`, `e.out.2`, `Sym2.out_fst_mem`, `out_snd_mem` work;
* `Finset.mem_image.mp` produces `s(x,a) = e`, so rewriting the goal needs `rw [← heq]`;
* `Finset.card_image_of_injective` needs **global** injectivity; for a map injective only on a finset
  use `Finset.card_bij` with explicit arguments — and `Set.InjOn` / `Function.InjectiveOn` do not exist
  here, which silently breaks elaborations;
* `Nat.le_trans` infers its implicit arguments from the **first** argument, so `Nat.le_trans hle (by omega)`
  fails when the goal has them in the other order;
* `by_contra` / `intro` on `¬ (x ∈ univ \ T)` and `¬ (e ∈ loops S)` unfold the membership and bind
  **vertices** instead of the membership proof — go through `Finset.mem_sdiff`, `mem_loops`,
  `Finset.sdiff_nonempty.mpr` instead.

## Status (round 58)

`lake build`: **OK** (3144 jobs; the new file `lean/JSPProblem/Pack.lean` builds in ~9 s).
`sorry`/`admit`: **0**.  `harness/score.py --strict-prize problems/JSP-000140/lean`:
`build_ok = true`, `partial_ok = true`, `prize_ready = false`,
`missing_theorems = ["jsp_000140_main"]`.

**ROUND 58 CHANGES ATTACK FAMILY AGAIN — TO THE *PARTIAL* FIRST STAGE, WHICH IS WHAT THE PAPERS
ACTUALLY BUILD.**  Rounds 49–56 attacked the `(2,1)`-block colouring of a **triangle decomposition**
of `K_n` (a Steiner triple system), because that is the only shape in which the object was written
down.  But arXiv:2207.02920 §4 ("the first phase stops at `i_max = (1/6) n²(1 - n^{-δ})`, so the
hypergraph matching covers `1 - n^{-δ}` of the edges") and arXiv:2208.12563 Thm 4.2 (IV) ("the
graph `L = K_n - E(F)` has maximum degree at most `n^{1-δ}`") build a **partial** triangle packing whose
leftover graph is *sparse but nonempty*, and arXiv:2207.02920 Claim 4 measures it ("at the end of
Phase 1 each vertex is incident with `O(n^{1-δ})` uncolored edges").  This development had **no
object for that**: `TwoOne` carried an unused hypothesis `cover` (every edge in some block), which
made a leftover graph inexpressible.

### 0. `TwoOne` is now the published first stage

`lean/JSPProblem/BlockCol.lean`: the field `cover` of the structure `TwoOne` — **which no proof of
`BlockCol.lean` ever used** — has been **deleted**, so `TwoOne n k m` is now a **packing of
edge-disjoint triangles** with a centre and two distinct colours each (`uniq`, `card_three`), i.e.
exactly the output of the hypergraph matching of arXiv:2208.12563 §4.  The Steiner triple systems of
rounds 49–56 are the instances with `6 * m = n * (n-1)`, and nothing below changes for them.

New file `lean/JSPProblem/Pack.lean` (592 lines, 28 declarations, **20 public theorems**, zero
placeholders, on the default build path).

### §1 — the leftover graph of a packing

| new | statement |
|---|---|
| `PackL C` | the edges of `K_n` in **no** block: the leftover graph of the hypergraph matching |
| `TwoOne.not_mem_PackL` | every block edge is covered — `PackL C` is the complement of the packing |
| `PackL.offDiag`, `PackL.subset_univ` | leftover edges are edges |

### §2 — the census of a partial packing

| new | statement |
|---|---|
| `TwoOne.card_blEdge`, `Pack.blocks_card` | the `m` edge-disjoint blocks span exactly `3 * m` edges |
| **`Pack.census`** | **`6 * m + 2 * |PackL C| = n * (n - 1)`** — the blocks and their leftover partition `E(K_n)` |
| `TwoOne.decomposition_empty` | `6 * m = n * (n-1) ⇒ PackL C = ∅`: the rounds 49–56 shape is the `PackL = ∅` case |
| `Pack.card_two_mul_le` | `SparseL (PackL C) D ⇒ 2 * |PackL C| ≤ n * D` (the handshaking lemma `Slot.handshake_le`) |
| `Pack.blocks_ge` | `n * (n-1) ≤ 6 * m + n * D`: with `D = n^{1-δ}` the packing covers `1 - n^{-δ}` of `E(K_n)` |
| **`Pack.price`** | **`6 * k + 5 * D ≥ 5 * (n - 1)`**, i.e. `k ≥ 5(n-1)/6 - 5D/6` — the *partial* price |

`Pack.price` is the round-49–56 price `5 * m ≤ n * k` (`TwoOne.price`: five colour-slots per block)
combined with the census: `D = 0` gives the sharp constant `5(n-1)/6 ≤ 6k`, and the published
`D = n^{1-δ}` gives `6k ≥ 5(n-1) - 5n^{1-δ}`, i.e. `k = 5n/6 - o(n)` — the catalog answer with
the rate the papers achieve.

### §3 — the second stage of a *partial* first stage, with no admissibility assumption

* **`FirstOk c₀ L` — THE FIRST-STAGE LOCAL CONDITION (P0).**  For every four-set, the colours of the
  **covered** edges together with `⌈|edgeFinset S ∩ L| / 2⌉` reach five.  A partial packing **cannot**
  satisfy `Admissible c₀`: its colouring carries arbitrary values on the leftover edges.
  `FirstOk` is the correct replacement, and `FirstOk.of_decomposition` shows that for a Steiner
  triple system (P0) *is* `Admissible`.
* `Pack.fresh_colours` — the counting statement the condition is built on: under `Proper c L`, the `t`
  leftover edges of a four-set receive `⌈t/2⌉` **distinct** fresh colours (pigeonhole over the
  fibres, each fibre bounded by 2 because a colour class is a matching and three vertex-disjoint edges
  of `K₄` would need six vertices — the private lemma `disjoint_card_le_two`).
* **`Pack.second_stage`** — `FirstOk (C.col) (PackL C)` + `SparseL (PackL C) D` ⇒ **an admissible
  `k + 2 * D + 1` colouring of `K_n`**, and `Pack.eg_le` — `EG n ≤ k + 2 * D + 1`.  The fresh colours are
  the greedy ones of `proper_of_sparseL` (the bad events `A_{e,f,i}` = `B₁` are excluded greedily,
  with `O(n^{1-δ})` extra colours).

### §4 — **THE PRIZE HYPOTHESIS IN DESIGN LANGUAGE ONLY**

* **`PackFamily`** — for every `ε' > 0` there is `N` such that every `n ≥ N` carries a packing of
  edge-disjoint triangles with a centre and two colours each, a leftover of maximum degree `D`
  (constant in `n`), the local condition `FirstOk`, and the price `6 * (k₁ + 2D + 1) ≤ 5 * (n-1) + ε' * n`.
* **`Pack.target_of_packFamily` — `PackFamily → jsp_000140_target`** (via
  `Pack.fiveSixthUpper_of_packFamily` and `Main.fiveSixthLower_eg`).

This is weaker than round 33's `CrossStageFamily` in every respect that matters: **no admissible
colouring appears among the hypotheses** — not `Admissible c₀`, not `Covers`, not `PairFree`, not
`NoCrossFour`, not `NoBadFour`, not `Tile`, not `Packed`, not `LeafClosed`, and no second stage at all.
All of those are consequences of the local condition and the second stage is built in §3.  **What is
left is the hypergraph matching of arXiv:2208.12563 §4 together with the bound `D = O(n^{1-δ})`
on its own output** — a Rödl-nibble / random-triangle-removal existence theorem, which Mathlib does
not contain.

### What it costs the prize, stated honestly

The prize hypothesis `Main.AdmissibleUpper ε` for `0 < ε < 1/6` is **untouched** and remains the sole
content of `jsp_000140_main`.  What round 58 changes is the *statement of the hypothesis*: the prize is
now reduced to the **pure design existence theorem of the published construction** — a near-perfect
triangle packing with a centre-and-colour assignment — with no colouring, no admissibility and no
budget clause left in it.  `jsp_000140_main` was again **not** declared.  B4
(`f(10,4,5) ∈ {8,9}`, closed by `Strict.strict_EG_ten_ge_eight` + `Tables.EG_ten_le`) and
`EG 12, EG 14, …, EG 19` — unchanged.

### Lean 4.34.0 pitfalls recorded this round

* `Finset.Disjoint s t` is `fun a, a ∈ s → a ∉ t`, so `intro e he1 he2` in a `Disjoint` goal binds `he2` to a
  **negation** (`Finset.mem_biUnion.mp he2` is then a type error), and `Finset.not_mem_biUnion`
  does not exist — use `by_contra` + `rw [Finset.mem_biUnion] at ⊥` or `exact he2 (...)`;
* `Finset.card_biUnion` needs `Set.PairwiseDisjoint` (a `Finset.Disjoint` argument — awkward); the
  clean route is a private `card_biUnion_eq` proved by `Finset.induction_on` plus
  `Finset.card_union_add_card_inter`;
* **`Finset.card_union_le` and `Finset.card_biUnion_le` are *proofs*, not iffs: they can be used with
  `exact` but not with `rw`** (`rw` demands an equality/iff/definition);
* `Finset.card_eq_sum_card_image` lives in `namespace Finset` (`Nat.` prefix fails) and
  `Finset.card_image_iff : (s.image f).card = (s.image g).card ↔ Set.InjOn f s` with `g` defaulting to
  `id`, so `.mpr` gives `(s.image f).card = s.card`; `Finset.Pigeonhole.*` is *not* in the default
  import closure of `Mathlib.Tactic` (it needs
  `import Mathlib.Algebra.Order.BigOperators.Group.Finset`, which `Pack.lean` now adds);
* `Nat.le_of_mul_le_mul_left` takes `c * a ≤ c * b` (c on the **left**), `Nat.le_of_mul_le_mul_right`
  the other way round; `Nat.div_mul_le_self a b : a / b * b ≤ a` is the safe way to turn
  `a ≤ 2 * q` into `a / 2 ≤ q` (`Nat.le_div_iff_mul_le` has arg names `(k x y)` and leaves `k` a
  metavariable, so `(by omega)` for the positivity cannot be elaborated);
* `Finset.sum_const`, `Finset.card_univ`, `Fintype.card_fin` leave an `nsmul` (`n • 3`), which `ring` does
  **not** normalise: use `Nat.nsmul_eq_mul` (the plain `Nat.smul_eq_mul` does not exist) or `norm_num`;
* `liftCol` has two implicit lengths `{k' k}` and Lean will happily unify both with the same `k`;
  write `liftCol (k' := k) (k := k + K) c h` whenever the result type is not already known.  Comparing
  the cards of `image (liftCol c h)` and `image c` is **not** possible with `Finset.card_le_card`
  (different `Finset` types): go through the intermediate equality
  `(A.image (liftCol c h)) = (A.image c).image (fun j => ⟨j.val, _⟩)`;
* `Finset.mem_erase : a ∈ s.erase b ↔ a ≠ b ∧ a ∈ s`, so `.mp` returns an `And` (`.1`/`.2`, not
  `.left`/`.right`);
* `Finset.not_nonempty_iff_eq_empty : ¬s.Nonempty ↔ s = ∅` gives an **`Eq`**, which must be turned into a
  card fact with `Finset.card_eq_zero.mpr` (using `.mp` the other way round is a type error), and
  `Finset.exists_mem_of_ne_nil` does not exist;
* `Finset.card_le_card (s := …) (t := …)` needs `s` and `t` given explicitly **and** of the same finset
  type; `Forall` with two binders before `∈` (`∀ e e' ∈ T, …`) is a **parse error** — write the memberships as
  separate `→`s;
* `Nat.pos_of_ne_zero` needs `a ≠ 0`, not a `NeZero` instance; use `letI : NeZero k := C.hk` before
  writing `(0 : Fin k)`.

## Status (round 56)

`lake build`: **OK** (3142 jobs; the new file `lean/JSPProblem/BlockCol.lean` builds in 5.5 s).
`sorry`/`admit`: **0**.  `harness/score.py --strict-prize problems/JSP-000140/lean`:
`build_ok = true`, `partial_ok = true`, `prize_ready = false`,
`missing_theorems = ["jsp_000140_main"]`.

*(As in the rest of this file, theorem names are written with the file prefix; the declarations live
in `namespace JSP140`, e.g. `JSP140.TwoOne.labTri` in `lean/JSPProblem/BlockCol.lean`.)*

**ROUND 56 CHANGES ATTACK FAMILY AGAIN — TO THE CONSTRUCTION SIDE, AND WRITES DOWN THE
CONSTRUCTION ITSELF.**  Rounds 49, 50 and 55 all recorded the same gap in `policy.json`: *the
`(2,1)`-block colouring was never written down as Lean data*.  `Block.decomposition_eq` prices a
"decomposition colouring" abstractly, `Rigidity.tight_pathFinset_is_STS` extracts a Steiner triple
system from an extremal colouring, but there was no *function* from a triangle decomposition plus a
centre and two colours per block into an edge colouring of `K_n` — so the family could not be
searched in the form the papers build, and the two design conditions that round 55's exhaustive
search (`discovery/JSP-000140/fano_s1s2.py`) had to impose *by hand* were never proved to follow
from admissibility.  New file `lean/JSPProblem/BlockCol.lean` (545 lines, 28 declarations,
17 public theorems, zero placeholders, on the default build path).

### 1. §1 — the colouring

* `TwoOne` — the data: `bl : Fin m → Finset (Verts n)` a triangle decomposition (`cover`, `uniq`,
  `card_three`), a centre `ctr i` per block, and two **distinct** colours `pc i ≠ qc i`;
* **`TwoOne.col` — the colouring**: the edge of a block that touches the centre gets `pc i`, the
  opposite edge gets `qc i`.  It is written as a sum over the blocks and lifted to `Sym2` through
  `Sym2.lift`, so it is total on loops as well;
* `TwoOne.col_touch` / `TwoOne.col_notouch` / `TwoOne.col_ctr_leaf` — the three cases,
  *unconditionally*.

### 2. §2 — **every block is a labelled triangle of the colouring**

* **`TwoOne.labTri` — `LabTri (TwoOne.col C) (ctr i) a b`**: the block is a labelled triangle with
  `pc i` on the two edges at the apex and `qc i` on the opposite edge — the `(a, a, b)` pattern of
  arXiv:2208.12563 §4, and the bridge between `Block.lean` (the decomposition as data) and
  `Triangles.lean` / `Cover.lean` (the construction interface);
* `TwoOne.triVerts_eq` — the three vertices of that labelled triangle are the block.

### 3. §3 — **the two search conditions are theorems, not hypotheses**

| new theorem | statement |
|---|---|
| **`TwoOne.apex_zero`** | `Admissible (col C) → ctr i ∈ zeroA (col C) (qc i)` — **apex-avoidance is free** |
| **`TwoOne.leaf_isolated`** | `nb (col C) (qc i) a univ = {b}` and `= {a}` at the other leaf, and `qc i ≠ pc i` |
| `TwoOne.centre_twoA` | `ctr i ∈ twoA (col C) (pc i)` — the block is a two-edge path of the colouring |

They hold for **every** `(2,1)`-block colouring because they hold for every labelled triangle of an
admissible colouring (`Strict.apex_zeroA`, `Cherry.nb_eq_singleton_of_cherry`).  So the two
conditions `fano_s1s2.py` had to impose are **consequences of the catalog condition**, and the
`(2,1)`-block CSP can be searched with them as *derived* facts.

### 4. §4 — the price: **the construction cannot beat `5/6`**

* **`TwoOne.paths_neq`** — two blocks never share both their centre and their "twice" colour: the
  centre would carry four edges of one colour (the two blocks share at most one vertex, and it is
  their common centre), against `Counting.nb_card_le_two`;
* **`TwoOne.paths_ge` — `Paths (col C) ≥ m`**, hence **`TwoOne.price` — `5 * m ≤ n * k`** (five
  slots per block, `n * k` slots in the palette) — with `6 * m = n * (n-1)` this is the sharp
  constant;
* **`TwoOne.paths_eq_of_sts` / `TwoOne.price_exact` — `n * k = 5 * m + Isolated (col C)`**, i.e.
  `k = 5(n-1)/6 + Isolated/n`: `Block.decomposition_eq` for the *explicit* colouring;
* **`TwoOne.recipe` — `Isolated (col C) = n → 6 * k = 5 * (n-1) + 6`**, and `TwoOne.recipe_eg`
  the same for `EG n`: **what a search for the sharp constant has to find** — an admissible
  `(2,1)`-block colouring of some Steiner triple system with exactly `n` missed slots;
* **`TwoOne.thirteen` — `Admissible (col C) ∧ Isolated (col C) = 13 → EG 13 = 11`**: the whole of
  B5 at `n = 13` is now *one finite question about 26 blocks*, each choosing a centre and two of
  eleven colours — `f(13,4,5) = 11` would be the first order at which `f(n,4,5) = 5n/6 + 1/6`;
* `TwoOne.decomposition_gap` — the family never attains `6k = 5(n-1)`.

### 5. Search evidence collected in parallel (all NEGATIVE, recorded so it is not repeated)

* **The `(2,1)`-block family at `t = 1` has never been searched before** — rounds 49–52 attacked
  `t = 0` (10 colours), a target `Strict.no_admissible_ten_of_thirteen` refutes.  At `t = 1` the
  family is a CSP in **26 variables** (`sts212b.c`, backtracking with the three hard constraints,
  *complete*, so a negative result is decisive for that decomposition): 4 seeds × 2200 s and
  1.3 · 10⁸ nodes each on the cyclic `STS(13)` with 11 colours — **no solution**.  An earlier
  min-conflicts engine over the same table (`sts212.c`, 5.9 · 10⁶ iterations) stalls at
  52 violated four-sets of 715 with 214 slot clashes.  So the family is *not* competitive at
  `n = 13` either — consistent with `TwoOne.recipe`: the `t = 1` price is real but apparently hard
  to pay;
* the **free-form complete DFS with the structural propagations** of round 24 (`eg6_struct.c`,
  4 seeds × 1200 s, 8.2 · 10⁷ nodes per seed) does **not** find an admissible 11-colouring of `K₁₃`
  or `K₁₄` either (`eg6r`, `r13k11_s*.out`, `r14k11_s*.out`);
* a probe of the "six slots per cherry" mechanism (`slot_six_probe.py`) shows the four certified
  colourings all satisfy `6 · Paths ≤ n · k`, **but for the wrong reason**: in `nineCol`,
  `tenCol`, `elevenCol` one has `Paths > |apexFinset|` (4 > 3, 8 > 6, 10 > 6), i.e. distinct
  cherries *do* share an `(apex, leaf colour)` slot.  **`Apex.apexBound`'s pigeonhole is therefore
  the only correct form of that argument**, and the sharp constant comes from `3 · Paths ≤ |E|`
  (each cherry brings three fresh edges), not from six slots per cherry.  Recorded so that the
  "six slots" reading is not re-derived.

### 6. What it costs the prize, stated honestly

The prize hypothesis `Main.AdmissibleUpper ε` for `0 < ε < 1/6` — the probabilistic existence
theorem of arXiv:2207.02920 §4/§12 and arXiv:2208.12563 §4 — is **untouched** and remains the sole
content of `jsp_000140_main`.  What round 56 adds is the *construction object* itself, its exact
price, and the reduction of the whole `n = 13` instance to a single finite CSP with two derived (not
assumed) constraints.  `jsp_000140_main` was again **not** declared.  B4 (`f(10,4,5) ∈ {8,9}`,
closed by `Strict.strict_EG_ten_ge_eight` + `Tables.EG_ten_le`) and `EG 12, EG 14, …, EG 19` —
unchanged.

### 7. Lean 4.34.0 pitfalls recorded this round

* `Finset.mem_insert_self` takes **`(a) (s)`**, not `(s) (a)`; `Finset.card_eq_two s h` hands back
  `∃ x y, x ≠ y ∧ s = {x, y}`, which is *definitionally* `insert x (insert y ∅)` — so write the
  `insert` form in every statement and the rewrites go through;
* **`Sym2.rec`'s swap obligation is `h ▸ f a b = f c d`, and `▸` will not accept a `Sym2.Rel`
  proof.**  The painless route is `Sym2.lift ⟨f, fun a b => f a b = f b a⟩`, which is
  `def`-symmetric by construction and reduces on `s(a, b)` by `rfl`;
* `Finset.sum` over `Fin m` with values in `Fin k` needs `[NeZero k]`; carrying the instance as a
  *field* of the data structure (`hk : NeZero k`) and `letI := C.hk` at each use site is the only
  version that survives `unfold`;
* `Finset.card_le_card_of_injOn` has parameter names `s`, `t`, `f` (not `s₁`, `s₂`) and takes the
  `Set.MapsTo` proof *before* the `Set.InjOn` one;
* `Function.Injective f` has `a`, `b` **implicit**, so `hinj hab` is the whole proof;
  `Function.Injective f` is *not* `f`-valued `Eq`-first as one might expect from the printed type;
* `mem_nb : a ≠ v ∧ a ∈ S ∧ c s(v,a) = i` — the distinctness is `a ≠ v`, so a hypothesis
  `h : a ≠ C.ctr i` fits directly and `Ne.symm h` is *wrong* there;
* **`have hq' : a ≠ b' := …` silently shadows the destructured `hab' : a' ≠ b'`** and then reports
  "The argument `hab'` has type `a ≠ b'`" — this cost 20 minutes of the round; rename derived
  hypotheses (`hne_aa`, `hne_ab`, …);
* `omega` will not prove `0 < n * (n - 1)` from `4 ≤ n` (a product of two unknowns), and will not
  prove `5 * P ≤ a - P` from `6 * P ≤ a` if `P` only occurs inside `Paths c`; supply
  `Nat.mul_pos` / `Nat.pos_of_mul_pos_left` / `Nat.mul_div_le` and hand omega linear facts about the
  *atoms* only;
* `show` and `change` do **not** make `exact` see through a notation (`{a, b}` vs
  `insert a (insert b ∅)`); the goal must be stated in the same form as the hypotheses, or converted
  with `have key : … := rfl` plus `rw [← key]`;
* an *uninitialised* `int seen[512];` on the stack (`sts212b.c`) read as a duplicate pair and
  reported "not a decomposition" — always `= {0}`.

## Status (round 55)

`lake build`: **OK** (3141 jobs; the new file `lean/JSPProblem/Apex.lean` builds in 7.8 s and emits
no warnings).  `sorry`/`admit`: **0**.  `harness/score.py --strict-prize problems/JSP-000140/lean`:
`build_ok = true`, `partial_ok = true`, `prize_ready = false`,
`missing_theorems = ["jsp_000140_main"]`.

*(As in the rest of this file, theorem names are written with the file prefix; the declarations live
in `namespace JSP140`, e.g. `JSP140.apexBound` in `lean/JSPProblem/Apex.lean`.)*

**ROUND 55 CHANGES ATTACK FAMILY AGAIN — TO THE *SECOND ORDER* OF THE NECESSITY SIDE — AND PROVES
AN INTERPOLATING FAMILY OF LOWER BOUNDS.**  Round 53 proved that the sharp counting bound
`6k = 5(n-1)` is never attained, using the local fact `Strict.apex_zeroA` (the apex of a labelled
triangle has *no* edge of the leaf-colour).  This round turns that local fact into a **global
price list**: every two-edge path must be paid for in `Isolated c` units *at its apex*, so the
sharper a colouring gets against `5n/6`, the more the leaf-colours of its paths must repeat at
their apexes.  New file `lean/JSPProblem/Apex.lean` (383 lines, 22 declarations, 16 public theorems,
zero placeholders, on the default build path).

### 1. `Apex.apexBound` — THE INTERPOLATING LOWER BOUND

```lean
theorem Apex.apexBound {M : ℕ} (hc : Admissible c) (hn : 4 ≤ n) (hM : 1 ≤ M)
    (hmul : ∀ y : Fin k × Verts n, (fibre of `apexPair` at y).card ≤ M) :
    (n - 1) * (5 * M + 1) ≤ 6 * M * k
```

Equivalently `5(n-1) + (n-1)/M ≤ 6k`, i.e. over `ℝ` (`Apex.apexBound_real`)

    `f(n,4,5) ≥ 5(n-1)/6 + (n-1)/(6M)`   when no `(leaf colour, apex)` pair carries more than `M`
    two-edge paths.

`M` interpolates between the two constants the development knows:

* **`M = 1`** (`Apex.k_ge_of_unique_apexPair`): the leaf-colours of the paths at each apex are all
  distinct, so nothing can be saved below `n-1` — **`k ≥ n-1`**.  This is the regime of the
  round-robin and ghost constructions, and it says why they cannot be improved below `n-1` by any
  rearrangement that keeps the apex leaf-colours distinct;
* **`M → ∞`**: the sharp counting bound `5(n-1) ≤ 6k` of `Cherry.five_sixth_lower`, i.e. the
  catalog constant `5/6` is the *large-multiplicity end of the same one-parameter family*.

`Apex.deficit_le` is the same statement in the currency of "colours saved":

    `6 * M * (n - 1 - k) ≤ (M - 1) * (n - 1)`

so **saving `d` colours below `n-1` forces a `(leaf colour, apex)` pair to carry at least
`(n-1)/(6d) - 1` two-edge paths** (`Apex.exists_fibre_gt_of_deficit` gives the existential form).
Since BCDP22 attain `5n/6 + o(n)`, this says their first-stage triangle packing must have apex
leaf-colours of unbounded multiplicity — a **necessary condition on the output of arXiv:2207.02920
§4 that is not implied by anything in rounds 1–54**.

### 2. The price list, itemised

* **`Apex.LabTri_cherryPair`** — every two-edge path of an admissible colouring is a labelled
  triangle: the two edges at the centre share a colour, the leaf edge has a different one
  (`Rigidity.cherry_leaf_pair`).  This is the bridge between `Cherry.lean` and `Triangles.lean`, and
  it is what lets round 53's `apex_zeroA` be applied to *all* paths of `c`;
* **`Apex.apexPair` / `Apex.apexFinset`** — the `(colour of the leaf edge, apex)` pairs realised by
  the paths, a finset of `Fin k × Verts n` whose cardinality is the number of `Isolated c` units the
  paths cost;
* **`Apex.mem_apexFinset_zeroA`** — every such pair is a missing-colour slot (`p.2 ∈ zeroA c p.1`);
* **`Apex.card_apexFinset_le_isolated`** — **the distinct `(leaf colour, apex)` pairs are at most
  `Isolated c`** (`|apexFinset c| ≤ Isolated c`);
* **`Apex.card_cherryFinset_le_mul_apexFinset`** (pigeonhole over the fibres of `apexPair`) and
  **`Apex.paths_le_mul_isolated`** — **`Paths c ≤ M · Isolated c`**: paths are paid for in `Isolated`
  units at the rate of at least one unit per `M` paths;
* **`Apex.k_ge_of_no_path`** — `Paths c = 0 ⟹ k ≥ n-1`, directly from `Surplus.global_identity`.

### 3. Search evidence collected in parallel (all NEGATIVE, recorded so it is not repeated)

* **Merging colours of the round-robin colouring never preserves admissibility.**  For `n = 9, 11,
  13` and *every* merged group of 2, 3 or 4 colours, the merged colouring violates `Admissible`
  (`discovery/JSP-000140/rrmerge_probe.py`; the four-set colour-count profile of the round-robin
  colouring is `{5: 195, 6: 520}` at `n = 13`, so *every* pair of colours is blocked).  So the one
  explicit construction of this development is merge-minimal — consistent with `Apex.apexBound`
  (`M = 1` ⟹ `k ≥ n-1`).
* **A general min-conflicts engine cannot find admissible colourings at the counting bound.**
  `discovery/JSP-000140/wsat_eg.c` (WalkSAT over "every `K₄` spans ≥ 5 colours", 4 seeds × 60 s per
  target) stalls at 24–128 violated four-sets out of 330/495/715/3876 for
  `(n,k) = (11,9), (12,10), (13,11), (14,11), (15,12), (16,13), (17,14), (18,15), (19,16),
  (19,17)`.  Round 53's conclusion (free-form single-edge search is not competitive) is confirmed
  with an independent engine; no new finite value of `f` was obtained.
* **The `(2,1)`-block family of `Block.lean` is empty below 7 colours at `n = 7`.**  Exhaustive
  enumeration over all centre/colour assignments to the 7 Fano blocks
  (`discovery/JSP-000140/fano_s1s2.py`) finds **no** assignment satisfying both *slot-freeness*
  (the 5 `(vertex, colour)` pairs per block are globally distinct) and *apex-avoidance* (the apex
  has no edge of the leaf-colour) for `k = 5` or `k = 6`.  This is exactly the pair of design
  conditions that `Apex.apexBound` says any construction must pay for, and it is the first
  *decidable* statement about that family.
* A dedicated `(2,1)`-block search on the cyclic STS(13)
  (`discovery/JSP-000140/sts_block.c`, blocks in `sts13_cyclic_blocks.txt`) with 11 or 12 colours
  stays at 455–492 violated four-sets of 715; the `(2,1)` family is not competitive with the
  generic engine either.  (This is the same target that rounds 49–52 attacked for 10 colours and
  that `Strict.no_admissible_ten_of_thirteen` has since refuted.)

### 4. What it costs the prize, stated honestly

The prize hypothesis `Main.AdmissibleUpper ε` for `0 < ε < 1/6` — the probabilistic existence
theorem of arXiv:2207.02920 §4/§12 and arXiv:2208.12563 §4 — is **untouched** and remains the
sole content of `jsp_000140_main`.  What round 55 adds is a *necessary* condition on any
construction that comes close to `5n/6`: the two-edge paths must share leaf-colours at their
apexes, at a rate that grows as the colouring approaches the counting bound.  `jsp_000140_main`
was again **not** declared.  B4 (`f(10,4,5) ∈ {8,9}`, closed by `Strict.strict_EG_ten_ge_eight` +
`Tables.EG_ten_le`) and `EG 12, EG 14, …, EG 19` — unchanged.

### 5. Lean 4.34.0 pitfalls recorded this round

* `Finset.card_le_card_of_injOn (f := …) ?_ ?_` leaves `s` and `t` **unresolved** unless they are
  given explicitly: `(s := …) (t := …)`.  Without them the `MapsTo` goal is stated against
  `Finset.univ` and every proof attempt fails with a type mismatch that names the *witness* type.
* In the `MapsTo` goal the witness of `Finset.mem_image.mpr` is the **domain** element, not the
  image: for `t := s.image (fun v : Verts n => (i, v))` the witness is `y.2`, for
  `t := s.image (fun y => (i, y.2))` it is `y`.  Getting this backwards is the single most
  confusing error of the round.
* `congrArg Prod.fst h` with `h : f y = f w` elaborates the *conclusion* first and then demands
  `h : y = w`; to get `y.1 = w.1` from `h` you must annotate the function
  (`congrArg (fun q : Fin k × Verts n => q.1) h`) — and even then `f = fun y => (i, y.2)` is *not*
  injective on pairs, so the `y.1 = w.1` half must come from the `y.1 = i` side condition.
* `Finset.card_eq_two : s.card = 2 ↔ ∃ x y, x ≠ y ∧ s = {x, y}` is an **`Exists`**, not a `Sigma`,
  so it cannot be used as a type; the two witnesses must be read as `h.choose` and
  `h.choose_spec.choose`, and the `show`/`rw` must unfold the definition that wraps them (a
  `noncomputable def` with the two `choose`s inlined, *not* a `let`, or `show` will not see it).
* `Prod.ext_iff` / `Prod.mk.inj` disagree about which direction `mpr` goes; `Prod.mk.inj h` with
  `h : (i, y.2) = (i, w.2)` gives `i = i ∧ y.2 = w.2` and is the only painless route.
* `le_of_mul_le_mul_left` needs an explicit `[PosMulReflectLE α]` instance; over `ℕ` and `ℤ` it is
  available, and it is the clean way to cancel a factor `n ≥ 1` after a cast.
* `ring` fails on a goal containing `Nat.sub` (`(M-1) * X + (5M+1) * X = 6M * X`): `Nat.sub` is not
  a ring term.  `rw [← Nat.mul_add]` (with the arguments written out) plus `Nat.sub_add_cancel`
  does it; after `obtain ⟨M', rfl⟩` from `Nat.exists_eq_add_of_le` the goal is a genuine ring
  identity and `ring` works.
* `omega` normalises products into atoms but does **not** identify `(n-1) * (5M+1)` with
  `(5M+1) * (n-1)`, nor `6 * (1 + M') * k` with `6 * (M' + 1) * k`: every hypothesis written by
  hand must use **exactly** the parenthesisation of the goal it is fed to, or `omega` silently
  treats the two as unrelated atoms (this cost about 40 minutes of the round).
* `mul_le_mul_of_nonneg_left/right` infer the multiplier from the second argument's type; passing
  the multiplier positionally (`(6 : ℤ)`) makes Lean guess `k`, so write `(a := (6 : ℤ))`.
* `rw` closes a goal that becomes *syntactically* a hypothesis; a trailing `linarith` after such a
  `rw` reports "no goals to be solved".  In a `calc` step this shows up as a spurious error one
  line later.

## Status (round 53)

`lake build`: **OK** (3140 jobs; the new file `lean/JSPProblem/Strict.lean` builds in 6 s and emits
no warnings).  `sorry`/`admit`: **0**.  `harness/score.py --strict-prize problems/JSP-000140/lean`:
`build_ok = true`, `partial_ok = true`, `prize_ready = false`,
`missing_theorems = ["jsp_000140_main"]`.

**ROUND 53 IS THE FIRST ROUND THAT IMPROVES THE SHARP LOWER BOUND: THE COUNTING BOUND
`6k = 5(n-1)` IS NEVER ATTAINED.**  New file `lean/JSPProblem/Strict.lean` (≈ 380 lines, 21
declarations, zero placeholders, on the default build path).

### 1. `Strict.apex_zeroA` — the whole obstruction is one `K₄`

Let `(u; p, q)` be a labelled triangle of an admissible `c`: `λ = c s(u,p) = c s(u,q)` on the two
edges at the **apex** `u`, `μ = c s(p,q) ≠ λ` on the opposite edge.  Then

> **the apex `u` has no edge of colour `μ` at all**, i.e. `u ∈ zeroA c μ`.

One line: if `c s(u,x) = μ` for some `x ≠ u`, then `x ∉ {u,p,q}` (both triangle edges at `u` carry
`λ`) and the `K₄` on `{u,p,q,x}` spans `λ, λ, μ, μ, c s(p,x), c s(q,x)` — **at most four**
colours, against the five the catalog condition demands.  So the four-set `{u,p,q,x}` is a bad
`K₄`, exactly the witness `Cover.not_admissible_*` exhibits for the other shapes.

### 2. `Strict.isolated_pos` — a two-edge path costs a `(vertex, colour)` slot

`Strict.isolated_pos_of_mem` (`v ∈ zeroA c i ⟹ 0 < Isolated c`) plus `Strict.isolated_pos`
(`0 < Paths c ⟹ 0 < Isolated c`: a centre `v ∈ twoA c i` gives the two neighbours `a, b`, hence
`LabTri c v a b` by `Cherry.nb_eq_singleton_of_cherry`, hence a missed slot).  So:

> **the two extremality conditions of `Surplus.surplus_identity` are incompatible.**

### 3. `Strict.not_sharp` — THE HEADLINE LOWER BOUND IS STRICT

```lean
theorem Strict.not_sharp {n k : ℕ} {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n) :
    ¬ (6 * k = 5 * (n - 1))
```

`Surplus.clean_of_extremal` turns `6k = 5(n-1)` into `Isolated c = 0 ∧ Defect c = 0`; `Defect c = 0`
says every edge is paid for by a two-edge path, so `Paths c > 0`, and §2 says `Isolated c ≥ 1`.

| new theorem | statement |
|---|---|
| `Strict.apex_zeroA` | `LabTri c u p q ⟹ u ∈ zeroA c (c s(p,q))` |
| `Strict.isolated_pos_of_mem` | `v ∈ zeroA c i ⟹ 0 < Isolated c` |
| `Strict.isolated_pos` | `0 < Paths c ⟹ 0 < Isolated c` |
| **`Strict.not_sharp`** | **`Admissible c → ¬(6k = 5(n-1))`** |
| `Strict.eg_never_sharp` | `¬(6·EG n = 5(n-1))` |
| **`Strict.eg_strict`** | **`5(n-1) + 1 ≤ 6·EG n` for every `n ≥ 4`** |
| `Strict.eg_ge_one_mod_six` | `m ≡ 1 (mod 6), m ≥ 7 ⟹ EG m ≥ m/6 + 1` (a whole extra colour) |
| `Strict.eg_strict_scaled` / `eg_strict_real` | `6·(EG n - 5n/6) ≥ -4`, i.e. `EG n ≥ 5n/6 - 2/3` |
| **`Strict.no_admissible_ten_of_thirteen`** | **`¬ ∃ c : Col 13 10, Admissible c`** |
| `Strict.EG_thirteen_ge_eleven` | `11 ≤ EG 13` |
| `Strict.EG_nineteen_ge_sixteen`, `EG_twentyfive_ge_twentyone`, `EG_thirtyone_ge_twentyfive` | `EG 19 ≥ 16`, `EG 25 ≥ 21`, `EG 31 ≥ 26` |
| **`Strict.no_extremal_colouring`** | **`¬ ∃ n k c, Admissible c ∧ 6k = 5(n-1)`** |
| `Strict.strict_is_finite` | the new lower bound is compatible with `FiveSixthLower EG 1` |

### 4. What it settles

* **`Main.extremal_at_thirteen_is_open` is decided**: `K₁₃` admits **no** admissible 10-colouring.
  `n = 13` is the first order at which the counting bound is an integer (`Rigidity.tight_mod6`
  forces extremality to `n ≡ 1 (mod 6)`), so the "first attainment of the sharp constant `5/6`
  beyond `n = 6`" that B5 and rounds 49–52 hunted for **does not exist**, and `Strict.no_extremal_
  colouring` says it does not exist at any order.
* **The ~1.5 CPU-hours of `(2,1)`-block searches of rounds 49–52 (`discovery/JSP-000140/sts_*.c`,
  `sts13_*.out`) were provably futile.**  `Strict.no_admissible_ten_of_thirteen` refutes the target
  of all of them.  The "best bad = 1 of 715 four-sets" evidence was measuring a family that cannot
  contain a solution.  (Independently, the free-form engine written this round,
  `discovery/JSP-000140/eg13_sa.c`, cannot even *find the known* admissible 5-colouring of `K₆`
  with 5 colours reliably — see §6.)
* **The lower half of the prize is strictly better than `Cherry.five_sixth_lower`**:
  `f(n,4,5) ≥ 5(n-1)/6 + 1/6`, and `≥ 5(n-1)/6 + 1` on `n ≡ 1 (mod 6)`.  This is still
  `5n/6 - O(1)`, so **the published statement `f(n,4,5) = 5n/6 + o(n)` is untouched** — it is not
  refuted, only sharpened at the `O(1)` level (`Strict.strict_is_finite`).
* **Every extremal-structure theorem of this development is now a theorem about the empty class**:
  `Rigidity.tight_*`, `Extremal.tight_*`, `Star.tight_*`, `Local.tight_*`, `Classwise.tight_*`,
  `Block.decomposition_eq`, `Surplus.extremal_of_covered_cherries`, `Sharp.jsp_000140_main_of_sharp`
  all assume `6k = 5(n-1)`, i.e. `Rigidity.tight_mod6` (`n ≡ 1 (mod 6)`), `tight_pathFinset_is_STS`
  (a Steiner triple system of two-edge paths) and the per-vertex profile
  `Main.star_centre_is_one_third` — none of which can occur.

### 5. Cost of the search engines, recorded so the next round does not repeat it

`discovery/JSP-000140/eg13_sa.c` (this round; incremental SA with breakout weights, bitmask
evaluation, time check inside the annealing loop, best-state printout) and `eg13free.c` (Breakout +
tabu + min-conflicts) were both written from scratch this round:

* `eg13_sa 8 7 20 5` — best **8 violated four-sets out of 70**, although `EG 8 = 7` is *proved* in
  this development (`Main.EG_eight`, from `VertexSearch.certC_eight_six`);
* `eg13_sa 13 13 15 1` — best 15 of 715, although the round-robin colouring is admissible;
* `eg13_sa 12 10 85 11` — best 83 of 495; `12 11` — 63; `13 11` — 111.

So the **free-form single-edge neighbourhood is not competitive with the existing engines**, and the
"no 10-colouring of `K₁₃`" question never had search evidence behind it.  Both programs are kept
(`eg13_sa` has the time check and the best-state printout that `eg8_sa` lacks) but neither is worth
CPU time in the next round.  The real finite targets left are `EG 12` and the non-extremal values,
and the only engine that ever worked (`FastSearch.hasAdmissibleSymG`, symmetry-reduced
depth-first, completeness proved) is out of reach beyond `n = 7`.

### 6. Lean 4.34.0 pitfalls recorded this round

* `Finset.card_eq_zero : s.card = 0 ↔ s = ∅` — the `mpr` direction wants `s = ∅`, so wrap the
  "no member" argument in `Finset.eq_empty_iff_forall_notMem.mpr` (it exists; `not_mem_empty`
  does not).
* `Finset.single_le_sum_of_canonicallyOrdered (Finset.mem_univ i)` gives `f i ≤ ∑ j, f j` for
  `f : Fin k → ℕ`; with the argument `f` left as a metavariable the instance search **fails**, so
  write the helper as `private theorem sum_ge_of_mem (f : Fin k → ℕ) (i : Fin k)`.  `omega` cannot
  relate a specific summand to the sum — chain with `lt_of_lt_of_le` instead.
* A `have h : T := bigTerm` is **opaque**, so neither `rw [h]` nor `show …` sees through it; define
  local sets as a `private def` (here `Strict.fourColours`) instead of a `have`.
* `Finset.mem_insert_self _ _` + `mem_in_insert` chains: the number of `mem_in_insert` wrappers is
  *not* the nesting depth minus one — Lean peels one level while elaborating `exact`, so an
  over-long chain reports "type mismatch" on the innermost `mem_insert_self`.
* `exact_mod_cast` **fails** on a statement containing a truncated `n - 1`; restate as
  `5 * n - 4 ≤ 6 * k` (pure `omega`) and then cast.
* `Nat.mul_pos` needs two explicit positivity goals, and `omega` will not derive `0 < n * (n-1)`
  from `4 ≤ n` (the `/2` in `n*(n-1)/2`); supply `Nat.mul_pos` and `Nat.div_pos` by hand.

## Status (round 52)

`lake build`: **OK** (3139 jobs; the new file `lean/JSPProblem/Sharp.lean` builds in 6.5 s).
`sorry`/`admit`: **0**.  `harness/score.py --strict-prize problems/JSP-000140/lean`:
`build_ok = true`, `partial_ok = true`, `prize_ready = false`,
`missing_theorems = ["jsp_000140_main"]`.

**ROUND 52 PROVES THAT THE COVERING CLAUSE OF THE PUBLISHED STATEMENT IS A THEOREM.**
New file `lean/JSPProblem/Sharp.lean` (468 lines, 18 declarations, zero placeholders, on the
default build path).  Rounds 29–51 asked for a colouring that is (i) *admissible*, (ii) *covered by
labelled triangles* (`Triangles.Covers`), and (iii) *cheap* (`6k ≤ 5(m-1) + δm`).  Round 52 shows
that (ii) is **not an extra requirement**.

| new theorem | statement |
|---|---|
| `Sharp.covered_iff_cherry` | `Covered c e ↔ ∃ i v, v ∈ twoA c i ∧ e ∈ cherryEdges c i v` |
| `Sharp.card_sdiff_leftover` | `|E(K_n) \ leftover c| = 3 * Paths c` |
| `Sharp.card_leftover_le` | `6k ≤ 5(n-1) + d ⟹ |leftover c| ≤ n*d/2` |
| `Sharp.card_leftover_of_eps` | `k ≤ 5n/6 + εn ⟹ |leftover c| ≤ 3εn² + 6n` |
| `Sharp.card_leftover_of_one` | `6k ≤ 5(n-1)+1 ⟹ |leftover c| ≤ n/2` |
| `Sharp.covers_of_extremal` | `Admissible c ∧ 6k = 5(n-1) ⟹ Covers c` |
| `Sharp.not_covers_ge` | `¬Covers c ⟹ 5(n-1)+1 ≤ 6k` |
| `Sharp.two_mul_leftover_add` | `2*|leftover c| + 5n(n-1) ≤ 6nk` (**refined sharp lower bound**) |
| `Sharp.triFamily_of_extremal` | `Admissible c ∧ 6k = 5(m-1) ⟹ Covers ∧ PairFree ∧ NoCrossFour ∧ NoBadFour` |
| `Sharp.TriFamilyAdmissible.slack` | `TriFamilyAdmissible ⟹ SlackFamily` (the `Covers` conjunct is free) |
| `Sharp.jsp_000140_main_of_admissibleUpper` | `AdmissibleUpper 1 ⟹ jsp_000140_target` |
| `Sharp.leftover_of_admissibleUpper` | the `o(n²)` leftover clause comes with the colouring |
| `Sharp.jsp_000140_main_of_sharp` | `6*EG m = 5(m-1)` on `m ≡ 1 (mod 6)` for large `m` ⟹ `jsp_000140_target` |

### Why this matters

A labelled triangle `(u; p, q)` of `c` is **exactly** a two-edge path `p - u - q` together with its
leaf edge `s(p,q)` (`covered_iff_cherry`), so the triangle covering of arXiv:2208.12563 §4 and the
`K₄` counting of `Cherry.lean` are the *same object*.  Hence the number of edges the covering misses
is `|E| - 3·Paths`, which is bounded by `n·d/2` as soon as `6k ≤ 5(n-1) + d`.  In particular

* at the extremal point `6k = 5(n-1)` the covering is **complete** — so an extremal admissible
  colouring *is* the published construction, and the "hypergraph matching" clause is forced by
  sharpness, not assumed;
* the "up to `o(n²)` edges" clause is **free** — every asymptotically optimal colouring covers all
  but `3εn² + 6n` edges;
* the sharp bound `5(n-1) ≤ 6k` is the `|leftover| = 0` case of the refined bound
  `2|leftover| + 5n(n-1) ≤ 6nk`: **uncovered edges cost colours**.

### What this leaves

`AdmissibleUpper 1` — for every `ε > 0` and all large `n`, an admissible `k`-colouring of `K_n` with
`k ≤ 5n/6 + εn` — is now **proved minimal**: every structural clause of every interface of rounds
29–51 (covering, matching, four-sets, leftover) is a theorem of `Admissible` plus the budget.  The
remaining content is the probabilistic existence theorem of arXiv:2207.02920 §12 / arXiv:2208.12563
§4 (`Partial.FamGreedyFamily`), which Mathlib cannot supply (no Rödl nibble, no local lemma).

### Lean 4.34.0 pitfalls recorded this round

* `Iff.mp` goes left → right; `.mpr` goes right → left.  Getting this backwards produces a very
  confusing "argument has type X but expected Y" error.
* `have h := f x (by omega)` **shadows** an outer hypothesis named `h`, and the tactic then cannot
  see the outer one.  Rename the inner binding whenever its name coincides.
* `omega` over two *truncating* `Nat.sub`s can lose a constraint (it over-approximates the model);
  restate the arithmetic as equalities (`L + 3*Paths = |E|`, `2*|E| = n*(n-1)`) plus a `calc`.
* `Nat.cast_div` followed by `push_cast` leaves the side goals `2 ∣ n*d` and `↑2 ≠ 0`; prefer the
  doubled form `2 * L ≤ n * d`.
* `Finset.filter_subset _ _` needs a `DecidablePred` instance for the filter of a `noncomputable def`
  (`leftover`); supply the subset proof as `fun e he => (mem_leftover.mp he).1` instead.

## Status (round 51)

`lake build`: **OK** (3138 jobs, 14 s incremental).  `sorry`/`admit`: **0**.
`harness/score.py --strict-prize`: `partial_ok = true`, `prize_ready = false`,
`missing_theorems = ["jsp_000140_main"]`.

**ROUND 51 CLOSES THE MATCHING-CONDITION BLOCKER `pairFree_of_admissible`, CARRIED OPEN SINCE ROUND
29 AND LEFT WITH ~40 TACTIC LINES OF BOOKKEEPING IN ROUND 50.**  `lean/JSPProblem/Cover.lean`
grew from 485 to **733 lines** and from 24 to **40 declarations**; nine of them are new public
theorems, zero placeholders, on the default build path.

### 1. `Cover.PairFree_of_admissible` — the matching condition is a THEOREM

`PairFree` was the one hypothesis of `Triangles.TriFamily` that had never been discharged from the
catalog condition.  It is now:

```lean
theorem PairFree_of_admissible {n k : ℕ} {c : Col n k} (hc : Admissible c) : PairFree c
```

proved via the round-50 role semantics in a nine-case analysis
(`Cover.triVerts_eq_of_mem_triPairs`, §2 of the file), with these three new private lemmas:

* **`role_norm`** — the role of `v` in a labelled triangle `(u; p, q)`, in normal form: either the
  *labelled* role (`v = u`, `j = c s(u,p)`), or a *path-leaf* role (after naming the other leaf
  `w`: `LabTri c u v w`, `c s(u,v) = j`, `triVerts u v w = triVerts u p q`), or an *opposite-leaf*
  role (`LabTri c u v w`, `c s(v,w) = j`, same vertex-set identity);
* **`lab_unify`, `path_unify`, `opp_unify`** — the three cases in which the two triangles coincide:
  both labelled (the two `j`-neighbour sets are `{p,q}` and `{p',q'}`), both path leaves (the unique
  `j`-neighbour of `v` is the labelled vertex of both, so `u = u'`, then `{v,w₁} = {v,w₂}`), and both
  opposite leaves (`w₁ = w₂`, then either `u = u'` or `obstruction_two`);
* **`lab_leaf_false`** — a labelled role and a leaf role at the same `(v, j)` force `(Nbrs c j v).card`
  to be both `2` and `1`.

The remaining four cases are ruled out by the round-50 obstructions: path/opposite and
opposite/path by `Cover.obstruction_one`, opposite/opposite with `u ≠ u'` by
`Cover.obstruction_two`.  **The whole matching condition is therefore a consequence of the catalog
condition**, and `Triangles.TriFamily` is no stronger than the statement "there is an admissible
colouring covered by labelled triangles with the right budget".

### 2. The price of a triangle family: where `5/6` comes from

* **`card_triPairs_five` — `(triPairs c u p q).card = 5`**: the five pairs
  `(u,λ), (p,λ), (q,λ), (p,μ), (q,μ)` are pairwise distinct.
* **`five_mul_card_le` — `5 * |T| ≤ n * k`** for a family `T` of labelled triangles of an
  admissible colouring with pairwise distinct vertex sets (the disjointness is now `PairFree`,
  proved above; counted with `Finset.card_disjiUnion`).
* **`five_mul_card_le_decomposition` — `5(n-1) ≤ 6k`**: a triangle *decomposition* of `K_n`
  (`6·|T| = n(n-1)`) therefore satisfies the catalog lower bound with the sharp constant `5/6` —
  read off the construction encoding (`n(n-1)/6` triangles, five pairs each) rather than by
  counting colour classes as in `Cherry.three_mul_paths_le_edges`.  This is the first formal
  appearance of the *reason* for `5/6` inside the construction interface.

### 3. The packing statements, now free

* **`triVerts_eq_of_mem_triEdges_admissible`** — two labelled triangles of an admissible colouring
  never share an edge (arXiv:2208.12563 §4: the triangles form a *matching*);
* **`exists_labTri_of_mem_of_admissible`** — all the colour-`i` edges at a vertex lie in one single
  labelled triangle;
* both are `Triangles.triVerts_eq_of_mem_triEdges` / `exists_labTri_of_mem` with `PairFree`
  discharged by §1.

### 4. The prize hypothesis, restated in the catalog language

* **`Cover.TriFamilyAdmissible`** — `Triangles.TriFamily` with `PairFree c` replaced by
  `Admissible c` (everything else unchanged: `Covers`, `NoCrossFour`, `NoBadFour`, the budget
  `6k ≤ 5(m-1) + δm`);
* **`TriFamily.of_admissible`** — the two forms are equivalent, i.e. the second phase of
  arXiv:2207.02920 §12 does **not** need a separate matching verification;
* **`jsp_000140_main_of_tri_family_admissible`** — the required statement follows from it.

**What is still missing is unchanged: the existence of the labelled-triangle system itself**
(`Partial.FamGreedyFamily`, a Rödler–nibble / random-triangle-removal existence theorem).  Both
papers constructing it are probabilistic, so there is no explicit colouring to formalise.

### Implementation notes for the next round

* This Lean version (4.34.0) **cannot parse a multi-line `by` block inside a `calc` step** when
  further steps follow — the parser reports `unexpected identifier; expected ':='`.  Restructure
  such `calc`s into `have`s plus `exact a.trans (b.trans c)`.
* `choose ... using h` abstracts over *every* free variable of `h`, including a `hU : U ∈ S`
  argument; use the `h ∨ ¬h` trick to keep the chosen function on `U` alone, or pass the triples
  themselves as the data (as `five_mul_card_le` does, which avoids `Classical.choose` entirely).
* `Finset.disjoint_left.mpr` is the way to build `Disjoint s t` for finsets (`Disjoint` is a class,
  `Disjoint.intro` does not exist), and `Finset.card_disjiUnion` / `Finset.sum_const_nat` are the
  two counting lemmas needed for the pigeonhole.
* `lean/JSPProblem/Cover.lean` compiles in **7 s** (no `native_decide`); `Seven.lean` (~50 min)
  and `Amplify.lean` (~150 s) were not touched, their oleans were replayed.

## Status (round 50)

`lake build`: **OK** (3138 jobs, 18 s incremental).  `sorry`/`admit`: **0**.
`harness/score.py --strict-prize`: `partial_ok = true`, `prize_ready = false`,
`missing_theorems = ["jsp_000140_main"]`.

**ROUND 50 ATTACKS THE MATCHING-CONDITION BLOCKER `pairFree_of_admissible` — CARRIED OPEN SINCE
ROUND 29 — AND PROVES ITS TWO NON-TRIVIAL LEMMAS.**  Rounds 46–49 attacked the sharp constant
from the *construction* side (lexicographic products, Steiner triple systems, `(2,1)`-block
colourings).  Round 50 attacks the other side: whether the matching condition of the published
construction (`Triangles.PairFree`) is an *extra* hypothesis or a *consequence* of the catalog
condition.  It is a consequence, and the reason is structural.

New file `lean/JSPProblem/Cover.lean` (485 lines, 24 declarations, **5 public theorems**, zero
placeholders, **on the default build path**).

### 1. The structural observation

For a labelled triangle `(u,p,q)` write `λ = c s(u,p) = c s(u,q)` and `μ = c s(p,q) ≠ λ`.  Its
five `(vertex, colour)` pairs are

  `(u, λ)` — the *labelled* pair (both `λ`-edges meet at `u`);
  `(p, λ), (q, λ)` — the two *path* leaves;
  `(p, μ), (q, μ)` — the two *opposite* leaves.

So a pair `(v, j)` of the triangle says one of only two things about `v`: either `v` is the
labelled vertex and has **two** `j`-neighbours, or `v` is a leaf and has **exactly one**.  The
uniqueness in the second case is the whole content, and it is provable from admissibility:

* **`Cover.pathLeaf_sem` — THE PATH-LEAF ROLE.**  If `a - u - b` is a two-edge path of colour `j`
  then the *only* `j`-edge at `a` is `s(a,u)`: `(Nbrs c j a).card = 1` and `u ∈ Nbrs c j a`.
  (If `w ≠ u` were another `j`-neighbour of `a`, then `w ∉ {a,u,b}` and the `K₄` `{a,u,b,w}`
  would carry three `j`-edges, `s(a,u)`, `s(a,w)`, `s(u,b)`.)  This is the isolated-two-edge-path
  lemma `Cherry.nb_eq_singleton` re-proved in the form the construction needs.
* **`Cover.oppLeaf_sem` — THE OPPOSITE-LEAF ROLE.**  If `s(a,b)` is the opposite edge of a
  labelled triangle, of colour `j`, then the *only* `j`-edge at `a` is `s(a,b)`:
  `(Nbrs c j a).card = 1` and `b ∈ Nbrs c j a`.  (If `w` were another `j`-neighbour of `a`, then
  `w ∉ {a,u,b}` and the `K₄` `{a,u,b,w}` would span at most three colours: `j` on `s(a,b)` and
  `s(a,w)`, `λ` on `s(a,u)` and `s(u,b)`, and the colour of `s(u,w)`.)  Note the conclusion is
  *stronger* than a bare cardinality statement: it says the `j`-edge at `a` is the opposite edge.
* **`Cover.centre_sem` — THE LABELLED ROLE.**  `(Nbrs c j u).card = 2`, with the two leaves as its
  elements.

### 2. The two obstructions, and the three `K₄` shapes they use

* `not_admissible_path_pair`, `not_admissible_path_pair2`, `not_admissible_path_pair3` — the three
  shapes of "two two-edge paths on one `K₄`", each proved by exhibiting the six edges' colours in
  a finset of at most four elements (`colorsOn_sub_six`), so `Admissible` fails.
* **`Cover.obstruction_one`** — a vertex cannot be the *path* leaf of one labelled triangle and the
  *opposite* leaf of another with the same `(vertex, colour)` pair.  (The unique `j`-neighbour of
  `v` is then both a labelled vertex and an other leaf, so `w' = u`, and the `K₄` on the four
  vertices carries the three-colour configuration `not_admissible_path_pair2`.)
* **`Cover.obstruction_two`** — a `(vertex, colour)` pair cannot be the *opposite*-leaf pair of two
  labelled triangles with **different** labelled vertices.  (The unique `j`-neighbour of `v` forces
  the two other leaves to coincide, and then the `K₄` carries `not_admissible_path_pair3`.)

### 3. What is still missing, precisely

`Cover.PairFree_of_admissible` (= `triVerts_eq_of_mem_triPairs`) needs five cases on the role of
`v` in the two triangles:

| `v` in `T₁` | `v` in `T₂` | verdict |
| --- | --- | --- |
| labelled | labelled | same two `j`-neighbours ⇒ `triVerts u p q = triVerts u' p' q'` |
| labelled | leaf | `(Nbrs c j v).card` would be `2` and `1` |
| path leaf | labelled | ditto |
| path leaf | path leaf | unique `j`-neighbour of `v` is `u = u'`, then case 1 |
| path leaf | opposite leaf | `obstruction_one` |
| opposite leaf | path leaf | `obstruction_one` |
| opposite leaf | opposite leaf | other leaves agree; then case 1 or `obstruction_two` |

Four of the cases need only `sub_insert2_of_card_le_two` + `pair_eq_of_pair`, one needs the two
obstructions; **all the substantive mathematics is proved**.  The remaining piece is the
bookkeeping: routing the role data of the two triangles through a single disjunction
(`role_of_mem` composed with `centre_sem`, `pathLeaf_sem`, `oppLeaf_sem`).  The draft of that
assembly was removed rather than left as a stub, so the file keeps zero placeholders and records
the five-case plan itself in its section 2.  Consequence: `PairFree` remains an assumption of
`jsp_000140_main_of_tri_family` for this round, but the blocker is now *reduced* rather than open.

## Status (round 49)

`lake build`: **OK** (3137 jobs).  `sorry`/`admit`: **0** (`placeholder_total = 0`).
`harness/score.py --strict-prize` (invoked on `problems/JSP-000140/lean`):
`build_ok = true`, `partial_ok = true`, `prize_ready = false`,
`missing_theorems = ["jsp_000140_main"]`.

**ROUND 49 CHANGES ATTACK FAMILY FOR THE FIRST TIME SINCE ROUND 14: FROM THE *NECESSITY* SIDE OF
THE SHARP CONSTANT TO THE *CONSTRUCTION* SIDE — AND IT WRITES DOWN, FOR THE FIRST TIME IN THIS
DEVELOPMENT, AN ACTUAL STEINER TRIPLE SYSTEM.**  Rounds 19–48 all worked on what an extremal colouring
*must* look like (`Rigidity.tight_pathFinset_is_STS`, `tight_mod6`, `Extremal.tight_ge_thirteen`,
`Main.star_profile_at_thirteen`, `Classwise.tight_thirteen_profile`, …): the development knows that an
extremal colouring of `K_n` decomposes `E(K_n)` into triangles and colours each with a `(a,a,b)`
pattern, knows the complete per-colour and per-vertex profile, and knows the first admissible order is
`n = 13` — **but it had never exhibited a single Steiner triple system, so there was nothing for a
construction to start from and no way to attack `Main.extremal_at_thirteen_is_open`.**  New file
`lean/JSPProblem/Block.lean` (325 lines, 18 declarations, zero placeholders, on the default build
path).

### 1. §1 — the census of a Steiner triple system (the family side)

The double count of "pairs inside blocks", which `Rigidity.sum_card_filter_pairIn` performs for the
two-edge paths of a *colouring*, performed here for the blocks alone:

* **`card_edgeFinset_univ_eq_three_mul_card` — `|E(K_n)| = 3 * |B|`** for every `B` with `IsSTS B`;
* **`six_mul_card_eq` — `6 * |B| = n * (n - 1)`**, i.e. a Steiner triple system of order `n` has
  exactly `n(n-1)/6` blocks — the number `Cherry.three_mul_paths_le_edges` forces an extremal
  colouring to reach *exactly* and which arXiv:2207.02920 builds up to `o(n²)` by random triangle
  removal (`six_mul_card_eq_real` is the same over `ℝ`);
* **`sts_three_dvd` — `3 ∣ n * (n - 1)`**, so no Steiner triple system exists for `n ≡ 2, 5 (mod 6)`.
  With `Rigidity.tight_mod6` (extremality forces `n ≡ 1 (mod 6)`) this is the **construction-side
  congruence obstruction**: the `(2,1)`-block construction reaches `5(n-1)/6` only on the residue
  class on which that number is an integer at all.

### 2. §2 — **THE FIRST EXPLICIT STEINER TRIPLE SYSTEM IN THIS DEVELOPMENT**

`B13` is the **cyclic** Steiner triple system of order `13`: the two base blocks `{0,1,4}` and
`{0,2,7}` developed by translation in `Z₁₃` (`fin13`, `sts13Block`, `B13`).

* **`card_B13` — exactly `26 = 13 · 12 / 6` blocks** (`native_decide`);
* **`card_filter_B13` — every one of the `78` pairs of `K₁₃` lies in EXACTLY ONE block**
  (`native_decide`; this is the decidable form of `IsSTS`, there being no `Decidable` instance for
  `∃!`);
* **`card_block_B13`** (`native_decide`) and **`IsSTS_B13`** — so `B13` is a decomposition of the `78`
  edges of `K₁₃` into `26` triangles: **exactly the object `Rigidity.tight_pathFinset_is_STS` demands
  of an extremal colouring of `K₁₃`, now written down and machine-certified**;
* `six_mul_card_B13`, `census_B13`, `first_instance_of_sharp_constant` (`6 · 10 = 5 · 12`, `|B13| = 26`)
  — the first non-trivial instance of the sharp constant as a single numerical statement.

### 3. §3 — **THE DECOMPOSITION FAMILY IS QUANTISED**

For a colouring whose two-edge paths decompose `K_n` (i.e. whose paths are a Steiner triple system),
`Surplus.global_identity` specialises to an exact price formula, and the price is quantised:

* **`decomposition_eq` — `n * k = 5 * Paths c + Isolated c`**: the counting argument pays exactly five
  colour-slots per triangle of the decomposition and nothing else.  This is the construction-side
  price formula (`k = 5(n-1)/6 + Isolated c / n`), i.e. what arXiv:2207.02920 §12 pays for the
  uncoloured leftover edges;
* **`decomposition_isolated_dvd` — `Isolated c = n * t` when `n ≡ 1 (mod 6)`**: the missed
  `(vertex, colour)` incidences come in **whole colours** — losing one costs a full colour's worth of
  coverage;
* **`decomposition_gap` — `6k = 5(n-1)` OR `5(n-1) + 6 ≤ 6k`**: **the `(2,1)`-block family has no
  surplus in between**, it either attains the counting bound exactly or wastes at least one colour;
* **`decomposition_gap_at_thirteen`** — the same at the first possible order: a decomposition
  colouring of `K₁₃` uses **exactly `10` colours, or at least `11`**.

### 4. The search that was run in parallel (`sts_search.c`, `sts_mc.c`, `sts_mc2.c`, `sts_polish.c`)

An admissible 10-colouring of `K₁₃` must be a `(2,1)`-block colouring of **some** STS(13): that is
`Rigidity.tight_pathFinset_is_STS` at `n = 13`.  So the finite question "does `K₁₃` admit an
admissible 10-colouring?" reduces, within a fixed STS, to a `26 × 300` table (per block: which of the
three vertices is the centre, and which two distinct colours).  Three engines were written
(`discovery/JSP-000140/sts_{search,mc,mc2,polish}.c`: min-conflicts with simulated annealing, weighted
min-conflicts, steepest descent, iterated local search on the exact objective "number of violated
four-sets") and run for ≈ 40 CPU-minutes on the cyclic `B13`.

* **No admissible `(2,1)`-block colouring was found.  The best state reached violates 16 of the 715
  four-sets of `K₁₃`** (min-conflicts alone reaches `bad = 1` occasionally, i.e. a single violated
  four-set, but never 0).  This is the **first quantitative statement about B5 in the shape the
  rigidity theorem forces**; it is evidence, not a proof.
* Only the **cyclic** STS(13) was searched; there are 10 isomorphism classes and the other 9 are
  untouched.

### 5. What this costs the prize, stated honestly

The prize hypothesis `Partial.FamGreedyFamily` (a near-perfect matching in the auxiliary hypergraph, a
sparse leftover, the two four-set conditions, `6(k+2D+1) ≤ 5(m-1)+δm`) is **untouched**: it is a
Rödl-nibble / random-triangle-removal existence theorem and Mathlib contains neither.  What round 49
changes is the *starting material* for the construction side: the combinatorial object the paper
builds by random triangle removal — a decomposition of `E(K_n)` into `n(n-1)/6` triangles — now
exists in the development as certified data (`B13`), its census is proved on the family side, and the
`(2,1)`-block colouring built on such a decomposition is priced exactly and shown to be quantised.
`jsp_000140_main` was again **not** declared; B5, `pairFree_of_admissible`, B4 (`f(10,4,5) ∈ {8,9}`)
— unchanged.

### 6. Abandoned / not done this round

* **The `(2,1)`-block colouring is still not written down as Lean data.**  The theorem that would
  make the census constructive — `Paths (blockCol B ctr pc qc) = |B|` for a `(2,1)`-block colouring
  of a decomposition — was drafted and *not* proved: it needs `(nb c i v univ).card ≤ 2` from
  `Admissible` (from `Definitions.classIn_card_le_two` + `Definitions.card_ge_three`) and then a
  `Sym2`-level case analysis showing that the two colour-`i` edges at a centre lie in **one** block
  (two different blocks would put three colour-`i` edges in one four-set).  Recorded in
  `policy.json.next_round_plan` step 3, with the two ingredients in the order they must be done;
* **only 1 of the 10 STS(13) isomorphism classes was searched**; the other 9 are the obvious next
  attempt (`policy.json.next_round_plan` step 1), and a success would give `EG 13 = 10`, the first
  attainment of the sharp constant `5/6` beyond `n = 6`, closing
  `Main.extremal_at_thirteen_is_open`;
* the STS census for `n` **odd** (`2 · |blocks through `v`| = n - 1`, hence `n ≡ 1, 3 (mod 6)`) was
  drafted and cut — a second `Finset.sum_comm` at the `(pair, block)` level, not needed this round;
* **cost note for the next round**: `Block.lean` compiles in ≈ 40 s (the `native_decide` calls over the
  `715` four-sets' worth of pair arithmetic dominate); `Amplify.lean` still costs ≈ 150 s and
  `Seven.lean` ≈ 50 min of `native_decide` — both were **not** touched, and the whole incremental
  build was 21 s.  Keep new material in new files.

## Status (round 48)

`lake build`: **OK** (3136 jobs).  `sorry`/`admit`: **0** (`placeholder_total = 0`).
`harness/score.py --strict-prize` (invoked on `problems/JSP-000140/lean`):
`build_ok = true`, `partial_ok = true`, `prize_ready = false`,
`missing_theorems = ["jsp_000140_main"]`.

**ROUND 48 REPLACES THE MECHANISM OF THE BLOW-UP OBSTRUCTION — AND THEREBY *FINDS* AN ADMISSIBLE
BLOW-UP, AT A PALETTE STRICTLY ABOVE THE BUDGET.**  Round 47 killed the lexicographic-product route
to `5n/6` for the palette `Fin q × Fin m` (`q·m = 5·(6m)/6` colours on `6m` vertices — exactly the
catalog budget).  Its proof needed `y ↦ L i₀ j x₀ y : Fin m → Fin m` to be **surjective**, which it
got from injectivity *at equal cardinalities*.  The moment the palette is `Fin q × Fin r` with
`r ≠ m` — which is precisely the regime a budget-respecting construction would use, since a
*cheaper* palette means `r < m` — that step is unavailable, and round 47's argument simply does not
apply.  New file `lean/JSPProblem/Amplify.lean` (548 lines, 34 declarations, zero placeholders, on
the default build path) redoes the obstruction **without** any surjectivity step, refutes the whole
budget range, and then exhibits an admissible blow-up just above it.  The family is now pinned down
exactly.

### 1. §1–§2 — the blow-up with an *arbitrary* cross-index space

`blockColR` / `blockColRT` (palette `Fin (q * r)`, cross-index space `Fin r` completely free),
`blockColR_swap`, `blockColRT_same`, `blockColRT_cross`.  `xrange L i j x` is **the set of cross
indices the `m` edges out of the inner vertex `x` of block `i` to block `j` receive**; `mem_xrange`,
`card_xrange` (`= m`, from injectivity), `card_xrange_le` (`≤ r`), and

* **`m_le_r_of_hinj`** — **injectivity of the cross labelling already forces `m ≤ r`**: `Fin m`
  injects into `Fin r`.  So the palette `q·r` of this shape is *never* smaller than `q·m`, and the
  catalog budget `q·r ≤ q·m` leaves no choice at all — it means `r = m`.

### 2. §3 — **THE INDEX-AVOIDANCE THEOREM** (the new mechanism)

* **`bad_fourSet`** — **the bad `K₄`, exhibited**: if the internal edge `x₀x₁` of block `i` carries
  the product colour `xcolQ (f i j) l₀` and the cross index `l₀` is realised by `x₀y₁` *and* by
  `x₁y₂`
  with `y₁ ≠ y₂`, then the three edges `x₀x₁`, `x₀y₁`, `x₁y₂` carry the same colour, so
  `{x₀, x₁, y₁, y₂}` spans **at most four** colours.  No surjectivity anywhere;
* **`xrange_avoid`** — **if the product colouring is admissible, then for every block `i`, every
  `j ≠ i`, every internal edge `x₀x₁` whose colour is `xcolQ (f i j) l₀`, and every `x₀ ≠ x₁`, the
  index `l₀` is missed by the cross edges of `x₀` or by those of `x₁`.**  The hypotheses are only:
  symmetry of `f` and `L`, the 1-factorisation covering property `hcover`, and injectivity of `L`
  in its first inner variable — exactly as in round 47, but **the statement holds at every palette
  `Fin (q·r)`, with no relation between `m` and `r`**.

### 3. §4 — **THE BUDGET IS EXACTLY THE POINT AT WHICH THE FAMILY DIES**

* **`xrange_eq_univ_of_le`** — if `r ≤ m` the cross-index set of an inner vertex has `m = r` elements
  inside `Fin r`, i.e. it is **all of `Fin r`**: a cross-index space within the budget hides
  nothing, and every colour index is hit from every inner vertex;
* **`blockColRT_not_admissible_of_budget`** — hence for `r ≤ m` a bad `K₄` always exists.  (Round 47
  proved only `r = m`, and by a different mechanism: injectivity + equal cardinality ⟹ surjectivity.)
* **`r_gt_m_of_admissible` / `r_ge_succ_of_admissible` / `palette_ge_succ_of_admissible`** — the sharp
  quantitative form: **an admissible blow-up needs a *strictly* larger cross-index space than the
  block, i.e. a palette of at least `q·(m+1) = q·m + q` colours.**  With the `K₆` factor and `q = 5`
  this exceeds the counting bound `5m ≤ f(6m,4,5)` (`Product.EG_ge_five_mul_six`) by five colours,
  so the blow-up route misses the counting bound and therefore `5n/6`;
* **`no_amplify_K6_within_budget`** — the budget case for the `K₆` witness, quantified over the
  palette.

### 4. §5 — **… AND THE FAMILY IS NOT DEAD, ONLY WASTEFUL: THE FIRST ADMISSIBLE BLOW-UP IN THIS
DEVELOPMENT**

`Lblk6` labels the cross edges of a `K₆`-by-`K₂` blow-up by the (block-ordering of the) pair of
inner indices, so the four cross edges between two blocks get the four cross indices `0, 1, 2, 3`
(`Lblk6_symm`, `Lblk6_inj`, `Lblk6_inj'`, `Lblk6_lt_four`, all `native_decide`); `psi6` gives the
single internal edge of block `i` the product colour with factor `i mod 5` and cross index `4 + i`,
which no cross edge ever carries.

* **`admissible_blowup_K6_m2`** — **an admissible edge colouring of `K₁₂` with `50 = 5 · 10` colours
  which is a lexicographic blow-up of the `K₆` witness `Product.fact6Col`** (`native_decide` over the
  `C(12,4) = 495` four-sets, ≈ 2.5 min);
* `EG_le_fifty_blowup` (`EG 12 ≤ 50`), `counting_bound_at_twelve` (`⌈5·11/6⌉ = 10`).

So the answer to "can the blow-up reach `5n/6`?" is now a theorem in both directions: **no at the
budget (`palette_ge_succ_of_admissible`), and yes strictly above it (`admissible_blowup_K6_m2`) —
at a factor of five.**  The mechanism of the failure is exactly one unit of cross-index space.

### 5. §6 — a blow-up is only as good as the colourings inside its blocks

`encInj`, `restrictCol_block` (restricting the blow-up to one block returns the internal colouring),
`colorsOn_block`, **`Admissible_block`** (**an admissible blow-up forces every internal colouring to
be admissible**) and `EG_le_palette_of_admissible` (`f(m,4,5) ≤ q·r`).  A lexicographic product is
never better than the colourings it is built from, so `K₂`-blocks — the only block size at which an
admissible blow-up was exhibited — cannot be iterated to reach `5n/6`.

### 6. What this costs the prize, stated honestly

The prize hypothesis `Partial.FamGreedyFamily` (a near-perfect matching in the auxiliary hypergraph,
a sparse leftover, the two four-set conditions, `6(k+2D+1) ≤ 5(m-1)+δm`) is **untouched**: it is a
Rödl-nibble / random-triangle-removal existence theorem and Mathlib contains neither.  What round 48
changes is the state of the *construction* side: the lexicographic-product family is no longer
"refuted at the budget but otherwise unexplored", it is **settled** — one theorem says an admissible
blow-up needs ≥ `q(m+1)` colours, one theorem says an admissible blow-up exists at `5·10` for
`K₆→K₂`, and a third says any admissible blow-up's blocks must themselves be admissible.  A
non-product family (with genuinely different colour classes in different blocks) must exist, and
none is known.  `jsp_000140_main` was again **not** declared.  `pairFree_of_admissible`; B4
(`f(10,4,5) ∈ {8,9}`) and B5 (`EG 13 ∈ {10,11}`) — unchanged.

### 7. Abandoned / not done this round

* **The general statement `blockColRT_not_admissible` for arbitrary `r` is FALSE and was deleted.**
  It was drafted from the mistaken belief that an injective `Fin m → Fin r` is surjective when
  `m ≤ r` (it is: `m = r`; injectivity forces `m ≤ r`, surjectivity forces `r ≤ m`).  With `r > m`
  the family is admissible — see §5 — and the Python check that revealed this is recorded in
  `discovery/JSP-000140/blowup_threshold.py` (reproduce: 495 four-sets, 0 violations);
* blow-ups by blocks `K_m` with `m ≥ 3` are not attempted: a `3+1` split puts a `K₃` inside one block,
  and a monochromatic triangle there would leave the four-set with only four colours, so the internal
  colourings would have to be triangle-free in every colour class — a genuinely harder design
  question, recorded as `next_lemma`;
* iterated blow-ups (`K₆` blown up by `K₂` and then again) are not attempted: it needs a *covering*
  factor map on `K₁₂` with 50 colours, which the `K₂` blow-up does not supply;
* round 45's census obstruction stays cancelled (its margin is negative only at `(7,6)` and `(8,6)`,
  both settled by search);
* **Cost note for the next round**: `JSPProblem/Amplify.lean` costs **≈ 150 s** of `native_decide`
  (the 495 four-sets of `K₁₂` dominate; the `Lblk6` facts are instant).  `Seven.lean` (≈ 50 min) was
  not touched and its `.olean` was reused.  Keep new material in new files.

## Status (round 47)

`lake build`: **OK** (3135 jobs).  `sorry`/`admit`: **0** (`placeholder_total = 0`).
`harness/score.py --strict-prize` (invoked on `problems/JSP-000140/lean`):
`build_ok = true`, `partial_ok = true`, `prize_ready = false`,
`missing_theorems = ["jsp_000140_main"]`.

**ROUND 47 CHANGES ATTACK FAMILY: THE *BLOW-UP* (LEXICOGRAPHIC PRODUCT) ROUTE TO `5n/6` — AND KILLS
IT IN FULL GENERALITY.**  `Tables.EG_six : EG 6 = 5` is the **only** order of this development at
which the catalog constant `5/6` is attained (`5 = 5·6/6`; `EG 7 = 7`, `EG 8 = 7` both miss it), so
the most tempting route to the missing upper bound `f(n,4,5) ≤ 5n/6 + o(n)` is to **amplify that one
witness**: blow `K₆` up `m` times into `6` blocks of `m` inner vertices, colour inside each block
arbitrarily, and colour across two blocks by the pair *(factor colour of the two blocks, cross index
of the two inner vertices)*.  The palette is `Fin 5 × Fin m`, i.e. **`5m = 5·(6m)/6` colours on `6m`
vertices — exactly the catalog budget, at every blow-up size.**  New file
`lean/JSPProblem/Product.lean` (431 lines, 28 declarations, zero placeholders, on the default build
path).

### 1. §1 — the blow-up as data

`encT` / `blkT` / `innT` (`Fin t × Fin m` encoded in `Fin (t·m)`, with `encT_inj_inner`,
`encT_inj_block`, `blkT_encT`, `innT_encT`); `xcolQ` / `xcolQDec` / `xcolQDec_xcolQ` /
**`exists_xcolQ`** (every colour of the palette splits *uniquely* into a block colour and a cross
index); `blockCol` (the colour of an **ordered** pair), **`blockCol_swap`** (it is a function of the
unordered pair — the statement that `f` and `L` are symmetric), `blockColT` (the colouring),
`blockColT_same` / `blockColT_cross` (the colour inside a block / across two blocks).

### 2. §2 — **THE PRODUCT OBSTRUCTION**

* **`blockCol_not_admissible` — NO LEXICOGRAPHIC PRODUCT COLOURING OF THIS SHAPE IS EVER
  ADMISSIBLE.**  For **any** number of blocks `t`, **any** number of factor colours `q`, **any**
  blow-up size `m ≥ 2`, **any** internal colourings `psi` and **any** symmetric cross labelling `L`
  injective in its first inner variable, the product colouring fails `Admissible` — the only
  hypothesis on the construction is `hcover`, that *the factor map covers every colour at every
  block* (the 1-factorisation property).  The bad `K₄` is exhibited: take two inner vertices
  `x₀ ≠ x₁` of a block `i₀`, split the colour of `x₀x₁` as `(a, l)`, choose a block `j ≠ i₀` with
  `f i₀ j = a`, and choose `y₁ ≠ y₂` in block `j` with `L i₀ j x₀ y₁ = L i₀ j x₁ y₂ = l` (possible
  because `y ↦ L i₀ j x₁ y` is injective on `Fin m`, hence onto).  Then the three edges
  `x₀x₁`, `x₀y₁`, `x₁y₂` all carry the **same** colour, so `Definitions.colorsOn_card_le_four`
  bounds that `K₄` by **four** colours while `Admissible` demands five.
* §2* `fin_add_comm` (the cross labelling `x + y` is symmetric) and `fin_add_inj` (`x ↦ x + y` is
  injective, via `Nat.ModEq.add_right_cancel` then `Nat.ModEq.eq_of_lt_of_lt`) — the canonical
  labelling.

### 3. §3 — the witness is fine; the blow-up is not

* `fact6Col` / `fact6` — the 1-factorisation `01|23|45`, `02|14|35`, `03|15|24`, `04|13|25`,
  `05|12|34`, as a colouring and as a factor map `Fin 6 → Fin 6 → Fin 5`;
* **`admissible_fact6Col`** — it *is* admissible (`native_decide` over the `C(6,4) = 15` four-sets): a
  second explicit admissible 5-colouring of `K₆`, independent of `Tables.sixCol`;
* `fact6_symm`, **`fact6_cover`** — symmetry and the covering property (`native_decide`);
* **`blowup_K6_not_admissible`** — **THE `K₆` WITNESS CANNOT BE AMPLIFIED**: for every `m ≥ 2` and
  every family of internal colourings, the blow-up of `K₆` along the 1-factorisation with the cross
  labelling `x + y` is not admissible.  `m ≥ 2` is used nowhere else, so the family starts at the
  right place (`m = 1` is the known witness) and dies immediately;
* **`EG_ge_five_mul_six`** — the blow-up palette `5m` is *exactly* the catalog counting bound
  `5(n-1)/6`, rounded up: `5m ≤ f(6m,4,5)`; **`EG_eq_five_mul`** — so a single admissible
  `5m`-colouring of `K_{6m}` would settle `f(6m,4,5) = 5m`, and §2 says the product family can never
  supply one;
* `blowup_K6_instance` — a `native_decide` certificate of one bad four-set `{0,1,3,4}` of `K₁₈` at
  blow-up size `3`, independent of the general argument.

### 4. What this costs the prize, stated honestly

The prize hypothesis `Partial.FamGreedyFamily` (a near-perfect matching in the auxiliary hypergraph,
a sparse leftover, the two four-set conditions, `6(k+2D+1) ≤ 5(m-1)+δm`) is **untouched**: it is a
Rödl-nibble / random-triangle-removal existence theorem and Mathlib contains neither.  What round 47
adds is a *negative* result with real content: **the cheapest way to obtain the upper bound — amplify
the one extremal small witness — is impossible**, in full generality, and this is the first time the
development has said anything about *asymptotic* construction families rather than about single
values of `f`.  A non-product family must exist, and none is known.  `jsp_000140_main` was again
**not** declared.  `pairFree_of_admissible`; B4 (`f(10,4,5) ∈ {8,9}`) and B5 (`EG 13 ∈ {10,11}`) —
unchanged.

### 5. Abandoned / not done this round

* The **budget-level** generalisation of the obstruction (cross-index space `Fin r` with `r ≤ m`,
  palette `Fin (q·r)`) is **not** proved; it is `policy.json.next_lemma`, and it is the statement that
  would close the whole amplification route in one theorem (`q·r ≤ q·m ⟹ r ≤ m`, and an injective
  `Fin m → Fin r` with `r ≤ m` is a bijection onto its image).
* Non-product amplification families (merging blocks rather than colouring them independently) are
  untouched.
* Round 45's census obstruction stays cancelled (its margin is negative only at `(7,6)` and `(8,6)`,
  both settled by search).
* **Cost note for the next round**: `JSPProblem/Seven.lean` costs ≈ 50 minutes of `native_decide`; it
  was **not** touched in round 47 and its `.olean` was reused — the whole incremental build took
  31 s.  `Product.lean` itself costs ≈ 10 s of `native_decide` (the 15 four-sets of `K₆` and the 18
  edges of `K₁₈`).  Keep new material in new files.

## Status (round 46)

`lake build`: **OK** (3134 jobs).  `sorry`/`admit`: **0** (`placeholder_total = 0`).
`harness/score.py --strict-prize` (invoked on `problems/JSP-000140/lean`):
`build_ok = true`, `partial_ok = true`, `prize_ready = false`,
`missing_theorems = ["jsp_000140_main"]`.

**ROUND 46 CLOSES BLOCKER B2 OF ROUND 19 — THE LAST STATEMENT THAT ROUND LEFT OPEN — BY ACTUALLY
RUNNING THE THIRD SEARCH OF THIS DEVELOPMENT AT `n = 7`.**  New file
`lean/JSPProblem/Seven.lean` (11 declarations, zero placeholders, on the default build path).

### 1. The two certificates

`FastSearch.lean` (round 19) built a *third* exhaustive engine for `f(n,4,5)`: `searchAuxSg`,
a depth-first search over the edge slots of `K_n` which prunes each branch as soon as one of the
`K₄`s completed by the slot being filled fails the catalog condition, branches only over the
colours **in order of first occurrence** (the colour-permutation symmetry reduction), and
enumerates the `K₄`s of every slot **once** in the table `fourGroupsS`.  Its **completeness
theorem** `searchAuxSg_iff` and its **lower-bound engine** `EG_ge_of_certG` were proved in round 19,
but the only certificates ever discharged for it were `certG_six_four` (`K₆`, four colours) and
`certG_five_three` (`K₅`, three colours) — the two statements the *first* search (`Search.lean`)
had already settled.  The certificate that mattered, `hasAdmissibleSymG 7 5 = false`, was left as
**blocker B2** for 27 rounds because it had never been run inside Lean.

* **`certG_seven_five : hasAdmissibleSymG 7 5 = false`** — about **50 minutes** of
  `native_decide` (≈ 1.3 · 10⁷ search nodes; the same statement takes seconds in optimised C and
  about 10⁴ × that in the interpreted Python model `discovery/JSP-000140/eg3_symmetry_nodes2.py`).
  Since the completeness of the program is the *proved* theorem `searchAuxSg_iff`, the `false`
  answer means what it says.
* **`certG_seven_seven : hasAdmissibleSymG 7 6 = true`** — about **80 seconds**; the same engine
  *finds* an admissible seven-colouring (the round-robin colouring `c({a,b}) = a + b` after the
  symmetry reduction has relabelled it).

### 2. What follows, in the catalog language

* **`no_admissible_six_of_seven : ¬ ∃ c : Col 7 6, Admissible c`** — no admissible six-colouring of
  `K₇` exists, with no witness to read and no search in the proof;
* **`no_admissible_at_most_six_of_seven`** — the strengthened form: `K₇` genuinely needs **all
  seven** of its colours (`Search.admissible_liftCol`);
* **`EG_seven_ge_g`**, **`EG_seven_le_g`**, **`EG_seven_g`** — `f(7,4,5) ≥ 7`, `≤ 7`, hence
  `f(7,4,5) = 7`: the value is **decided by this single engine on both sides**, so
  `searchAuxSg_iff` is exercised on a `true` *and* on a `false` answer at the same order;
* **`EG_seven_by_g`** — the same value with **no search at all** on the upper-bound side
  (`Construction.EG_le_sumCol 7`), so the two derivations are independent;
* **`counting_bound_missed_by_two_at_seven`** — `⌈5(7-1)/6⌉ = 5` while `f(7,4,5) = 7`: at `n = 7`
  the sharp constant `5/6` of the catalog answer misses by **two** colours, although it is attained
  for every `n ≤ 6` (`Tables.EG_six`);
* **`three_engines_agree_at_seven`**, **`EG_seven_decided`** — the three searches of this
  development (`Search.lean`, `FastSearch.lean`, `VertexSearch.lean`) are three independent programs
  with three independently proved completeness theorems, and all three certify `f(7,4,5) = 7`.

### 3. Limits, stated honestly

`EG 7 = 7` was **already** known in this development (`Main.EG_seven` from the vertex-addition
search, `Main.EG_seven_leaffree` from the leaf-free search), so this round adds a third independent
derivation rather than a new value of `f`; the substantive gain is the closure of B2 and the fact
that `searchAuxSg_iff` is now validated at the hardest order.  `n = 8` is out of reach of this
engine (`> 7.5 · 10⁷` nodes in 900 s of Python) and is settled instead by
`VertexSearch.certC_eight_six`; `n = 9` needs the leaf-free engine (`Nine.certD_nine_six`,
≈ 80 min, deliberately kept off the default build path).  **No new value of `f(n,4,5)` was found
this round** and the prize hypothesis `Partial.FamGreedyFamily` is untouched.

### 4. Abandoned this round (recorded so the next round does not repeat it)

* **The census obstruction of round 45 was NOT ported to Lean**, and this was a deliberate
  decision, not an accident.  Its full content is `|twoFourSets c i| = choose |E_i| 2 + (n-4) ·
  (twoA c i).card`, which needs three `Finset.card_bij` bijections at the `Sym2` level (ordered
  adjacent pairs ↔ twice the centres; ordered disjoint pairs ↔ twice the four-sets with a disjoint
  doubled pair; `(path, extra vertex) ↔ four-sets with an adjacent doubled pair`), and the first of
  them cannot be obtained without the identity `|tri c i| = |twoA c i|`.  The *arithmetic* half of
  that identity is cheap (`|pathTrip c i| = ∑_v deg_i(v)·(deg_i(v)-1) = 2·|twoA c i|` follows from
  `deg_i v ≤ 2` with no `Sym2` case analysis), and the Sym2 half is the expensive one.
  **And the payoff would be nil**: re-reading `discovery/JSP-000140/census_feasibility.py`, the
  obstruction's margin is negative only at `(n,k) = (7,6)` and `(8,6)` — both of which this
  development already settles by search (`Main.EG_seven`, `Main.EG_eight`) — and positive for every
  `n ≥ 9`.  It refutes nothing new.
* Asymptotically the census obstruction is worthless anyway (`∑_i choose |E_i| 2 ≳ n⁴/(8k)` forces
  only `k ≥ 3`), so it cannot move the prize.
* **Cost note for the next round**: `JSPProblem/Seven.lean` now costs **≈ 50 minutes of
  `native_decide`**; touching it (or any file that changes its import trace) repays that.  Do not
  edit `Seven.lean` casually.

## Status (round 45)

`lake build`: **OK** (3133 jobs).  `sorry`/`admit`: **0** (`placeholder_total = 0`).
`harness/score.py --strict-prize` (invoked on `problems/JSP-000140/lean`):
`build_ok = true`, `partial_ok = true`, `prize_ready = false`,
`missing_theorems = ["jsp_000140_main"]`.

**ROUND 45 CHANGES ATTACK FAMILY: THE `K₄` SIDE OF THE CATALOG CONDITION INSTEAD OF THE EDGE
SIDE.**  Rounds 37–44 all looked at a colouring through its **edges** (the two-edge-path counting,
the slot counting, the auxiliary hypergraph `H`, the exact surplus identity).  This round looks at
it through its **four-vertex cliques**, and finds there an obstruction that the edge side cannot see.
New file `lean/JSPProblem/Census.lean` (309 lines, 23 declarations, zero placeholders).

### 1. §1 — **THE 5-OR-6 DICHOTOMY**

`Definitions.classIn_card_le_two` (*no four vertices carry three edges of one colour*) has, until now,
been used only locally.  Read globally, together with the fact that the colour classes partition
`E(K_S)`, it says that the only admissible multiplicity patterns of the six edges of a `K₄` are
`(2,1,1,1,1)` and `(1,1,1,1,1,1)`.  With `doubledIn c S` = the colours occurring **twice** on `S`:

* **`card_colorsOn_add_doubledIn`** — the exact form, **for every four-element `S`**
  `|colorsOn c S| + |doubledIn c S| = 6`;
* **`card_doubledIn_le_one`** — **A `K₄` HAS AT MOST ONE DOUBLED COLOUR** (so the pattern
  `(2,2,1,1)`, i.e. four colours, is impossible — this is where the whole `≥ 5` of the catalog
  condition enters the census);
* **`card_colorsOn_four_five_or_six`** — **EVERY FOUR-SET OF AN ADMISSIBLE COLOURING SPANS EXACTLY
  FIVE OR SIX COLOURS**;
* `card_colorsOn_four_eq_six_iff`, `card_colorsOn_four_eq_five_iff` (rainbow ↔ no doubled colour;
  five colours ↔ exactly one doubled colour); `classIn_card_mem_colorsOn`,
  `mem_colorsOn_of_card_pos`, `sum_card_classIn_colors`, `twoFourSets c i`, `fiveFourSets c`.

### 2. §2 — the counting tools the census needs

`edgePairs` / `mem_edgePairs` / **`card_edgePairs`** (the ordered pairs of distinct members of a
finset) and **`two_mul_choose_two`** (`2 * choose m 2 = m * (m - 1)`), plus `sum_const_card_nat`.

### 3. §3 — **A NEW OBSTRACTION, MACHINE-CHECKED: THE CENSUS OBSTRUSION** (not yet in Lean)

Counting the `K₄`s in which a colour is doubled, in two ways, gives the **exact per-colour census**

    `|twoFourSets c i|  =  choose |E_i| 2  +  (n - 4) * (twoA c i).card`

(one for every unordered pair of colour-`i` edges — a *disjoint* pair determines its `K₄` uniquely,
an *adjacent* pair, i.e. a two-edge path, lies in `n-3` of them), and therefore

    **THE CENSUS OBSTRUSION**   `choose n 4  ≥  ∑_i choose |E_i| 2  +  (n - 4) * Paths c`,

a new necessary condition on the colour-class profile.  It is *not* a consequence of
`Surplus.surplus_identity`, which knows only `∑_i |E_i|`, `Paths c` and `Isolated c`.

**Findings** (`discovery/JSP-000140/census_feasibility.py`, a DP over the colour-class profiles, exact):

| `(n, k)` | margin `choose n 4 − (obstruction LHS)` | verdict |
| --- | --- | --- |
| `(6, 5)` | **0** | the known admissible `K₆`/5 witness **saturates** the obstruction |
| `(7, 6)` | −1 | **refuted** |
| `(8, 6)` | −14 | **refuted** |
| `(9, 7)`, `(10, 8)` | +6, +45 | not refuted |
| `(13, 10)` | +215 | not refuted — the obstruction does not touch B5 |

The `(6,5)` row is the sanity check that the obstruction is correct: the explicit 5-colouring of `K₆`
(`Tables.sixCol`, whose `Isolated = 0`, `Defect = 15`, `Paths = 0` are computed in round 44) has
`∑_i choose 3 2 = 15 = choose 6 4` exactly.

Combining with two per-colour arithmetic facts about the profile `(a,b,z) = (twoA, oneB, zeroA)`
(both `native_decide`-able, `3a + 2b + z` replaced by `a + b + z = n` and `2|E_i| = 2a + b`):

* `choose |E_i| 2 + 3 z ≥ 6` for every profile of `K₇`,
* `choose |E_i| 2 + 4 a + 42 ≥ 12 |E_i|` for every profile of `K₈`,

the obstruction **refutes an admissible six-colouring of `K₇` and of `K₈`**, hence (with
`Construction.EG_le_sumCol` and `Main.EG_le_ghost_sub`)

    **`EG 7 = 7`   and   `EG 8 = 7`**.

This is the **first improvement of the catalog counting bound `f(n,4,5) ≥ 5(n-1)/6` obtained in this
development**: at `n = 7` and `n = 8` the counting bound gives only `≥ 6`.  It is also a *finite*
statement, i.e. unlike the first-stage existence it is closeable in Lean.

### 4. NOT proved this round — the exact blocker

**Section 3 of `Census.lean` is proved in Python but NOT yet in Lean.**  Four helper lemmas were
drafted and all four failed to compile inside this round's budget, so they were cut out of the file
to keep the build green: `exists_mk_of_mem` / `toFinset_inj` / `exists_common_centre` (turning a
vertex of a `Sym2` into `s(v, a)`) and `card_fourSets_through_three` / `card_fourSets_through_four`
(the number of `K₄`s through a three- resp. four-vertex set is `n-3` resp. `1`).  The root cause is the
`Sym2` representation: `Sym2` has **no** coercion to `Finset` (`Sym2.toFinset` is a `def` through
`Multiset`), `x ∈ z` for `z : Sym2` is *not* a `Membership` (only `Sym2.mem_toFinset` is, and it is
an `Iff`), and `Finset.eq_empty_iff_forall_not_mem`, `Finset.card_pos_iff`, `Finset.Nonempty.some`,
`Finset.card_le_antisymm`, `Nat.choose_succ` and `Nat.sub_mul` **do not exist** in this Mathlib/batteries
version.  Every failing `rw`/`rcases` and the working substitutes are written out in
`discovery/JSP-000140/policy.json.next_lemma`, in the order they must be done.

The prize itself is unchanged: `FiveSixth EG` for all large `n` still needs the construction of
arXiv:2207.02920 / arXiv:2208.12563, i.e. a Rödl-nibble / differential-equation / random-triangle-removal
existence theorem, and Mathlib has none of them.  `jsp_000140_main` was again **not** declared.
`pairFree_of_admissible`; B4 (`f(10,4,5) ∈ {8,9}`, which the round-14 notes already make a
corollary of `EG_ge_ceil_five_sixth` + `Tables.EG_ten_le`) and B5 (`K₁₃` with ten colours) —
unchanged.

## Status (round 44)

`lake build`: **OK** (3132 jobs).  `sorry`/`admit`: **0** (`placeholder_total = 0`).
`harness/score.py --strict-prize` (invoked on `problems/JSP-000140/lean`):
`build_ok = true`, `partial_ok = true`, `prize_ready = false`,
`missing_theorems = ["jsp_000140_main"]`.

**ROUND 44 REPLACES THE `5/6` COUNTING *INEQUALITY* BY AN EXACT *IDENTITY*, AND READS OFF THE
DEFECT BUDGET THE MISSING CONSTRUCTION HAS TO PAY — AND, WITH IT, A NEW *CONSTRUCTION* FAMILY
(1-FACTORISATION + MERGING) WHICH WAS TESTED AND IS REFUTED AT THE COUNTING BOUND.**
New file `lean/JSPProblem/Surplus.lean` (542 lines, 37 declarations, zero placeholders).

### 1. §1 — the two defects of a colouring

* **`zeroA c i` / `Isolated c`** — DEFECT I: the number of `(vertex, colour)` incidences on which the
  colour does not occur at all (neither a two-edge-path centre `Counting.twoA` nor a single-edge
  vertex `Counting.oneB`);
* **`Defect c = |E(K_n)| - 3 · Paths c`** — DEFECT II: the edges of `K_n` that **no two-edge path pays
  for** (each path brings three edges with it and these triples are pairwise disjoint,
  `Cherry.cherryEdges_disjoint`);
* **`card_twoA_oneB_zeroA`** — THE THREE DEGREE CLASSES OF A COLOUR CLASS PARTITION THE VERTICES,
  `|twoA| + |oneB| + |zeroA| = n`: the exact form of `Paths.twoA_oneB_card_le` (which recorded only
  `≤ n`);
* **`two_mul_classIn_eq`** — **THE EXACT PER-COLOUR COUNTING IDENTITY `2·|E_i| = n + p - z`**, where
  `p` is the number of two-edge-path centres of the colour and `z` the number of vertices it misses:
  the sharp form of `Paths.two_mul_classIn_le_add` (`2|E_i| ≤ n + p`), which kept the `+p` and
  *discarded the `-z`*;
* **`sum_classIn_add_isolated` / `global_identity`** — `2·|E(K_n)| + Isolated c = n·k + Paths c`, i.e.
  `n(n-1) + Isolated c = n·k + Paths c`: `Paths.mul_n_sub_one_le` with the missed vertices added back.

### 2. §2 — **THE EXACT SURPLUS IDENTITY** (`surplus_identity`)

    `6 * (n * k) = 5 * n * (n - 1) + 6 * Isolated c + 2 * Defect c`

for every admissible colouring and `n ≥ 4`.  **The number of colours exceeds `5(n-1)/6` by exactly
`Isolated c / n + Defect c / (3n)`, in two integers, with no inequality anywhere**
(`surplus_of_k`: `6·Isolated + 2·Defect = n·(6k - 5(n-1))`).  `Cherry.five_sixth_lower` is the
*shadow* of this equality (`five_sixth_lower_of_surplus`).

### 3. §3 — what it says about extremality, and about what a construction must do

* **`clean_of_extremal` / `extremal_of_clean`** — a colouring is extremal (`6k = 5(n-1)`) **iff** it
  has *no* missed `(vertex, colour)` incidence and *no* unpaid edge.  This is the **converse** to
  `Rigidity.tight_pathFinset_is_STS` and `Main.extremal_no_isolated_vertex`: necessity was known, the
  *sufficiency* — i.e. the certification a construction needs — now is too;
* **`extremal_of_covered_cherries`** — **the design target in one statement**: an admissible colouring
  in which every edge is paid for by a two-edge path and every colour reaches every vertex is
  extremal;
* **`defect_budget`** — **a colouring that pays `r` colours more than `5(n-1)/6` pays at most `r·n`
  in defects**: with the published `6k ≤ 5(n-1) + δn` this is `6·Isolated + 2·Defect ≤ δn²`, i.e. the
  first stage of arXiv:2208.12563 §4 / arXiv:2207.02920 §4 (which leaves `Θ(n^{2-δ})` edges over)
  must leave `o(n²)` *defects*, in the exact currency of the catalog constant `5/6`
  (`isolated_le_of_budget`, `defect_le_of_budget`);
* **`defect_divisible` / `three_mul_isolated_defect_divisible`** — `n ∣ (6·Isolated + 2·Defect)`, and
  for odd `n` also `n ∣ (3·Isolated + Defect)`: a cheap *necessary* condition on the output of any
  construction, checkable before a single four-clique is looked at;
* **`surplus_real` / `EG_surplus_real` / `EG_surplus_exists`** — over `ℝ`, at the optimum:
  `f(n,4,5) = 5(n-1)/6 + (the defects of an optimal colouring)`, so the excess of `f(n,4,5)` over
  `5n/6` *is* the defect price of a colouring witnessing it.

### 4. §4 — the defects of the explicit colourings (`native_decide`)

| witness | `n`, `k` | `Isolated` | `Defect` | `6I + 2D` | `n·(6k-5(n-1))` |
| --- | --- | --- | --- | --- | --- |
| `Tables.sixCol` | 6, 5 | **0** | **15** | 30 | 30 |
| `Tables.nineCol` | 9, 8 | **4** | **24** | 72 | 72 |
| `Tables.tenCol` | 10, 9 | **8** | **21** | 90 | 90 |
| `Tables.elevenCol` | 11, 10 | **10** | **25** | 110 | 110 |

with `tenCol_budget`, `tenCol_divisible`, `elevenCol_divisible` as the machine-checked statements.
The `K_6` witness is *clean in defect I* (`Isolated = 0`, as `Main.extremal_no_isolated_vertex`
forces at `n = 6`) and pays its whole surplus `6·5 - 5·5 = 5` colours in unpaid edges.

### 5. §5 — **A NEW CONSTRUCTION FAMILY, TESTED AND REFUTED AT THE COUNTING BOUND**

Rounds 40–43 all attacked the *matching* side, i.e. necessary conditions on the unknown witness of
arXiv:2208.12563 §4.  Round 44 also tried a family on the **upper-bound** side, never attempted in
this development: **merge pairs of one-factors of a 1-factorisation of `K_n` into single colours**
(`discovery/JSP-000140/factormerge2.py`, plus the earlier min-conflicts solver `eg7_walk.c` and the
incremental annealer `eg8_sa.c` for the raw constraint system).  A union of two one-factors is a
disjoint union of even cycles, so the colour-degree bound of `Admissible` is automatic and the only
condition to check is *"no four-set has two vertex-disjoint pairs of edges of one colour"*; with `m`
merges one gets `k = (n-1) - m`, and at `m = (n+5)/6` exactly `5(n-1)/6`.  **Findings (all machine
checked):**

* `n = 6`, `m = 0`: **0 violations** — the family reproduces the known admissible 5-colouring of
  `K_6`, so the criterion is correct;
* `n = 10`: the round-robin 1-factorisation with `m = 0` has 3 violated four-sets and **every one of
  the 36 single merges has at least 6** (`m = 2,3,4` worse still);
* `n = 10`, `k = 8` (= the counting bound ⌈5(n-1)/6⌉, i.e. **B4**): 40 000 000 moves of min-conflicts
  from seven seeds never reached 0; the best assignment found still violates **6** of the 210
  four-sets.  **This is evidence, not a proof** — but it is the first quantitative statement about
  B4 that this development has produced.

### 6. NOT proved this round

The existence of the matching itself, i.e. `Partial.FamGreedyFamily`: for every `δ > 0` and all large
`m ≡ 1 (mod 6)` a *near-perfect* matching in `H` with a sparse leftover, no bad and no crossing
four-set, and `6(k+2D+1) ≤ 5(m-1) + δm`.  `defect_budget` now says *exactly* what such a matching has
to achieve — a first stage whose `3·Isolated + Defect ≤ δn²/2` — but producing one needs a Rödl
nibble / differential-equation method / random triangle removal, and Mathlib contains none of them.
The 1-factorisation-merging family of §5 is refuted only *at the counting bound* and for the
round-robin factorisations; a general 1-factorisation with more merges is not excluded (though
`Hyper.witness_size`/`Cherry.three_mul_paths_le_edges` bound what it could achieve).
`pairFree_of_admissible`; B4 (`f(10,4,5) ∈ {8,9}`, `f(11,4,5) ∈ {9,10}`); B5 (`K₁₃` with ten colours)
— unchanged, with the new quantitative evidence of §5 recorded for B4.

## Status (round 43)

`lake build`: **OK** (3131 jobs).  `sorry`/`admit`: **0**.  `harness/score.py --strict-prize`
(invoked on `problems/JSP-000140/lean`):
`partial_ok = true`, `prize_ready = false`, `missing_theorems = ["jsp_000140_main"]`.

**ROUND 43 PROVES THE PER-VERTEX AND PER-EDGE BUDGETS OF A FIRST STAGE — AND, FROM THEM, THAT A
NEAR-PERFECT MATCHING WITH A SPARSE LEFTOVER MUST HAVE A CENTRE AT *EVERY* VERTEX.**  Round 42
listed the per-vertex budget and the per-edge bound as its `next_lemma` and cut both to keep the build
green; both are in this file, and the per-vertex *edge* accounting that goes with them turned out to
be the sharper object.  `lean/JSPProblem/Edge.lean` grows from 737 to 1655 lines (37 -> 88
declarations, zero placeholders).

### 1. §5 — the per-vertex slot budget (`slots_at_le`)

* **`card_SlotsAtF_eq`** — the colours a family uses at `v` are *exactly* one per member centred at
  `v` and two per member having `v` as a leaf.  Round 42 could only prove `≤`: it did not know that
  the colour projection of the slots at `v` is injective, i.e. that **`SlotFree` holds at one vertex
  and one colour at a time** (`injOn_col_slotsF`).  The ingredients are `mem_slotPair`,
  `card_slotPair`, `mem_cfgSlots_leaf` and `SlotsAtF_eq`;
* **`slots_at_le` — THE PER-VERTEX SLOT BUDGET: `|centF F v| + 2·|leafF F v| ≤ k` for every vertex.**
  This is `Fam.slots_countF` (`5·|F| ≤ nk`, the slot counting of JM §4 that produced the `5/6`) made
  *pointwise*, and with `leafF_card_le` (`2·|leafF F v| ≤ k`) and `centF_card_le`.

### 2. §6 — the per-edge budget (`coverF_card_le`)

* `s_swap`, `coverF_swap`, `coverF_leaf'`, `coverF_leaf''` (the covering-member role analysis of §3,
  in a form that does not mention the three classes), `cover_ABC_disj` and
  **`card_coverF_eq_three`** — the three classes `coverA/coverB/coverC` (a-central, b-central,
  leaf-only) partition the members covering `s(a,b)`;
* `class_slots_le` (the engine: one colour at `v` for a centred class, two for a leaf class) and its
  two instances `coverA_card_le`, `coverB_card_le`;
* **`coverF_card_le` — NO EDGE OF `K_n` IS COVERED BY MORE THAN `2k/3` MEMBERS OF A MATCHING:
  `3·|coverF F (s(a,b))| ≤ 2k`** (and `coverF_card_le'`, at most `k` members).  So with the published
  `k ≈ 5n/6` each edge is covered at most `5n/9` times, while JM (IV)/BCDP Claim 4 allow `n^{1-δ}`
  leftover edges at each vertex: the per-edge budget is what forces the *leftover*, not the covering.

### 3. §7 — the per-vertex edge accounting (`degL_at`)

* `spokes`, `card_spokes`, `edgesAt`, `card_edgesAt`, `mem_edgesAt`, `covAt`,
  **`card_covAt` — A CONFIGURATION COVERS TWO OF ITS THREE EDGES AT EACH OF ITS VERTICES** (at the
  centre: the two spokes; at a leaf: the spoke *and the opposite edge* — this is round 43's correction
  of the round-43-draft, which wrongly counted one edge at a leaf);
* `card_throughF` (the members through `v` are the centred ones and the ones having `v` as a leaf),
  `covAll`, **`card_covAll` — the covered edges through `v` number `2·(|centF F v| + |leafF F v|)`**,
  **`covAll_eq_inter` — they are exactly `edgesAt v ∩ coveredF F`**, `covR`, `card_covR`,
  `covAll_covR_disj`, `edgesAt_eq_union`;
* **`degL_at` — THE PER-VERTEX EDGE ACCOUNTING:
  `n - 1 = 2·(|centF F v| + |leafF F v|) + DegL (leftoverF F) v`**, the local form of
  `Fam.edgeCoverF`.

### 4. §8 — the density a sparse leftover forces

* **`throughF_card_ge` — `2·(|centF F v| + |leafF F v|) ≥ (n-1) - D`**, i.e. *every* vertex is
  passed through by at least `⌈((n-1-D)/2)⌉` members: JM (IV) / BCDP Claim 4, per vertex
  (compare `First.SparseL_iff_degTris`);
* **`centF_card_ge` — `|centF F v| ≥ (n-1-D) - k`** (from the density and the slot budget), and
  `leafF_card_ge`; this is the *local* form of the slot counting `First.count_lower`, and it says a
  first stage cannot hide its work at a few centres and pay for it with leaves;
* **`centF_card_ge_one` / `centre_cover_univ` — IF `(n-1) - D > k` THEN EVERY VERTEX IS THE CENTRE OF
  AT LEAST ONE MEMBER**, and `sum_centF_card_ge` (the global `|F| ≥ n(n-1-D-k)`);
* `throughF_card_eq` — `|throughF F v| = |centF F v| + |leafF F v|`.

### 5. NOT proved this round

The existence of the matching itself, i.e. `Partial.FamGreedyFamily`: for every `δ > 0` and all large
`m ≡ 1 (mod 6)` a *near-perfect* matching in `H` with a sparse leftover, no bad and no crossing
four-set, and `6(k+2D+1) ≤ 5(m-1) + δm`.  Round 40 retired plain maximality (`Hyper.greedy_gap`), round
41 retired maximality-with-avoidance (`Spoil.avoid_price`), and rounds 42–43 now give *three further
necessary conditions on its witness* (the per-vertex budget, the per-edge bound, and a centre at every
vertex) that no maximality rule produces.  The obstacle is unchanged and is the density of the
matching, not the local conditions: the Rödl nibble / differential-equation method / random triangle
removal, none of which Mathlib contains.
`pairFree_of_admissible`; B4 (`f(10,4,5) ∈ {8,9}`, `f(11,4,5) ∈ {9,10}`); B5 (`K₁₃` with ten colours)
— unchanged.

## Status (round 41)

`lake build`: **OK** (3130 jobs).  `sorry`/`admit`: **0**.  `harness/score.py --strict-prize`
(invoked on `problems/JSP-000140/lean`):
`partial_ok = true`, `prize_ready = false`, `missing_theorems = ["jsp_000140_main"]`.

**ROUND 41 COMPUTES THE FIRST-MOMENT ESTIMATE OF arXiv:2208.12563 §4 AS A THEOREM, AND PROVES —
AS A THEOREM — THAT MAXIMALITY-WITH-AVOIDANCE CANNOT CERTIFY THE CATALOG BUDGET FOR ANY CHOICE OF
THE FOUR-SET CONDITIONS.**  Rounds 31–40 reduced the prize to the existence of a *near-perfect
matching* in the auxiliary hypergraph `H`; round 40 retired the *plain greedy* way of getting one.
The papers do not use maximality: they take a **partial** matching which avoids the hyperedges that
would create a bad four-set, and they bound the number of those **spoiled** hyperedges by a first
moment.  That estimate is a *finite counting statement about `H`* — no probability, no Rödl nibble,
no local lemma — and this file computes it.  New file `lean/JSPProblem/Spoil.lean` (785 lines,
27 declarations, zero placeholders).

### 1. §1 — the four-set census of `H`

* **`card_fours_sup` / `card_fours_tri` — EXACTLY `n - 3` FOUR-SETS CONTAIN A GIVEN TRIANGLE** (a
  configuration of `H` has three vertices).  This is the ingredient that turns a set of bad
  four-sets into a set of spoiled hyperedges: **each spoiled hyperedge lies in at most `n-3`
  four-sets.**
* **`card_auxF_four` — THE FOUR-SET CENSUS OF `H`: EXACTLY `24·k(k-1)` HYPEREDGES OF `H` HAVE THEIR
  THREE VERTICES IN A GIVEN FOUR-SET** (twelve ordered triples of distinct vertices out of four,
  times `k(k-1)` ordered pairs of distinct colours).  One bad four-set therefore spoils *exactly*
  `24k(k-1)` hyperedges, whatever "bad" means.
* `cfgVerts_sub_iff`, `card_filter_le`, `sum_ite_mem_card`, `sum_ite_filter_card` — the counting
  tools (the last two are the indicator-sum identities used throughout).

### 2. §2 — spoiled hyperedges: both sides of the first moment

* **`spoilF B`** — the hyperedges of `H` lying inside one of the four-sets of `B`;
* **`spoil_double` — THE DOUBLE COUNT** of the pairs `(hyperedge, bad four-set containing it)`,
  from either side;
* **`card_spoilF_le` — UPPER SIDE: `|B|` bad four-sets spoil at most `24·k(k-1)·|B|` hyperedges;**
* **`card_spoilF_ge` — LOWER SIDE: they spoil at least `24·k(k-1)·|B|` hyperedges `n-3` times over;**
* **`spoil_squeeze` — THE TWO SIDES TOGETHER: `24·k(k-1)·|B| ≤ (n-3)·|spoilF B| ≤ 24·k(k-1)·|B|`.**
  Bad four-sets and spoiled hyperedges are equivalent up to a factor `n-3`, and the four-set
  direction is exact.  This is the whole content of the first moment of §4, deterministically.

### 3. §3 — the avoidance rule, and its price

* **`SlotFresh`, `AvoidClosed`** — the rule "add a hyperedge whenever it is unblocked and
  unspoiled", and its fixed point;
* **`card_blocked_le`, `closed_census` — THE CENSUS OF A CLOSED FAMILY:
  `|E(H)| ≤ 25(n-1)(n-2)(k-1)·|F| + |spoiled|`** (every hyperedge of `H` is blocked by a slot of
  `F`, or is unblocked and hence spoiled);
* **`avoid_first_moment` — WHAT THE RULE DELIVERS:
  `n(n-1)(n-2)·k(k-1) ≤ 25(n-1)(n-2)(k-1)·|F| + 24·k(k-1)·|B|`;**
* **`avoid_certify` — THE PRICE OF THE FOUR-SET CONDITIONS: `25·|F| + n ≥ n·k` as soon as
  `24k·|B| ≤ n(n-1)(n-2)`** — a four-set condition costing `o(n²)` four-sets costs the rule at most
  `n` slots out of `n·k`;
* **`avoid_gap` / `avoid_gap_of_budget` / `avoid_price` — AND THE PUNCHLINE.**  At `δ ≤ 1/6`, with
  the catalog budget `6k ≤ (5+δ)n − 11`, the best size the rule can certify is at most
  `n((5+δ)n−17)/150`, and that is **strictly below** `n((7−δ)n−1)/42`, the size every valid first
  stage must have (`Hyper.first_stage_size`).  So **maximality-with-avoidance cannot certify the
  budget, whatever the four-set conditions are**: the Rödl nibble is needed for the *matching
  itself*, not for the local conditions.  This is the strict generalisation of round 40's
  `Hyper.greedy_gap` to a strictly stronger deterministic rule.

### 4. §4 — the bridge back to the catalog condition

* **`badFours`, `mem_badFours`, `badFours_eq_empty_iff` — `Admissible c ↔ badFours c = ∅`:**
  the set of four-sets a colouring fails on, and the equivalence with the catalog condition;
* **`spoilF_empty_of_admissible`** — an admissible colouring spoils no hyperedge at all, i.e. the
  four-set conditions of §4 are exactly the filter of the avoidance rule.

**NOT proved this round.**  The existence of the near-perfect matching
(`Partial.FamGreedyFamily`, the single remaining prize hypothesis).  §2–§3 above now *prove* that
the first-moment counting of the local conditions is available and cheap, and that the resulting
deterministic rule is short of the budget by a factor `≈ 25/7 · 7/(5+δ) > 4`; the missing step is
the one that is genuinely probabilistic (Rödl nibble / differential-equation method / random
triangle removal), and Mathlib has neither.  `pairFree_of_admissible`, B4 (`f(10,4,5) ∈ {8,9}`,
`f(11,4,5) ∈ {9,10}`) and B5 (`K₁₃` with ten colours) are unchanged.

## Status (round 40)

`lake build`: **OK** (3129 jobs).  `sorry`/`admit`: **0**.  `harness/score.py --strict-prize`
(invoked on `problems/JSP-000140/lean`):
`partial_ok = true`, `prize_ready = false`, `missing_theorems = ["jsp_000140_main"]`.

**ROUND 40 ATTACKS THE EXISTENCE SIDE FOR THE FIRST TIME IN THE MATCHING WORLD, AND PROVES — AS A
THEOREM, NOT AS PROSE — THAT THE CHEAPEST DETERMINISTIC CONSTRUCTION CANNOT WORK.**
Rounds 31–39 only *assumed* the first stage exists.  This round builds the auxiliary `8`-uniform
hypergraph `H` of arXiv:2208.12563 §4 (= arXiv:2207.02920 Phase 1) as **data**, computes it exactly,
and then runs the *whole* of the greedy / maximal-matching argument on it.  New file
`lean/JSPProblem/Hyper.lean` (831 lines, 51 declarations, zero `sorry`).

### 1. §1 — `H` as data, and its census

The hypervertices of `H` are the slots `Verts n × Fin k`; its hyperedges are the five-slot sets of
the well-formed configurations.

* **`auxF`, `mem_auxF`, `OkF_iff`** — the edge set of `H`, and `OkF F ↔ F ⊆ auxF n k`.
* **`card_auxF` — THE CENSUS OF `H`: `|E(H)| = n(n-1)(n-2)·k(k-1)`.**  Three pairwise distinct
  vertices and two distinct colours.  No colouring, no four-vertex clique, no probability anywhere.
  (The ingredients `card_offdiag` — ordered pairs of distinct vertices avoiding a given one — and
  `sum_ite_ne` — `k(k-1)` ordered pairs of distinct colours — are proved too.)

### 2. §2 — the degree of a hypervertex of `H`

* **`card_ok_centre`** — the hyperedges prescribing the centre slot number exactly
  `(n-1)(n-2)(k-1)` (the other two vertices avoid `x` and each other, the other colour avoids `c`);
* **`swapUP`, `swapPQ`, `swapIJ`** (each an `Equiv`, each preserving `Ok`) and the four transfer
  lemmas `card_ok_leafP`, `card_ok_leafQ`, `card_ok_leafPJ`, `card_ok_leafQJ` — a prescribed *pair* of
  slots may be moved to any other pair, so one count suffices;
* **`card_auxDeg_le` — THE DEGREE OF A HYPERVERTEX OF `H`:
  `|{ g ∈ H : σ ∈ slots g }| ≤ 5(n-1)(n-2)(k-1)`.**  Exact.

### 3. §3 — the greedy (maximal-matching) argument, in full

* **`SlotMaximal`** — no hyperedge of `H` outside `F` is slot-disjoint from `F`; this is exactly the
  output of a greedy hypergraph-matching algorithm;
* **`blockedF`, `blocked_card_le`** — at most `25(n-1)(n-2)(k-1)` hyperedges share a slot with a fixed
  member of `F`;
* **`card_auxF_le_of_maximal`** — the double count `|E(H)| ≤ |Slots F|·5(n-1)(n-2)(k-1)`;
* **`greedy_guarantee` — WHAT THE TRIVIAL ARGUMENT PROVES: `25|F| ≥ n·k`, i.e. `|F| ≥ nk/25`.**
  This is the *entire* content of the nibble-free argument: a maximal matching covers at least
  `3nk/25` edges of `K_n`, about a fifth of them.

### 4. §4 — what the catalog budget demands, and the gap

* **`budget_k_le`** (`6k ≤ (5+δ)n − 11`) and **`budget_le_D`** (`7D + 6 ≤ δn`, the converse
  direction of `First.proper_fits`), from the budget and the slot counting;
* **`first_stage_size` — WHAT THE BUDGET FORCES: `42|F| ≥ n((7-δ)n − 1)`, i.e. `|F| ≈ n²/6`** — more
  than five times what §3 delivers;
* **`leftover_frac_le`**, **`leftover_frac_le_of_small`** — the leftover is at most a `δ/7`-fraction
  of the edges, and **at the published `δ ≤ 1/6` it is at most `1/42` of them**: the first stage must
  cover more than `41/42` of `E(K_n)`;
* **`greedy_gap` — THE GAP: `42nk < 25n((7-δ)n−1)` for `δ ≤ 1/6`, `n ≥ 1`**, i.e. the greedy
  guarantee `nk/25` is strictly below the size of every valid first stage, by a factor
  `42(5+δ)/(25(7-δ)) > 4`;
* **`greedy_short`, `no_greedy_first_stage`** — every valid first stage has `25|F| > n·k`, and **no
  family of size at most `nk/25` satisfies the published budget**.  The Rödl nibble / random triangle
  removal is therefore *necessary*, and this is now a theorem of the development rather than a remark.

*Honest scope*: `greedy_guarantee` and `first_stage_size` are both **lower bounds** on `|F|` and are
mutually compatible — a maximal family may be lucky.  What is proved is that the *guarantee* the
trivial argument delivers is short of what the budget requires by a factor `> 4`, so maximality can
never *certify* a first stage.

### 5. §5 — what the prize hypothesis says about its witness

* **`witness_size`** — reading the two theorems off `Partial.FamGreedyFamily`: for `δ ≤ 1/6` any
  family paying the budget has more than `n((7-δ)n−1)/42` members and leaves at most `1/42` of the
  edges uncovered.  So the object of arXiv:2208.12563 §4 is a *near-perfect* hypergraph matching.

**NOT proved this round.**  The existence of that matching: it is a hypergraph-matching existence
theorem (Rödl nibble / differential-equation method / random triangle removal); Mathlib has neither a
nibble nor a local lemma, and both papers are existential, so there is no colouring to write down.
§3–§4 above now *prove* that this is a real obstruction rather than an omission of effort.
`pairFree_of_admissible`, B4 (`f(10,4,5) ∈ {8,9}`, `f(11,4,5) ∈ {9,10}`) and B5 (`K₁₃` with ten
colours) are unchanged.

## Status (round 39)

`lake build`: **OK** (3128 jobs).  `sorry`/`admit`: **0**.  `harness/score.py --strict-prize`
(invoked on `problems/JSP-000140/lean`):
`partial_ok = true`, `prize_ready = false`, `missing_theorems = ["jsp_000140_main"]`.

**ROUND 39 CLOSES THE ROUND-38 BLOCKER COMPLETELY: `Tile` AND `Packed` OF THE FINISHED COLOURING
ARE FREE, AND THE REQUIRED THEOREM IS REDUCED TO THE PUBLISHED FIRST STAGE WITH AN ARBITRARY
LEFTOVER AND A DETERMINISTIC SECOND STAGE.**
`lean/JSPProblem/Partial.lean` grows from 437 to 1038 lines (20 -> 47 declarations, zero `sorry`).

*Section 4 — the leaf half of the tiling condition* (the lemma round 38 isolated as `next_lemma`):

* `partner_coverNbrs` — the edge from `v` to a covered colour-`i` neighbour of `v` is an edge of
  the member holding the slot `(v,i)` (the forcing step of `coverNbrs_mem`, isolated);
* `coverNbrs_card_le_one_of_leaf` — **a leaf of the slot graph has at most one covered colour-`i`
  neighbour** (the four partner lemmas force it to be a single vertex);
* `coverNbrs_eq_pair_of_card_two` — **TWO COVERED NEIGHBOURS MEAN A CENTRE**: `v` is the centre of
  the member holding `(v,i)`, `i = cfgI g`, and the two neighbours are exactly its two leaves;
* **`coverNbrs_card_one_of_mem_card_two`** — **the leaf half of `Criterion.Tile` for a partial first
  stage**: each of the two has covered colour-degree exactly one;
* `coverNbrs_eq_singleton_of_card_two` — the same in the form `{centre}`, and `edgeCol_spoke_leaf`
  (a spoke of a configuration carries the centre colour).

*Section 5 — the finished colouring.*  With `c := extendColDep (colOf F d) (leftoverF F) g`
(the first-stage colours kept, every leftover edge given a fresh colour):

* `finCol`, `extendColDep_finCol_of_leftover`, `covered_of_nmem_leftoverF`, **`mem_Nbrs_finCol`**
  and `card_Nbrs_finCol` — **the bridge**: for a first-stage colour `i` and `a ≠ v`,
  `a` is an `i`-neighbour of `v` in the finished colouring **iff** it is a *covered* `i`-neighbour
  of `v` in the matching; and an edge of the leftover never receives a first-stage colour;
* `card_le_one_of_fresh` — **a fresh colour has colour-degree at most one**, by `Proper`;
* **`tile_of_fam_partial`** — **`Tile c` from `OkF + LinF + SlotFree + Proper` alone**: degree half
  from `coverNbrs_card_le_two`, leaf half from `coverNbrs_card_one_of_mem_card_two`, fresh case from
  `Proper`.  No `Covers`, no bound on the leftover;
* `mem_twoA_card_two`, **`pathSet_eq_cfgVerts`** — the two-edge paths of the finished colouring are
  *exactly* the three vertices of the members of `F`, with their centre colours;
* **`packed_of_fam_partial`** — **`Packed c` from the same hypotheses** (`cfgVerts_lin`).

*Sections 6–7 — the reduction.*

* **`FamPartialFamily`** — the published construction in the form it actually has: for every
  `δ > 0` and all large `m ≡ 1 (mod 6)` a matching `F` in the auxiliary hypergraph of
  arXiv:2208.12563 §4 / arXiv:2207.02920 Phase 1, a **sparse leftover** (`SparseL D`, = JM (IV) of
  Thm 4.2 = BCDP Claim 4), a **proper** second stage (`A_{e,f,i}` resp. `B₁`), the two four-set
  conditions (`B_D`, `C_{D,i}`) and the budget `6(k+K) ≤ 5(m-1) + δm`.  **No colouring is
  quantified over**: `F` is a finset of configurations and `g` is its second-stage colouring.
  **No complete covering is required** — this is the published (partial) covering, in contrast with
  round 37's `FamFamily`;
* `FamPartialFamily.admissible`, `FamPartialFamily.slack`,
  **`jsp_000140_main_of_fam_partial_family`** — the required theorem reduced to it;
* **`greedyF`, `proper_greedyF`** — the **deterministic** second stage: if the leftover has maximum
  degree `D`, the greedy edge colouring of `Second.proper_of_sparseL` gives a proper colouring of
  the leftover with `2D+1` fresh colours, so `Proper` need not be a hypothesis at all;
* **`FamGreedyFamily`, `famGreedyFamily_partial`, `jsp_000140_main_of_greedy_family`** — the sharpest
  interface found so far: the leftover's *sparsity* alone pays for the second stage, and what is
  left is (i) the matching in the auxiliary hypergraph, (ii) its leftover degree, (iii) the
  exclusion of the alternating four-cycles and the crossing pairs — the only genuinely probabilistic
  part of the two papers.

**NOT proved this round.**  The existence of the first stage: the hypergraph matching of
arXiv:2208.12563 §4 (Thm 4.2) / the random triangle removal of arXiv:2207.02920, together with the
two four-set conditions of its second stage.  Mathlib has neither a Rödl nibble nor a local lemma.
`jsp_000140_main` therefore remains undeclared: the reduction theorems have the honest hypothesis
`FamGreedyFamily`, which is a probabilistic existence statement.

## Status (round 38)

`lake build`: **OK** (3128 jobs).  `sorry`/`admit`: **0**.  `harness/score.py --strict-prize`
(invoked on `problems/JSP-000140/lean`):
`partial_ok = true`, `prize_ready = false`, `missing_theorems = ["jsp_000140_main"]`.

**ROUND 38 REMOVES THE COMPLETE-COVERING REQUIREMENT FROM TWO OF THE FOUR LOCAL CONDITIONS.**
Round 37 could only close the *extremal* first stage (`FamFamily` demands `leftoverF F = ∅`),
because `Tile` and `Packed` were imported from `Triangles.lean`, where they are consequences of
`Covers`.  New file `lean/JSPProblem/Partial.lean` (437 lines, 20 declarations, zero `sorry`)
attacks that blocker, and the mechanism is one lemma:

* **`colSlot_covered` — THE SLOT LEMMA.**  If a **covered** edge `s(v,a)` has colour `i` in the
  induced colouring `colOf F d`, then the member covering that edge uses the **slot** `(v,i)`.
  Since `SlotFree` admits at most one member per slot, **every colour-degree of the induced
  colouring of an arbitrary matching in the auxiliary hypergraph is at most two — with no
  `Covers` hypothesis and no bound whatsoever on the leftover.**  This is `Criterion.Tile`'s
  degree half, and it is *free*.
* **`coverNbrs_mem`** — the **explicit classification** of a covered colour-`i` neighbour of `v`:
  a leaf if `v` is the centre of the member holding the slot `(v,i)`, the centre if `v` is a leaf,
  the other leaf if the colour is the `cfgJ` colour.  (This is the local form of
  `Cherry.leaf_not_centre`.)  With `partner_of_centre`, `partner_of_leaf`, `partner_of_leafJ`,
  `partner_of_leafJ'` it is the whole combinatorics of a two-edge path in the matching world.
* **`coverNbrs_card_le_two`** — **THE COLOUR-DEGREE BOUND IS FREE.**
* **`cfgVerts_lin` — THE PACKING CONDITION IS FREE.**  Two members whose triples meet in two
  vertices share an edge, so `LinF` forces them to be equal: the triples of the members of a
  family form a **partial Steiner triple system**.  This is `Criterion.Packed` outright, again
  with no complete covering.

**NOT proved this round.**  The **leaf half** of the tiling condition
(`coverNbrs_card_one_of_mem_card_two`: a vertex with two covered colour-`i` neighbours gives each
of them exactly one), hence `Tile` and `Packed` of the **finished** colouring, hence the reduction
`jsp_000140_main_of_fam_partial_family` to a leftover-tolerant first stage.  The draft of that
chain and the exact failing tactics are recorded in `discovery/JSP-000140/policy.json`
(`next_lemma`); it is mechanical once the leaf half is in.  The single remaining *existence*
object is unchanged (the hypergraph matching of arXiv:2208.12563 §4 / arXiv:2207.02920 Phase 1).

## Status (round 37)

`lake build`: **OK**.  `sorry`/`admit`: **0**.  `harness/score.py --strict-prize`
(invoked on `problems/JSP-000140/lean`):
`partial_ok = true`, `prize_ready = false`, `missing_theorems = ["jsp_000140_main"]`.

**ROUND 37 CHANGES THE SHAPE OF THE RESIDUAL HYPOTHESIS: THE FIRST STAGE IS NO LONGER A
COLOURING BUT A MATCHING IN THE AUXILIARY HYPERGRAPH.**

Every hypothesis of this development up to `First.PartialStageFamily` is stated for a colouring
`c : Col n k`.  That is the wrong way round for an *existence* theorem: what
arXiv:2207.02920 (Phase 1) and arXiv:2208.12563 (§4, Thm 4.2) produce is a **matching in an
auxiliary `8`-uniform hypergraph** whose hypervertices are the `(vertex, colour)` slots, and the
colouring of `K_n` is a *consequence* of that matching.  New file `lean/JSPProblem/Fam.lean`
(1021 lines, 55 declarations, zero `sorry`) makes that object the primitive one.

* **A CONFIGURATION is data**: `Cfg n k = Verts n × Verts n × Verts n × Fin k × Fin k` — centre,
  two leaves, the colour at the centre, the colour of the opposite edge — with `cfgEdges` (the
  hyperedge: three edges of `K_n`), `cfgSlots` (the five hypervertices of arXiv:2208.12563 §4),
  `edgeCol`, `Ok`; a **family** `F : Finset (Cfg n k)` with `OkF`, `LinF` (two members share no
  edge), `SlotFree` (**the matching condition**: two members share no slot), `coveredF`, `leftoverF`.

* **The slot counting of round 36, with no colouring anywhere**: `card_cfgSlots` (5),
  `card_cfgEdges` (3), `card_SlotsF` (`5·|F|`), **`slots_countF`** (`5·|F| ≤ n·k`),
  `card_coveredF` (`3·|F|`), **`edgeCoverF`** (`C(n,2) = 3·|F| + |leftoverF|`), `handshakeF`
  (`2·|leftoverF| ≤ n·D`), **`count_lowerF`** (`5(n-1) ≤ 6k + 5D`), `count_lowerF_tight`,
  `first_stage_numbersF`.

* **THE COLOURING IS INDUCED, AND THE ENCODING IS AN EQUIVALENCE.**
  `colOf F d` is the colouring prescribed by the matching; `mem_cfgSlots_end` (every endpoint of an
  edge of a configuration uses the slot of that edge's colour) and `eq_long_of_same` (two edges of a
  configuration with the same colour are the two edges at its centre) are the combinatorics of the
  hyperedge; then **`labTri_of_mem`** (a member of the family is a labelled triangle of `colOf`),
  **`covers_colOf`** and **`pairFree_colOf`** (a family covering `E(K_n)` *is* a labelled-triangle
  system in the sense of `Triangles.lean`), with the converse
  **`mem_or_mem_swap_of_labTri`** / `mem_or_mem_swap_of_labTri'` — every labelled triangle of
  `colOf` comes from **one** member of the family, because the slot `(u,i)` is shared by the two
  configurations covering the two edges at the centre and `SlotFree` forces them to coincide.

* **`FamFamily` and `jsp_000140_main_of_fam_family`**: the required theorem `jsp_000140_main`
  reduced to the existence, for every `δ > 0` and all large `m ≡ 1 (mod 6)`, of a matching in the
  auxiliary hypergraph (a finset of configurations, pairwise edge- and slot-disjoint, covering all
  of `E(K_m)`, with no bad and no crossing four-set in the induced colouring, and at most
  `5(m-1)/6 + δm/6` colours).  **No colouring is quantified over in the hypothesis**, so it is a
  finite combinatorial condition on a finset — a checkable object, which is what a construction can
  actually provide.

* **THE CENTRE BALANCE (section 5)**: `centF`, `leafF`, `throughF`; `slotsAt` with
  `slotsAt_centre` (exactly **one** slot at the centre), `slotsAt_leaf`/`slotsAt_leaf'` (exactly
  **two** at a leaf), `slotsAt_ne` (none elsewhere), `card_slotsAt`; and
  **`card_slotsF`** — the slots a family uses at `v` are one per configuration centred at `v` and
  two per configuration having `v` as a leaf:
  `(slotsF F v).card = (centF F v).card + 2·(leafF F v).card`, with `card_slotsF_le` (`≤ k`).

**NOT proved this round (blockers B1, B2 in `discovery/JSP-000140/policy.json`)**:
`FamFamily` is an existence theorem about a hypergraph matching (Rödl nibble / differential-equation
method), and Mathlib has neither.  Moreover the interface proved here needs a **complete** covering,
because `pairFree_colOf` (hence `tile_of_tri`/`packed_of_tri`, and with them the automatic `Tile`
and `Packed`) needs `Covers`; with a leftover the uncovered edges carry the default colour and
spurious labelled triangles appear.  The published Phase 1 leaves `Θ(n^{2-δ})` edges over
(BCDP §4: the matching stops at `i_max = (1/6)n²(1-n^{-δ})`), so the complete interface is the
*extremal* case and the partial one needs `Tile`/`Packed`/`LeafClosed`/`CrossThin` ported to
configurations.  That port is the single next step (policy `next_round_plan` item 1).

# ACCEPTANCE — JSP-000140

## Catalog statement (record `JSP-000140`, fetched 2026-09-30)

> **JSP-000140 · How many edge colors are necessary if every four-vertex clique must contain
> at least five colors?**
>
> | Field | Value |
> | --- | --- |
> | Mathematical area | Graph theory |
> | Date proposed | No later than 1997 (bibliographic evidence) |
> | Current status | **Solved** |
> | Lean proof (catalog) | **No** |
> | Publications | `[BCDP22]` arXiv:2207.02920 — *The Erdős–Gyárfás function `f(n,4,5) = 5n/6 + o(n)` — so Gyárfás was right*, **by Patrick Bennett, Ryan Cushman, Andrzej Dudek, Paweł Prałat** (round 13 correction: the authors are *not* Banerjee–Bradshaw–Letzter–Pokrovskiy, and the construction is **probabilistic** — a randomised process based on *random triangle removal*, analysed with the differential-equation method — so there is no explicit colouring to formalise); `[JoMu22]` arXiv:2208.12563 |

The quantity asked for is the **Erdős–Gyárfás function** `f(n, p, q)`, i.e. the least number
of colours in an edge-colouring of `K_n` in which every `K_p` spans at least `q` colours,
specialised to `f(n, 4, 5)`.  The solved answer is

    f(n, 4, 5) = 5n/6 + o(n).

## Required theorem

`jsp_000140_main` — the Lean name that the prize gate checks.  It must be the **complete**
catalog statement, i.e. `f(n, 4, 5) = 5n/6 + o(n)`, proved with no `sorry`.  In this
development the statement is

```lean
JSP140.jsp_000140_target : Prop := JSP140.FiveSixth JSP140.EG
JSP140.FiveSixth f : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → |(f n : ℝ) - 5 * (n : ℝ) / 6| ≤ ε * n
```

with `JSP140.EG n` the least number of colours in an admissible colouring of `K_n`
(`lean/JSPProblem/Definitions.lean`), and

```lean
JSP140.Admissible c : Prop :=
  ∀ S : Finset (Fin n), S.card = 4 → 5 ≤ (JSP140.colorsOn c S).card
```

the catalog condition ("every four-vertex clique contains at least five colours").

## Status (round 36)

`lake build`: **OK** (3126 jobs).  `sorry`/`admit`: **0** (`placeholder_total = 0`).
`harness/score.py --strict-prize` (invoked on `problems/JSP-000140/lean`):
`build_ok = true`, `partial_ok = true`, `prize_ready = false`,
`missing_theorems = ["jsp_000140_main"]`.

**ROUND 36 PROVES THE SLOT COUNTING — THE CONSTANT `5/6` IS NOW A THEOREM ABOUT THE FIRST STAGE
ALONE, AND THE CATALOG BUDGET IS SHOWN TO BE *EQUIVALENT* TO THE FIRST STAGE'S COLOUR BOUND.**  This
closes the blocker that round 35 had to isolate as a hypothesis (`First.FirstStageCounting`), so the
residual prize hypothesis no longer contains any counting axiom.

### 1. New file `lean/JSPProblem/Slot.lean` (497 lines, 24 declarations, zero placeholders)

* **`triPairs_eq_anchorPairs`** — THE INGREDIENT ROUND 35 WAS MISSING.  The five `(vertex, colour)`
  pairs of a labelled triangle `(u,p,q)` are the *anchor* pairs of its **vertex set**: `(x,j)` with
  `x ∈ T` and `j` the colour of an edge of the triangle at `x`.  So the slot count is a function of
  the vertex set and of the colouring, and round 35's impossible "canonical labelling"
  (`lab : triSet c → …` cannot be total, `Fin 0` being `Empty`) is simply not needed: `triSets c` is
  the *image* of the finset of labelled triangles, so no representative is ever chosen;
* **`card_triPairs`** — five distinct pairs per triangle (the hypervertices `{u_i,v_i,w_i,v_j,w_j}`
  of the auxiliary `8`-uniform hypergraph `H` of arXiv:2208.12563 §4);
* **`slots_five`** — **THE SLOT COUNTING**, `5 · |triSets c| ≤ n · k`: the slots of two different
  triangles are disjoint (`PairFree.of_common`), and there are `n·k` of them;
* **`edgeCover_count`** — **THE OTHER HALF**, the exact identity `C(n,2) = 3·|triSets c| + |leftover c|`:
  every edge of `K_n` lies in a unique labelled triangle or is leftover;
* **`sum_DegL_two_mul_card`, `handshake_le`** — the **handshaking lemma** `2·|L| ≤ n·D` for a leftover
  of maximum degree `D` (round 35 had only the weaker `|L| ≤ n·D`, which is why its slack was `10D`);
* `lin3_triSets` — two triangles of the system sharing an edge are the same triangle, so the triangle
  system is **linear** (this is where `PairFree` is consumed).

### 2. `lean/JSPProblem/First.lean` §6 — fourteen new theorems

* **`count_lower` — THE SLOT COUNTING AS A THEOREM: `5(n-1) ≤ 6k + 5D` from `PairFree` and
  `SparseL (leftover c) D` alone.**  **No four-vertex clique is checked anywhere in this proof**, so
  the constant `5/6` of the catalog answer follows from the hypergraph-matching structure of the first
  stage by itself: five slots buy three edges;
* **`count_lower_tight`, `tight_attained_of_le`** — for a *complete* covering (`D = 0`):
  `5(n-1) ≤ 6k`, attained or strictly exceeded, never fallen short of;
* **`budget_published_iff` — THE SHARP FORM OF THE CATALOG BUDGET.**

      `6(k + 2D + 1) ≤ 5(n-1) + δn  ↔  6k + 5D ≤ 5(n-1) + δn - 7D - 6`,

  i.e. **the budget of the published two-stage construction is not an extra hypothesis**: it *is* the
  first stage's colour bound, with the second stage's `7D+6` (the greedy properness `2D+1`, see
  `proper_fits`) already deducted.  (An earlier draft claimed the budget follows from `7D+6 ≤ δn`
  alone; that is **false** and was deleted — `count_lower` is `≥`, so the slot count must also be
  tight.  The truth is the iff above.)
* **`budget_and_count`** — with `count_lower`, the budget squeezes the first stage's colour count
  into an interval of width `δn`: the published slot count must be asymptotically tight;
* `leftover_eq_leftoverTris` — the leftover of a colouring *is* the leftover of its triangle system;
* **`SparseL_iff_degTris_triSets`** — round 35's density lemma, now for the objects the construction
  actually produces: `SparseL (leftover c) D ↔ 2·degTris (triSets c) v ≥ n-1-D` at every vertex, i.e.
  the first stage must pass through every vertex at least `⌈(n-1-D)/2⌉` times;
* `sum_degL_edgeFinset`, `edge_count_two_mul` — `2·C(n,2) = n(n-1)`;
* `first_stage_numbers` — the three numbers of a first stage (slots, edges, degree) in one statement.

### 3. NOT proved this round (blockers)

* **the existence of the first stage** — `First.PartialStageFamily`, now with its budget rewritten as
  the first stage's colour bound by `budget_published_iff`: an almost-complete linear triple system
  with `PairFree`, no bad/crossing four-set, leaf closure, leftover degree `D`, `o(n)` crossing pairs
  and at most `5(m-1)/6 + (δm-7D-6)/6` colours.  This is JM Thm 4.2 / BCDP Phase 1, a *probabilistic*
  existence theorem; Mathlib has neither the Rödl nibble nor the local lemma, so no amount of
  verification-side work reaches it.
* **the deterministic maximal-matching obstruction** — the cheapest deterministic fragment of the
  existence side, and the `next_lemma` of round 37 (see `policy.json`).
* `pairFree_of_admissible`; B4 (`f(10,4,5) ∈ {8,9}`, `f(11,4,5) ∈ {9,10}`); B5 (`K₁₃` with ten
  colours) — unchanged.

## Status (round 35)

`lake build`: **OK** (3125 jobs).  `sorry`/`admit`: **0**.  `harness/score.py --strict-prize`
(invoked on `problems/JSP-000140/lean`):
`build_ok = true`, `partial_ok = true`, `prize_ready = false`,
`missing_theorems = ["jsp_000140_main"]`.

**ROUND 35 GOES AFTER THE *FIRST* STAGE — AND FINDS THAT THE ROUND-34 INTERFACE IS VACUOUS AND
THAT THE DETERMINISTIC SECOND STAGE IS PROVABLY UNPAYABLE.**  New file
`lean/JSPProblem/First.lean` (696 lines, 47 declarations, zero placeholders).

### 1. The first stage is a linear triple system, and its density is a *per-vertex* condition

`Tri3`/`Lin3`/`degTris`/`covTris`/`leftoverTris` abstract the first stage of arXiv:2208.12563 §4 —
edge-disjoint triangles of `K_n`, one colour each, `(vertex, colour)` pairs of distinct triangles
disjoint — to a **linear family of three-element vertex sets**:

* `card_covTris` — the vertices covered at `v` number `2 · degTris v` (linearity is exactly what
  makes the contributions disjoint);
* `sum_degTris` — `∑_v degTris v = 3 · |Tris|`;
* `deg_le` — `2 · degTris v ≤ n - 1`, the Steiner bound;
* `card_leftover_le_of_SparseL` — the **total** form, `|L| ≤ nD`, the shape a first-moment argument
  produces;

* **`SparseL_iff_degTris` — THE FIRST-STAGE DENSITY LEMMA.**  The leftover graph of the triple
  system has maximum degree at most `D`

      `⟺  2 · degTris v ≥ n - 1 - D`  for every vertex `v`.

  This is the exact, purely combinatorial form of "maximum degree `D = n^{1-δ}`" (JM §4 (IV) /
  BCDP Claim 4): **the first stage must pass through every vertex at least `⌈(n-1-D)/2⌉` times.**

### 2. **THE PRICE OF EVERY SECOND STAGE — the headline of this round**

`FirstStageCounting` (`5(n-1) ≤ 6k + 5D`, the slot counting of JM §4) plus

* **`budget_leftover` — THE ACCOUNTING IDENTITY.**  The catalog budget
  `6(k + fresh) ≤ 5(n-1) + δn` leaves `6 · fresh ≤ 5D + δn` for the second stage.

From that one identity:

* **`proper_fits`** — the **published** second stage (round 31's greedy properness,
  `fresh = 2D + 1`) fits whenever `7D + 6 ≤ δn`; for the published `D = n^{1-δ}` this holds for all
  large `n`.  **The second stage of the papers is PAYABLE; the local lemma is not needed for it.**
* **`deterministic_budget_strong` / `deterministic_budget`** — the deterministic second stage of
  rounds 33/34, which also excludes `B₂ = B_D` and `B₃ = C_{D,i}` with no probability and costs
  `fresh = 2D² + 2D + T + 1`, gives

      `12 D² + 7D + 6T + 6 ≤ δn`,   in particular   **`12 D² ≤ δn`**,  i.e.  `D = O(√(δn)) = o(√n)`.

  For `D = n^{1-δ}` and `δ < 1/2` this is **false for all large `n`**.
* **`deterministic_imp_proper` / `deterministic_ne_proper`** — the two budgets are strictly ordered:
  the round-33/34 budget implies the published one, not conversely.

**This retires a whole attack family.**  The "honest price" of rounds 33/34 was prose; it is now
`deterministic_budget`, a theorem.  **At the published parameters the symmetric local lemma (or
something of its strength) is genuinely necessary for `B₂` and `B₃`** — and a first-moment argument
is no help either, since it also needs `q ≫ D²` while the budget leaves only `fresh ≤ (5D + δn)/6`.

### 3. The interface of round 34 is **vacuous**

`CrossStageFamily` asserts `Covers c₀` — the **complete** covering of round 29 — together with
`SparseL` and `CrossThin` on `leftover c₀`.  But `Covers c₀ ↔ leftover c₀ = ∅`
(`covers_iff_leftover_eq_empty`), so with `D = T = 0` the fresh-colour cost is `1`, and

* **`crossStageFamily_iff_triFamily` : `CrossStageFamily ↔ TriFamily`** (together with
  `crossStageFamily_tri`, `crossStageFamily_of_tri`, `jsp_000140_main_of_cross_iff_tri`).

**The whole second stage of rounds 33 and 34 is dead code with respect to the remaining
hypothesis.**  `PartialStageFamily` is the corrected interface: the first stage may leave `o(n²)`
edges uncovered, `Design` and `LeafClosed` are hypotheses (they are Phase-1 output, and
`tile_of_tri`/`leafClosed_of_tri` need the *complete* covering), and `SparseL`/`CrossThin` are
genuinely non-vacuous.  `crossStageFamily_partial` shows it is at least as general, and
`leftover_card_le` records *why* a total bound is not enough: `AlmostCovers c (n·n)` holds for
**every** colouring.

### 4. NOT proved this round (blockers)

* **the slot counting itself** — `First.count_lower`, `5(n-1-D) ≤ 6k` from `PairFree` alone.  It is
  isolated as the hypothesis `FirstStageCounting`, and every verdict of §2 is proved *from* that
  hypothesis, so none of them depends on its details.  The recipe (all four ingredients derived in
  round 35 and recorded in `policy.json.next_lemma`): `centre_unique` — the centre of a first-stage
  triangle is determined by its vertex set, the Steiner-system-with-a-centre-per-block structure of
  rounds 13/24; `card_triPairs = 5`; the double count `∑_T ∑_v |colTris c T v| = 5·|Σ|`; and the
  injectivity of `(T, v, i) ↦ (v, i)` from `PairFree`.  The obstacle is that a canonical labelling
  of each triple cannot be a *total* function (`Fin 0` is `Empty`).
* **the existence of the first stage** — an almost-complete linear triple system with uniform vertex
  degree, `NoCrossFour`, `NoBadFour`, leaf closure, and a controlled crossing count: this is
  `PartialStageFamily`, and it is the single remaining prize hypothesis.
* `pairFree_of_admissible`; B4 (`f(10,4,5) ∈ {8,9}`, `f(11,4,5) ∈ {9,10}`); B5 (`K₁₃` with ten
  colours) — unchanged.

## Status (round 34)

`lake build`: **OK** (3124 jobs).  `sorry`/`admit`: **0**.  `harness/score.py --strict-prize`
(invoked on `problems/JSP-000140/lean`):
`build_ok = true`, `partial_ok = true`, `prize_ready = false`,
`missing_theorems = ["jsp_000140_main"]`.

**ROUND 34 REMOVES THE OTHER BAD-EVENT FAMILY TOO: THE WHOLE SECOND STAGE OF BOTH PAPERS IS
DETERMINISTIC.**  Round 33 removed `B_D` and declared the last bad event `C_{D,i}`
(= `B₃`) ungreedyable "because it constrains *disjoint* pairs of leftover edges", leaving the
symmetric Lovász Local Lemma as the only remaining probabilistic tool.  **That is a statement about
the colours, not about the combinatorics, and this file corrects it**: what a greedy colouring needs
is a *bound* on the number of partners each edge has, not adjacency.

New file `lean/JSPProblem/Cross.lean` (581 lines, 22 public + 8 private declarations, zero
placeholders):

* **`greedy_of_boundedRel` — THE GENERAL ENGINE.**  For *any* symmetric relation `R` on a finite set
  `F` in which every `e ∈ F` is `R`-related to at most `M` others, there is a map `g : F → Fin (M+1)`
  injective on every `R`-related pair of distinct elements (elements added one at a time by
  `Finset.induction_on`; each new element avoids the colours of the at most `M` already-coloured
  elements related to it).  `Second.rainbow_of_sparse_leftover` is the instance `R = Shares`,
  `M = 2D`; round 33's `star_greedy` is the instance `R = Shares ∨ Sep`, `M = 2D² + 2D`;
* **`Cross` — the crossing relation of `C_{D,i}`** (two crossing leftover edges whose complementary
  pair is covered and phase-1 monochromatic), with `Cross.symm`, `ne_of_Cross`, and
  **`noCrossFresh_of_inj`**: a fresh colouring injective on the `Cross` pairs cannot produce the bad
  event at all — a strictly stronger statement than `NoCrossFresh`, which only asks for distinctness
  when the complementary pair happens to be monochromatic;
* **`crossF`, `card_crossF_le` — THE UNCONDITIONAL BOUND `4n`.**  A partner of `e = s(a,c)` is
  `s(b,d)` with `c₀ s(a,d) = c₀ s(b,c)` (or the same for the other complementary pairing of the
  4-set), so for each of the `≤ n` choices of `b` there are at most two choices of `d` — by the first
  stage's colour-degree bound `Tile` (`tile_of_tri`; for an admissible colouring this is `Cherry`'s
  `5/6` count).  No hypothesis is used, not even sparsity of the leftover;
* **`CrossPairs`, `CrossThin`, `card_crossF_le_of_thin` — THE USABLE BOUND.**  What the first
  stage's analysis has to deliver is a *counting statement about its own output* ("at most `T` pairs
  of crossing leftover edges have a monochromatic complement"), and `card_crossF_le_of_thin` turns
  such a **total** bound — the shape a first-moment argument produces — into the **per-edge** bound
  the greedy engine consumes;
* **`FreshRel` = `Shares ∨ Sep ∨ Cross`, `card_freshRel_le` (`2D² + 2D + T`), `cross_greedy_extend`,
  `second_stage_of_cross` — THE COMPLETE SECOND STAGE.**  `Proper` (`A_{e,f,i}` = `B₁`),
  `NoAltCycle` (`B_D` = `B₂`) and `NoCrossFresh` (`C_{D,i}` = `B₃`) hold *simultaneously* with
  `2D² + 2D + T + 1` fresh colours, given only that the leftover has maximum degree `D` and at most
  `T` crossing pairs.  No probability anywhere;
* **`admissible_of_cross`, `CrossStageFamily`, `SlackFamily.of_cross`,
  `jsp_000140_main_of_cross_stage_family`** — the required theorem `jsp_000140_main` reduced to the
  published construction with **no probabilistic object in the second stage at all**;
* **`CrossThin.mono`, `second_stage_of_cross_wide`** — the fresh-colour cost is monotone in the
  crossing count, so a first stage with *no* crossing pair reproduces exactly the `2D² + 2D + 1`
  fresh colours of round 33.

**THE HONEST PRICE, AND THE CORRECTION TO ROUND 33.**  The deterministic route costs `T` extra fresh
colours over round 33 (`2D² + 2D + T + 1` instead of `2D² + 2D + 1`), where `T` is the crossing-pair
count of the first stage's output; the expected value of `CrossPairs c₀ L` is `Θ(n^{1-2δ})` for the
published `D = n^{1-δ}`, hence `o(n)`, so the budget is unaffected — but the hypothesis is a *new*
one, a density statement about the first stage, and it is **not** implied by round 33's
`StarStageFamily` (which asserts the `C_{D,i}`-avoidance of one particular colouring).  What this
round establishes is therefore: (i) the Lovász Local Lemma is **not needed anywhere** in the second
stage of either paper, and (ii) its content can be replaced by two counting statements about the
output of the first stage — the maximum degree `D` (already known from JM (IV) / BCDP Claim 4) and
the crossing-pair count `T`.

**Abandoned this round:** `StarStageFamily.of_cross` (`CrossStageFamily → StarStageFamily`).  It
was written, then *deleted as false*: `CrossThin c₀ L T` with `T` given cannot yield a colouring
with `2D² + 2D + 1` fresh colours, because the greedy genuinely needs the `T + 1` extra colours of
the crossing pairs it has to separate.  The two families are alternative hypotheses for the same
conclusion, not comparable ones.

## Status (round 33)

`lake build`: **OK** (3123 jobs).  `sorry`/`admit`: **0**.  `harness/score.py --strict-prize`
(invoked on `problems/JSP-000140/lean`):
`build_ok = true`, `partial_ok = true`, `prize_ready = false`,
`missing_theorems = ["jsp_000140_main"]`.

**ROUND 33 REMOVES ONE OF THE TWO BAD-EVENT FAMILIES OF THE PUBLISHED SECOND STAGE: `B_D` IS A
GREEDY MATTER, NOT A PROBABILISTIC ONE.**  Round 32 reduced the required theorem to
`StageFamily`, whose second-stage hypotheses are the properness (already deterministic, round 31)
plus the two bad-event families `B_D` (arXiv:2208.12563 §4 = `B₂` of arXiv:2207.02920 §12) and
`C_{D,i}` (`B₃`), both of which the two papers obtain from the symmetric **Lovász Local Lemma** —
which Mathlib does not contain.

New file `lean/JSPProblem/StarColour.lean` (576 lines, 13 public + 15 private declarations, zero
placeholders) proves that `B_D` never needed the local lemma:

* `Sep L e f` and `Sep.symm` — **two leftover edges separated by a third leftover edge**: the two
  *outer* edges of a path of three leftover edges `a – b – p – q` on four distinct vertices
  (`e = s(a,b)`, `f = s(p,q)`, and `s(b,p) ∈ L` or `s(q,a) ∈ L`).  In a 4-cycle of leftover edges
  these are the two diagonals;
* `StarProper c L` — a fresh colouring which is proper **and** injective on the separated pairs;
* **`noAltCycle_of_starProper` — THE REDUCTION.**  Properness makes neighbouring cycle edges
  differ, separation makes the diagonals differ, so **all four colours of a 4-cycle of leftover
  edges are pairwise distinct** and the cycle spans at least three colours: the bad event `B_D`
  cannot occur.  (Private helper `card_ge_four` does the counting; `cyc_ne` the distinctness of the
  adjacent edges of the cycle.);
* the counting: `NbL` (the leftover neighbours of a vertex, `card_NbL : (NbL L v).card = DegL L v`),
  `wit` (the witnesses `(y,z)` with `s(y,v) ∈ L`, `y,z ∉ e`, `z ≠ y`, `s(z,y) ∈ L`, counted through
  two nested images), `card_wit_le : |wit L e v| ≤ D²`, `sepF` (the leftover edges separated from
  `e`), **`card_sepF_le : |sepF L e| ≤ 2D²`**, `mem_wit`, `mem_sepF` (every separated edge is
  caught), plus `card_mem_e_le` (an edge has at most two endpoints);
* **`star_greedy` — THE GREEDY STAR COLOURING.**  A leftover graph of maximum degree `D` has a
  colouring with `2D² + 2D + 1` fresh colours which is proper and injective on the separated pairs.
  Each new edge avoids the colours of the at most `2D` edges it meets (as in round 31) and of the
  at most `2D²` edges separated from it;
* **`second_stage_of_sparseL` / `second_stage_of_leftover` — THE DETERMINISTIC HALF OF THE SECOND
  STAGE**: `Proper ∧ NoAltCycle` for `extendColDep` with `2Δ(L)² + 2Δ(L) + 1` fresh colours, no
  probability anywhere;
* **`admissible_of_star`**: a first-stage `Design` with leaf closure, extended properly on `L` and
  respecting the separated pairs, and avoiding `C_{D,i}`, is `Admissible`;
* `StarStageFamily`, `SlackFamily.of_star`, **`jsp_000140_main_of_star_stage_family`** — the
  required theorem `jsp_000140_main` reduced to the published construction with `NoAltCycle`
  **deleted from the hypotheses** (it follows from properness + the separated-pair condition by
  `noAltCycle_of_starProper`) and with the fresh-colour budget `2D²+2D+1` made explicit.  Only two
  probabilistic objects remain: the hypergraph matching of the first stage (JM Thm 4.2) and the
  single bad-event family `C_{D,i}` / `B₃` (the local lemma).

**THE HONEST PRICE.** `2D²` fresh colours rather than the `Θ(n^{1-δ})` of the papers, so the
deterministic exclusion of `B_D` is affordable only for `D = o(√n)`; `C_{D,i}` constrains *disjoint*
pairs of leftover edges and cannot be handled by any greedy rule, so the local lemma is still
needed for it.  What this round establishes is the precise division of labour between determinism
and probability inside phase 2 of arXiv:2208.12563 §4 = arXiv:2207.02920 §12.

**Abandoned this round:** the symmetric Lovász Local Lemma itself.  It was the round-32 blocker,
and the round-32 plan proposed it as the next target; the analysis of this round shows that half of
its application (the events `B_1`, `B_2`) is *not* a local-lemma application at all — `B_1` is the
greedy properness of round 31 and `B_2` is the greedy star colouring proved here — so the local
lemma is needed only for `C_{D,i}`.  Formalising it as a probability theory (Lovász's entropy /
Kolaitis–Miller counting proof) is a separate, much larger task and was not attempted; see
`policy.json` for the exact remaining formulation.

## Status (round 31)

`lake build`: **OK** (3121 jobs).  `sorry`/`admit`: **0**.  `harness/score.py --strict-prize`
(invoked on `problems/JSP-000140/lean`):
`partial_ok = true`, `prize_ready = false`, `missing_theorems = ["jsp_000140_main"]`.

**ROUND 31: THE SECOND STAGE IS CORRECTED AGAINST THE SOURCES, AND ITS DETERMINISTIC HALF IS
PROVED.**  New file `lean/JSPProblem/Second.lean` (528 lines, 26 declarations, zero placeholders).

### 1. The interface of round 30 was too strong — the papers were read this round

Round 30 stated the second stage as `Leftover.Rainbow` ("the leftover edges receive pairwise
distinct fresh colours inside every four-set") and named `Leftover.rainbow_of_sparse_leftover` as
the next lemma, attributing its existence to the symmetric local lemma.  arXiv:2207.02920 §12 and
arXiv:2208.12563 §4 (verbatim quotations in `acceptance.json`, key `literature_round31`) say
something different:

* the hypergraph matching of the first stage covers only `1 - n^{-δ}` of the edges (BCDP stops at
  `i_max = ⅙ n²(1-n^{-δ})`, §4), leaving a leftover graph `L` with `Θ(n^{2-δ})` edges;
* `L` is then coloured with `n^{1-δ}` fresh colours (JM) resp. `εn/2` fresh colours (BCDP), each
  fresh colour being **reused `Θ(n^{1-δ})` times**;
* what the local lemma has to exclude is (i) two *adjacent* leftover edges getting the same fresh
  colour — `A_{e,f,i}` (JM §4), `B₁` (BCDP §12); (ii) an *alternating* four-cycle inside `L` —
  `B_D`, `B₂`; (iii) a crossing leftover pair of equal fresh colour above a phase-1 monochromatic
  pair — `C_{D,i}`, `B₃`.  BCDP: "**Note that if none of the events in `ℬ` happens, then Phase 2
  gives us a `(4,5)`-coloring**".

So the published second stage is **proper** (every fresh colour class is a matching), not
rainbow: `Rainbow` would demand `|L| = Θ(n^{2-δ})` colours.

### 2. What is proved in `Second.lean`

* **`colorsOn_ext_card`** — the *exact* counting identity of the second stage (round 30 had only
  the `≤` version `Leftover.card_colorsOn_ext`);
* **`admissible_iff_second_stage`** — the verification condition is an **iff**: under `Extends`,
  `Admissible c ↔ SecondStage c₀ c L`, where `SecondStage` says that on every four-set the
  surviving first-stage colours plus the fresh colours number at least five.  Nothing else is
  needed, and nothing less will do; `secondStage_of_ext` shows round 30's `Compensate` route is an
  instance;
* `Shares`, `DegL`, `SparseL`, **`Proper`** — the graph vocabulary of the published second stage
  (`Proper c L` = every fresh colour class on `L` is a matching = no `A_{e,f,i}`);
* `card_shares_le`, `proper_of_sparseL` — at most `2D` leftover edges meet a given leftover edge,
  hence the greedy step;
* **`rainbow_of_sparse_leftover`** — **the named next lemma of round 30, proved in the published
  form**: a leftover graph of maximum degree `D` has a colouring by `2D+1` fresh colours in which
  two leftover edges sharing a vertex never get the same colour.  This is the *deterministic*
  half of the local lemma (`A_{e,f,i}` / `B₁`), needs no probability, and costs
  `2Δ(L)+1 = 2n^{1-δ}+1 = o(n)` fresh colours;
* `DegL_le`, **`DegL_leftover`**, `proper_of_leftover` — `Δ(leftover c) ≤ n-1` for every colouring,
  so the second stage *always* exists and costs at most `2n-1` fresh colours;
* `exists_four_adjacent`, **`Rainbow.proper`**, `Rainbow.proper_leftover` — two adjacent edges of
  `K_n` lie in a common four-set, so the round-30 interface is at least as strong as the published
  properness.

### 3. NOT proved this round (blockers)

* **the composition theorem** `Second.admissible_of_stage2`: `Design c₀` (round 28) + `Extends` +
  `Proper` + "no alternating four-cycle of leftover edges" + "no crossing equal-coloured leftover
  pair above a monochromatic first-stage pair" + leaf-closure `⇒ Admissible c`.  The case analysis
  is complete in writing (a violating `K₄` is a double-doubling; two doubled paths contradict
  `Criterion.Packed`, path + crossing contradict `NoBadFour`, two crossings form an alternating
  four-cycle) but the Lean proof is not;
* **`Rainbow_iff_injOn`**, the full sharpness statement (`Rainbow ↔ Set.InjOn c L` for `4 ≤ n`,
  hence `Rainbow` costs `|L|` colours).  Only the adjacent case is proved (`Rainbow.proper`);
  the general case needs the cardinality of a four-point endpoint set, which did not fit the
  round;
* **the symmetric local lemma itself** — (P2) and (P3) above.  Mathlib has no LLL.

## Status (round 42)

`lake build`: **OK** (3131 jobs).  `sorry`/`admit`: **0**.  `harness/score.py --strict-prize`
(invoked on `problems/JSP-000140/lean`):
`partial_ok = true`, `prize_ready = false`, `missing_theorems = ["jsp_000140_main"]`.

**ROUND 42: THE EDGE CENSUS OF `H` — THE THIRD AND LAST LOCAL DATUM — PLUS THE FIRST PER-VERTEX
CONSTRAINT ON A MATCHING.**  Rounds 40 and 41 computed the hypervertex degrees
(`Hyper.card_auxDeg_le`) and the four-set census (`Spoil.card_auxF_four`) of the auxiliary
hypergraph `H` of arXiv:2208.12563 §4, and retired maximality and maximality-with-avoidance *by
theorem*.  The third local datum — the number of hyperedges through a **given edge of `K_n`** — had
never been computed.  New file `lean/JSPProblem/Edge.lean` (715 lines, 37 declarations, zero
placeholders):

* `mem_cfgEdges_eq`, `eq_spk`, `eq_sqk`, `eq_sqp` — **the three roles of an edge in a
  configuration**: an edge is one of its two spokes or its opposite edge, and `Sym2.eq_iff` gives
  the two orientations.
* `card_auxF_spoke1`, `card_auxF_spoke2`, `card_auxF_opp` — **the census of each role**: exactly
  `2(n-2)k(k-1)` hyperedges of `H` have `s(a,b)` as their first spoke, as their second spoke, or as
  their opposite edge (two orientations of the endpoints, `n-2` free vertices, `k(k-1)` colour pairs;
  each proved by `Finset.card_bij` from the parameter finset `endsPair ×ˢ freeVerts ×ˢ colourPairs`).
* **`card_auxF_edge` — THE EDGE CENSUS OF `H`: EXACTLY `6(n-2)k(k-1)` HYPEREDGES OF `H` CONTAIN A
  GIVEN EDGE OF `K_n`.**  Together with the hypervertex degrees and the four-set census this is the
  **complete local census of `H`**: every finite first-moment or local-lemma argument on `H` needs
  only these three numbers.
* **`auxF_edge_double` — the census is consistent**: summed over the `C(n,2)` edges the local count
  returns `3·|E(H)|`, as it must, every hyperedge of `H` having three edges.
* `coverF F e` and the three classes `coverA`/`coverB`/`coverC` (`a`-central, `b`-central,
  leaf-only); **`coverF_role` — the role analysis**, `coverF_leaf`, `coverBC_leaf` (a covering member
  in which `a` is not the centre has `a` as a leaf and uses **both** colour slots at `a`),
  `coverA_slot`, `coverBC_mem`, `coverF_eq_three`.
* `SlotsAtF F v`, `slotPair g`, and **`card_SlotsAtF` — the per-vertex slot count**: the slots of a
  family at `v` number at most `|centF F v| + 2·|leafF F v|` — the first constraint on a matching in
  `H` that goes beyond the global `5|F| ≤ nk` of `Fam.slots_countF`.
* **`sum_slots_at_card` — `Σ_v (|centF F v| + 2·|leafF F v|) = 5·|F|`**, the per-vertex form of
  `Fam.card_SlotsF`, with `sum_centreF_card`, `card_leafF`, `sum_leafF_card` as the three counting
  ingredients.

**STILL MISSING** (unchanged in substance): the existence of the near-perfect matching in `H`
(`Partial.FamGreedyFamily`) — a Rödl-nibble / random-triangle-removal existence theorem that Mathlib
cannot host.  **Next round's first item** (drafted this round, machinery in the build): the per-vertex
*budget* `|centF F v| + 2·|leafF F v| ≤ k` (which needs `SlotFree` applied one vertex at a time)
and then the per-edge bound `3·|coverF F (s(a,b))| ≤ 2k` (the same disjointness summed over the two
endpoints of the edge).

## Status (round 30)


`lake build`: **OK** (3120 jobs).  `sorry`/`admit`: **0**.  `harness/score.py --strict-prize`
(invoked on `problems/JSP-000140/lean`):
`partial_ok = true`, `prize_ready = false`, `missing_theorems = ["jsp_000140_main"]`.

**ROUND 30: NEW ATTACK FAMILY — THE SECOND STAGE OF THE PUBLISHED CONSTRUCTION.**  Round 29 encoded
the published first stage as labelled triangles, but its hypothesis `Triangles.TriFamily` demanded
`Triangles.Covers`, i.e. a **complete** covering of every edge.  That is strictly stronger than
arXiv:2208.12563 §4 (= arXiv:2207.02920), where the hypergraph matching covers only `1 - o(1)` of the
edges and the **leftover graph** `L` is coloured in a *second stage* with `n^{1-δ}` extra colours by a
symmetric local lemma.  The new file `lean/JSPProblem/Leftover.lean` (489 lines, 32 public + 4
private declarations, zero placeholders) formalises that second stage as an exact, **proved**
interface — no hypergraph, no probability, no local lemma:

* `leftover c`, `Covered`, `covers_iff_leftover_eq_empty`, `card_lost`, `lost_four` — the leftover
  graph of a partial construction, the equivalence "a complete covering is the empty leftover" (so
  round 29 is the `K = 0` case), and the accounting of the loss.
* `Extends` (first-stage colours kept off `L`, fresh colours on `L`), `Rainbow` (leftover colours
  pairwise distinct inside every four-set) and `Compensate` (the weakest interface condition: fresh
  colours ≥ dying first-stage colours on every four-set), with `Compensate.of_rainbow`.
* `card_colorsOn_ext` — **the counting identity of the second stage**: on a four-set the extension
  has at least *(first-stage colours on the covered edges) + (fresh colours on the leftover edges)*,
  the two being disjoint palettes, so the second stage never destroys colours.
* `admissible_of_covered`, **`admissible_of_ext`** (the published form: an admissible first stage +
  fresh colours that compensate ⇒ admissible) and `admissible_of_ext_rainbow`.
* `freshCol`, `extendColDep`, `Extends_extendColDep`, `admissible_of_extendColDep`, `rainbow_of_index`,
  **`admissible_of_matching_leftover`** — the second stage as a function; in particular *if the
  leftover is a matching the second stage is complete and needs no local lemma*.
* `ExtFamily`, `SlackFamily.of_ext`, **`jsp_000140_main_of_ext_family`** — the required theorem
  `jsp_000140_main` reduced to the published statement **in its faithful two-stage form**, and
  `ExtFamily_of_TriFamily` showing round 29 is an instance of it.

**STILL MISSING** (unchanged in substance): the existence of the pair `(c₀, c)` — the probabilistic
first stage (hypergraph matching) together with the symmetric local lemma that colours the leftover
graph rainbowly with `n^{1-δ}` fresh colours.  That is `Leftover.ExtFamily`, the single remaining
prize hypothesis.  The next concrete lemma is named in
`discovery/JSP-000140/policy.json`: `Leftover.rainbow_of_sparse_leftover` for leftover graphs of
maximum degree `D` (`D ≤ 1` is proved this round).

*Note on the gate*: `harness/score.py` only checks that a theorem **named** `jsp_000140_main` is
declared.  Renaming one of the reductions to that name would flip `prize_ready` without proving
anything, and `ACCEPTANCE.md` requires `jsp_000140_main` to be the complete catalog statement
`FiveSixth EG`; this was deliberately **not** done.

## Status (round 24)

`lake build`: **OK**.  `sorry`/`admit`: **0**.  `harness/score.py --strict-prize`
(invoked on `problems/JSP-000140/lean`):
`partial_ok = true`, `prize_ready = false`, `missing_theorems = ["jsp_000140_main"]`.

**ROUND 24 CHANGES THE ATTACK FAMILY TWICE: the exhaustive search becomes a PROPAGATOR (which
makes the *upper* bound movable at all), and the extremal structure gets its missing PER-VERTEX
half.**

### 1. The search of rounds 18–22 was only able to *refute*; now it finds

Rounds 18–22 built a complete depth-first search whose only pruning test is "the `K₄` completed by
this slot must span five colours" — a test that can only fire at the **six-th** edge of a clique.
Round 24 adds the three consequences of admissibility that `Cherry.lean` has *already proved*, so
that they can be used as propagations instead of a leaf test (`discovery/JSP-000140/eg6_struct.c`):

* colour-degree `≤ 2` at every vertex (`Counting.nbrsIn_card_le_two`);
* if `x – a – b` is a `j`-path then the leaf edge `{x,b}` has a colour `≠ j` and **neither `x` nor
  `b` has any other neighbour in that colour** (`Cherry.nb_eq_singleton_of_cherry`), maintained
  incrementally as a lock on the two endpoints;
* two two-edge paths never share a pair (`Rigidity.pathSet_sub_inter`), i.e. the leaf edge of a path
  is registered once.

All three are consequences of `Admissible`, so the search still decides exactly the same question;
with a random colour order at every node and restarts it becomes a **witness finder**:

| instance | nodes | note |
| --- | --- | --- |
| `n = 6, k = 5` | 254 | `Tables.sixCol`, the 1-factorisation |
| `n = 7, k = 6` | 42 429 | **the round-21 certificate** (13 301 689 nodes before) |
| `n = 8, k = 7` | 751 660 | |
| `n = 9, k = 8` | 127 957 | `Tables.nineCol` of round 22 |
| `n = 10, k = 9` | 1 544 452 | **new** `Tables.tenCol`, `f(10,4,5) ≤ 9` |
| `n = 11, k = 10` | 3 920 144 | **new** `Tables.elevenCol`, `f(11,4,5) ≤ 10` |

(`discovery/JSP-000140/eg5_localsearch.c`, a WalkSAT on the same constraint system, was measured and
**rejected**: it cannot even rediscover the *known* 8-colouring of `K₉`.)

Consequences, all in the default build:

* `Tables.admissible_tenCol`, `Tables.EG_ten_le` — an admissible **9-colouring of `K₁₀`**, verified
  by `native_decide` over all `C(10,4) = 210` four-element vertex sets.  This is the first even
  order at which this development certifies fewer than `n` colours (before: `f(10,4,5) ≤ n + 1`);
* `Tables.admissible_elevenCol`, `Tables.EG_eleven_le` — an admissible **10-colouring of `K₁₁`**
  (`C(11,4) = 330` four-element vertex sets), improving the round-robin bound `f ≤ n`;
* `Main.f_ten_between_eight_and_nine`, `Main.f_eleven_between_nine_and_ten`,
  `Main.two_new_intervals` — `8 ≤ f(10,4,5) ≤ 9` and `9 ≤ f(11,4,5) ≤ 10`, both of width one.

### 2. New file `lean/JSPProblem/Star.lean` — the local profile of an extremal colouring

Everything known about the extremal case (rounds 13–15) was *global*: the two-edge paths form a
Steiner triple system (`Rigidity.tight_pathFinset_is_STS`), every colour class spans `V`
(`Rigidity.tight_covers`).  `Star.lean` records what a **vertex** sees — the constraints a
construction of such a colouring must satisfy:

* `Star.sum_nb_star` — **the star identity**: `∑_i |nb c i v| = n - 1` for **every** colouring and
  every `v` (the per-vertex handshaking lemma; the colour classes restricted to the star of `v`
  partition its `n-1` edges).  No admissibility needed;
* `Star.star_centred_colours` — under "every colour class spans `V`", the number of colours in which
  `v` is the **centre** of a two-edge path is `n - 1 - k`;
* `Star.tight_star_centre` — in the extremal case `6k = 5(n-1)`, **every vertex is the centre of
  exactly `(n-1)/6` two-edge paths**;
* `Star.tight_star_oneB` — `v` has colour-degree `1` in exactly `2(n-1)/3` colours;
* `Star.tight_blocks_through` — **every vertex lies in exactly `(n-1)/2` blocks** of the Steiner
  triple system (the per-vertex form of `Rigidity.sum_card_filter_pairIn`);
* `Main.star_centre_is_one_third_of_blocks`, `Main.star_profile_at_thirteen` — the centre function
  is therefore **`1/3`-balanced at every point**, and for the first order at which the sharp constant
  `5/6` can be attained at all (`n ≡ 1 (mod 6)` by `Rigidity.tight_mod6`, `n ≥ 13` by
  `Extremal.tight_ge_thirteen`): a hypothetical admissible 10-colouring of `K₁₃` must have every
  vertex the centre of exactly `2` of the `26` paths and colour-degree `1` in exactly `8` of the
  `10` colours.  `Main.extremal_at_thirteen_is_open` states the corresponding open question.

### 3. NOT proved this round (blockers B4, B5, B7)

* **`f(10,4,5) = 8` or `9`?** and **`f(11,4,5) = 9` or `10`?** — closing either needs an exhaustion
  of "no admissible 8-colouring of `K₁₀`" / "no admissible 9-colouring of `K₁₁`"; the randomised
  search did not finish the tree in 900–1200 s of wall clock, and such a certificate would cost as
  much as `Nine.certD_nine_six` (≈ 80 CPU-minutes, off the default build path).
* **Is `K₁₃` admissible with ten colours?** (`Main.extremal_at_thirteen_is_open`.)  This is the
  first order at which the counting bound `5(n-1)/6 = 10` could be attained; the search found no
  such colouring in 1500 s.  Note that at every order found so far (`n = 7, 8, 9, 10, 11`) the
  search finds nothing **at** the counting bound, which is direct computational evidence that the
  `o(n)` of the headline is necessary.
* **B7** — the single-edge side of the local profile: `Star.tight_star_oneB` plus
  `Star.tight_blocks_through` give "exactly `(n-1)/3` of the `2(n-1)/3` colours in which `v` has
  colour-degree `1` are isolated single edges"; the identification with `Singles.singleFinset` is
  not yet formalised.
* **The single remaining prize hypothesis is unchanged**: `Slack.jsp_000140_main_of_STS_slack_family`
  — for every `δ > 0` and all large `m ≡ 1 (mod 6)` an admissible `k`-colouring of `K_m` with
  `6k ≤ 5(m-1) + δm`.  This is the **probabilistic** construction of arXiv:2207.02920 (random
  triangle removal + differential equation method); there is no explicit colouring in the
  literature to formalise, and round 24 confirms that no *explicit* construction is reachable by
  search: nothing is found at the counting bound for any `n ≥ 7`.

## Status (round 22)

`lake build`: **OK**.  `sorry`/`admit`: **0**.  `harness/score.py --strict-prize`
(invoked on `problems/JSP-000140/lean`):
`partial_ok = true`, `prize_ready = false`, `missing_theorems = ["jsp_000140_main"]`.

**ROUND 22 CLOSES BLOCKER B2′ OF ROUND 21 — BOTH OF ITS NAMED OPTIMISATIONS ARE PROVED
EQUIVALENT TO `Admissible` AND APPLIED — AND OBTAINS `f(9,4,5) = 8`, THE THIRD EXACT VALUE OF
`f(n,4,5)` ABOVE THE COUNTING BOUND.**

### 1. The two bridges round 21 said were missing (`JSPProblem/QuadEnum.lean`, 133 lines, 7 declarations, zero `sorry`)

Blocker B2′ of round 21 said the two concrete optimisations of the pruning test "both need a proved
equivalence to `Admissible`".  Those equivalences are now proved.

* **`mem_quadsOf_of_incQuad`** — every increasing quadruple occurs in the list `quadsOf n`, and
  **`incQuad_of_mem_quadsOf`** — conversely: the `K₄`s of `quadsOf n` are exactly the increasing
  quadruples, so the search really tests every `K₄` of `K_n`;
* **`exists_quadSet_of_card` / `exists_mem_quadsOf_of_card`** — **every four-element `Finset` of
  `Verts n` is the vertex set of an increasing quadruple of `quadsOf n`**, proved by sorting the
  set (`Finset.sort` of Mathlib `Data/Finset/Sort.lean`, the *same* sorting tool the vendored
  Mathlib uses for `Finset.min'`/`max'`) and taking the four elements of the resulting four-element
  list.  This is the statement that identifies the `Finset`-world of `Admissible` with the
  quadruple-world of the search;
* **`admissible_iff_all_quads`** — **`Admissible c` iff every `K₄` of `quadsOf n` spans at least
  five colours** (in the form `decide (5 ≤ (quadColors c q).toFinset.card) = true`).

### 2. The leaf-free search (`JSPProblem/LeafFree.lean`, 523 lines, 34 declarations, zero `sorry`)

`VertexSearch.searchAuxC` tests, **at every leaf**, `decide (Admissible (tabOfC n dflt M))` — a
predicate that quantifies over **all `2^9` four-element `Finset`s** of `K₉` and builds a
`Finset.image` for each of them, once per complete assignment of the 36 slots (21 286 763 of them
for the certificate of round 22).  **All of it is redundant**: every `K₄` is *completed* at the
position `slotQuadC n q` — the largest of its six slots — and `slotQuadC n q < C(n,2)`
(`slotQuadC_lt`), so every `K₄` has already been tested, and has already passed, by the time the
search reaches the end of the table.

New in this file:

* `searchAuxD` — `searchAuxC` with the leaf replaced by `true`, and with `dflt`, `tabOfC` and
  `Admissible` removed from the search program altogether;
* **`QPassedC M t`** — the new invariant, "every `K₄` completed below the position `t` has already
  passed the pruning test", with `QPassedC_update` (maintained by colouring the current slot) and
  `QPassedC_skip` (survives the move from vertex `b` to `b+1`);
* **`quadOKC_test`** — the pruning test *read backwards*: if a total colouring `c` agrees with the
  partial colouring `M` on the six edges of a `K₄` and the `K₄` passes the test, then `c` gives it
  at least five colours (through `collect6_eq_quadColors` and `quadColors_toFinset`);
* **`admissible_of_quadsOKC`** — **the leaf lemma**: if `c` agrees with `M` on every edge and every
  `K₄` passes the test on `M`, then `Admissible c`;
* `mem_quadGroupsC_slotQuadC` — **the group table of the vertex-addition search is complete** (every
  `K₄` is in the group of the position at which it is completed), the other half of what the leaf
  was computing;
* **`searchAuxD_iff` — THE COMPLETENESS THEOREM OF THE LEAF-FREE SEARCH**: the search returns
  `true` on the partial colouring `M` at the position `posC b a` **iff some admissible colouring
  of `K_n` agrees with `M` on every edge below that position**; `hasAdmissibleD_iff`,
  `EG_ge_of_certD` — the lower-bound engine;
* `certD_seven_six`, `certD_seven_seven`, `EG_seven_leaffree` — the certificate of round 21
  re-derived by the new engine (`f(7,4,5) = 7` from the leaf-free search).

### 3. The cheap distinctness count (`JSPProblem/Distinct.lean`, 109 lines, 11 declarations, zero `sorry`)

The test `decide (5 ≤ (l.toFinset : Finset (Fin k)).card)` costs **six red-black-tree insertions per
`K₄` test** in compiled code, and the search performs 269 824 034 of them for the `K₉` certificate.
`insAll l []` computes the same number as a `List` length:

* `insNew`, `insAll`, `insNew_mem`, `insNew_nodup`, `insAll_mem`, `insAll_nodup`,
  `insAll_nil_toFinset`, **`ndist_eq_card` (`ndist l = (l.toFinset).card`)** and
  **`decide_ndist` (the two `decide`s agree)**.

`FastSearch.quadOK` and `VertexSearch.quadOKC` now use `ndist`; every existing certificate still
verifies (the two `quadOK_of` proofs were adapted in one line each).  **Measured effect on the
"no admissible 6-colouring of `K₈`" certificate, which is the same 38 654-node search as `K₇`:
113 s wall / 22 s CPU before, 17 s wall / 5.4 s CPU after** — a factor of 4, and this is what brings
the 21 286 763-node `K₉` certificate inside `lake build`.

### 4. The third value above the counting bound: `f(9,4,5) = 8` (in `JSPProblem/Nine.lean`)

**The `K₉` certificate is deliberately kept OUT of the default build.**  The search visits
21 286 763 nodes and 269 824 034 `K₄` tests and `native_decide` needs of the order of **80 CPU
minutes** — 4 h 12 min of wall clock in round 22 with the harness host at load 45–50 on 8 cores.
The run *did* reach the end of the certificate in round 22 (it failed only on a name-resolution
slip in the statement that follows it), so the `false` answer is confirmed; but putting it in the
default build would make every *rebuild* cost that much, so the certificate and its consequences
live in `lean/JSPProblem/Nine.lean`, which is not imported by `JSPProblem.lean`:

```sh
cd lean && lake build JSPProblem.Nine      # re-verify (~80 CPU-minutes)
```

What is in the default build is the cheap half: `Tables.EG_nine_le` (`f(9,4,5) ≤ 8`) together
with the counting bound gives `Main.f_nine_between_seven_and_eight : 7 ≤ f(9,4,5) ≤ 8`.


`Tables.lean` gains the colouring the search found, written down as a literal table and certified
by `native_decide` over all `C(9,4) = 126` four-element vertex sets — independently of the search:

* `nineCol`, **`admissible_nineCol`**, `EG_nine_le : f(9,4,5) ≤ 8`, `nineCol_some_tight` (some `K₄`
  spans exactly five colours);
* `Main.f_nine_between_seven_and_eight : 7 ≤ f(9,4,5) ≤ 8` (counting bound and `EG_nine_le`);
* in `Nine.lean`: **`certD_nine_six : hasAdmissibleD 9 6 = false`** (no admissible 7-colouring of
  `K₉`), **`EG_nine : EG 9 = 8`**, `counting_bound_strict_at_nine` (`8 > 7 = ⌈5·8/6⌉`),
  `EG_nine_above_five_sixth` (`5·8 < 6·8`, a strict improvement of the sharp `5/6` constant at a
  concrete order);
* `Main.first_six_values` — `f(4) = f(5) = f(6) = 5`, `f(7) = f(8) = 7`;
  `Main.admissible_is_all_quads`, `Main.every_four_set_is_tested`,
  `Main.EG_seven_two_engines` (the two engines agree on `f(7,4,5)`).

`f(9,4,5) = 8 > ⌈5(9-1)/6⌉ = 7` is the **third** order at which the Erdős–Gyárfás function exceeds
the counting bound, and it is the third independent confirmation (after round 16's failure of
`AG(2,3)` and round 13's characterisation by Steiner triple systems) that the **design-theoretic
route to the extremal family does not exist at `n = 9`**: the extremal colouring would have to have
`⌈5(9-1)/6⌉ = 7` colours, and there is none.

### 5. NOT proved this round (blocker B3', now a pure constant-factor question)

* **`hasAdmissibleD 10 6 = false`** — no admissible 7-colouring of `K_{10}`; measured in C with the
  vertex-addition order and no leaf test: the search fails *inside* `K₉`, i.e. the same
  21 286 763 nodes, so nothing new is required, only another ~80 CPU-minute evaluation.  The next
  orders are `f(10,4,5)`, where the counting bound `⌈5·9/6⌉ = 8` would be attained if an admissible
  8-colouring of `K_{10}` exists (the search at eight colours is out of reach in C: > 300 s), and
  then, for `n = 11, 12, …`, the `o(n)` question.
* **A cheaper evaluator.**  `native_decide` evaluates in the kernel/`Meta.reduce` interpreter, not
  in compiled code; a 4x factor was recovered inside Lean (the `Finset`-free test of
  `Distinct.lean`), but the remaining 21e6-node search would be a few minutes in *compiled* code.
  Formalising "the search returns the same answer when evaluated by the C evaluator" is a separate
  (large) project; a cheaper route would be to make the search's own work per node smaller (an
  array instead of `List.getD` for the group table).
* **The upper half of `jsp_000140_main` is untouched** — it needs the probabilistic construction
  of arXiv:2207.02920 (blocker "SINGLE REMAINING PRIZE HYPOTHESIS", unchanged).

## Status (round 21)

`lake build`: **OK**.  `sorry`/`admit`: **0**.  `harness/score.py --strict-prize`
(invoked on `problems/JSP-000140/lean`):
`partial_ok = true`, `prize_ready = false`, `missing_theorems = ["jsp_000140_main"]`.

**ROUND 21 CHANGES THE *ORDER* OF THE SEARCH AND OBTAINS THE FIRST TWO EXACT VALUES OF
`f(n,4,5)` THAT EXCEED THE COUNTING BOUND: `f(7,4,5) = f(8,4,5) = 7`.**

### 1. The diagnosis: the search order, not the search

Blocker **B2** of round 20 ("the certificate `hasAdmissibleSym 7 5 = false` is a pure
constant-factor question") is **closed**, and the constant factor was **344**, not a few
percent.  The searches of `Search.lean` and `FastSearch.lean` fill the slots `a*n + b` in
*lexicographic* order — all the edges at vertex `0`, then all the edges at vertex `1`, … — so
the first `K₄` is completed only after `n-1 = 6` of the `21` edges have been coloured, and the
first **four** only after `13`.  The pruning therefore fires extremely late.

New file `lean/JSPProblem/VertexSearch.lean` (719 lines, 60 declarations, zero `sorry`)
renumbers the slots by the **larger** endpoint: the position of the edge `{a,b}` (`a < b`) is
`tri b + a` with `tri b = C(b,2)`, so the edge order is

    (0,1), (0,2), (1,2), (0,3), (1,3), (2,3), (0,4), … , (n-2,n-1)

(the triangle on `{0,1,2}` first, then the star from vertex `3`, then from vertex `4`, …).
Every `K₄` is now completed as early as it possibly can be: the first after **six** edges, the
first four after **ten**.  Measured with `discovery/JSP-000140/eg3_vertex_order_nodes.py`,
which reproduces both orders:

| order | search | nodes |
| --- | --- | --- |
| lexicographic (`FastSearch.lean`) | `K₇`, six colours | **13 301 689** |
| vertex-addition (`VertexSearch.lean`) | `K₇`, six colours | **38 654** |

13 301 689 is exactly the figure round 19 measured in Python, so the two numbers are directly
comparable.  The new certificate is `native_decide`-able in seconds.

### 2. What is proved

* `tri`, `nEdgeC`, `slotC`, `slotOfC`, `posC`, `fuelC` — the numbering, with `tri_succ`
  (`tri b + b = tri (b+1)`), `tri_mono`, `slotC_inj`, `slotOfC_inj`, `slotOfC_lt`,
  `slotOfC_eq_slotC_iff`, `posC_succ`, `posC_skip`: the vertex-addition numbering is a
  **bijection `[0, C(n,2)) → {edges of K_n}`**, and the state `(b,a)` of the search is exactly
  the position `posC b a = tri b + min a b`;
* `quadSlotsC`, `slotQuadC`, `quadOKC`, `allOKC`, `quadOKC_of`, `quadGroupsC` — the pruning
  test and the group table in the new numbering;
* **`searchAuxC_iff` — THE COMPLETENESS THEOREM**: the search returns `true` on the partial
  colouring `M` at the position `posC b a` **iff some admissible colouring of `K_n` agrees with
  `M` on every edge below that position**.  It is proved by induction on the fuel and assumes
  nothing about the search; the symmetry step uses the round-19 `admissible_swapCol` /
  `swapCol_apply_of_small` unchanged.  Because the new numbering is dense, the two awkward
  features of the old proof disappear: there is no "slot carrying no edge" to skip and the
  `K₄` completed at a position is determined by the position alone;
* `hasAdmissibleC_iff`, `EG_ge_of_certC` — the lower-bound engine;
* **`certC_seven_six : hasAdmissibleC 7 5 = false`** (`native_decide`) — **no admissible
  six-colouring of `K₇`**; **`certC_seven_seven`** and **`certC_six_six`** are the
  cross-checks on the other side (the search does find the round-robin colouring of `K₇` and
  an admissible six-colouring of `K₆`, so it is not vacuously false);
* **`VertexSearch.EG_seven : f(7,4,5) = 7`** — `certC_seven_six` for the lower bound,
  `Construction.EG_le_sumCol 7` for the upper bound.  This is the **first exact value of the
  Erdős–Gyárfás function in this development that exceeds the counting bound**
  `5(n-1)/6 = 5`;
* `Main.certC_eight_six`, **`Main.EG_eight : f(8,4,5) = 7`** (lower bound from the same
  certificate, upper bound from the ghost colouring, `3 ∤ 7`);
* `Main.first_above_counting` (`f(4) = f(5) = f(6) = 5`, `f(7) = f(8) = 7`),
  `Main.counting_bound_strict` (`⌈5(n-1)/6⌉ < f(n,4,5)` at `n = 7, 8`),
  `Main.the_o_n_term_is_needed` (the excess over `5n/6` is `0` at `n = 6`, `n/6` at `n = 7`,
  `n/24` at `n = 8`), `Main.catalogue_estimate_at_seven` (the catalog estimate holds at
  `n = 7` **with equality**), and `Restriction.EG_ge_seven_of_seven` (`f(n,4,5) ≥ 7` for every
  `n ≥ 7`).

### 3. NOT proved this round (blocker B2', now a pure constant-factor question again)

* **`hasAdmissibleC 9 6 = false`** — no admissible **seven**-colouring of `K₉`, which with the
  admissible eight-colouring the search itself produces would give `f(9,4,5) = 8`.  Measured
  in C with the vertex-addition order: **21 286 763 nodes, 4.85 s**.  In Lean it did not finish
  in 30 minutes: the per-leaf cost is dominated by `decide (Admissible (tabOfC …))`, which
  quantifies over all `2^9` four-element `Finset`s, and by `collect6`, which allocates a
  `List` and builds a `Finset (Fin k)` per `K₄`.  Replacing the leaf test by
  `allOKC (tabOfC …) (quadsOf n)` (35 clique tests instead of 512 set enumerations) and
  replacing `l.toFinset` by a `List`-level distinctness count are the two concrete
  optimisations that would close this; both need a proved equivalence to `Admissible`.
* The same certificate for `n = 10, 11` (identical node count — the search fails inside `K₇`).

## Status (round 20)

`lake build`: **OK**.  `sorry`/`admit`: **0**.  `harness/score.py --strict-prize`
(invoked on `problems/JSP-000140/lean`):
`partial_ok = true`, `prize_ready = false`, `missing_theorems = ["jsp_000140_main"]`.

**ROUND 20 CLOSES BLOCKER B1: THE COMPLETENESS THEOREM OF THE SYMMETRY-REDUCED SEARCH IS PROVED,
AND A SECOND, FASTER SEARCH IS PROVED COMPLETE AS WELL.**

### 1. `FastSearch.searchAuxS_iff` — the completeness theorem (blocker B1 of round 19, closed)

```lean
FastSearch.searchAuxS_iff {n k : ℕ} (dflt : Fin k) {M : PTab k} {u d fuel : ℕ}
    (hnn : n * n ≤ d + fuel) (hspec : PSpec n M u d) :
    searchAuxS n dflt M u d fuel = true ↔
      ∃ c : Col n k, (∀ e, OffDiag e → slotOf e < d → M (slotOf e) = some (c e)) ∧ Admissible c
```

The search returns `true` on the partial colouring `M` — which by `PInv` uses exactly the
colours `0, …, u-1` — at level `d` **iff some admissible colouring of `K_n` extends `M` on the
edges of the slots `< d`**.  It is proved by induction on the fuel and assumes nothing whatever
about the search.  Three structural steps:

* **the base case** (`fuel = 0`, or `n*n ≤ d`): in one direction the witness is `tabOf` itself,
  and in the other the prefix agreement forces `tabOf n dflt M e = c e` for every edge, because
  `slotOf e < n*n ≤ d`.  The new lemma `tabOf_agrees` is what makes this work, and the new
  lemma `meaningfulSlot_slotOf` (every edge occupies a meaningful slot) is what makes `PFilled`
  usable at all;
* **the symmetry step**: an admissible extension whose colour at the current slot *exceeds* `u`
  is brought into the explored range by the transposition of `u` with that colour.
  `admissible_swapCol` (round 19) says the relabelling keeps it admissible, `swapCol_apply_of_small`
  says it does not disturb the colours already entered (because `PInv` says they are all `< u`),
  and the colour of the current edge becomes exactly `u`;
* **the skip step** for slots carrying no edge (`PFilled_skip`, `slot_lt_of_not_meaningfulS`).

Two statements that look plausible and are **false** were removed in the process: "a partial
colouring is injective on the meaningful slots" (a table may assign the same colour in two
slots), and the converse of `mem_groupsOf`.

The fuel hypothesis `n * n ≤ d + fuel` is *not* in the round-19 draft and is **necessary**:
without it the base case `decide (Admissible (tabOf n dflt M))` need not have an extension,
because `tabOf` fills the unfilled slots with the default colour.

### 2. The lower-bound engine, and the round-18 certificates re-derived

`FastSearch.hasAdmissibleSym_iff` and `FastSearch.EG_ge_of_certSym` are the engine of round 18,
now driven by the new search.  Five `native_decide` certificates go through it
(`certSym_four_four`, `certSym_five_four`, `certSym_six_four`, `certSym_six_five`,
`certG_six_four`, `certG_five_three`): no admissible 4-colouring of `K₄`, `K₅` or `K₆`, and `K₆`
*does* have an admissible 5-colouring, so `Main.EG_six_by_search` pins `f(6,4,5) = 5` with the
search on **both** sides.  `Main.small_values_by_sym_search` re-derives
`f(4,4,5) = f(5,4,5) = f(6,4,5) = 5`, and `Main.the_searches_agree` cross-checks the two
independent search programs of `Search.lean` and `FastSearch.lean` against each other.

### 3. A second, faster search — `searchAuxSg` — also proved complete

`searchAuxSg` takes the table of the `K₄`s completed by each slot as an argument
(`fourGroupsS`), so that the filter over the `n⁴` quadruples which `searchAuxS` performs **at
every search node** is performed **once**.  `searchAuxSg_iff` is the completeness theorem of
this search, in the same shape, with `mem_fourGroupsS` for the soundness of the table; and
`hasAdmissibleSymG_iff` / `EG_ge_of_certG` are its engine.

**NOT proved this round (blocker B2): the certificate `hasAdmissibleSymG 7 5 = false`** — no
admissible 6-colouring of `K₇` — which with `Construction.EG_le_sumCol 7` would give the exact
value `f(7,4,5) = 7`, the first order at which `f` exceeds the counting bound `5(n-1)/6 = 5`.
Measured in Python this search is 13 301 689 nodes; the Lean search is now proved correct and
its constant factor reduced, but the host is saturated (load 46 on 8 cores, the other forever
loops), so the evaluation did not finish this round.  The remaining work on B2 is therefore
purely a constant-factor question: the recursion still walks all `n²` slots although only the
`n(n-1)/2` meaningful ones carry an edge.

## Status (round 19)

`lake build`: **OK**.  `sorry`/`admit`: **0**.  `harness/score.py --strict-prize`
(invoked on `problems/JSP-000140/lean`):
`partial_ok = true`, `prize_ready = false`, `missing_theorems = ["jsp_000140_main"]`.

**ROUND 19 REPLACES THE VERIFIED SEARCH OF ROUND 18 BY A FAST, SYMMETRY-REDUCED ONE AND PROVES
EVERYTHING ABOUT IT EXCEPT ITS COMPLETENESS THEOREM.**

New file `lean/JSPProblem/FastSearch.lean` (611 lines, 60 declarations, zero `sorry`).  Three
changes make the search of `Search.lean` fast enough to reach `n = 7`, and all of the
corresponding mathematics is formalised:

* the four-cliques of `K_n` are enumerated as an **explicit list of increasing quadruples**
  (`Quad`, `incQuad`, `quadsOf`, `groupsOf`, `mem_groupsOf`) instead of by filtering the universe
  of four-element finsets — `Search.fourSets` enumerates `2^(n²)` candidates, i.e. `2^49` for
  `n = 7`, which is exactly why the round-18 search could not certify anything beyond `n = 5`;
* the pruning test works on a **list of six colours** (`collect6`, `quadOK`, `allOK`), and a `K₄`
  which is not complete yet is not tested at all;
* the search branches only over **the colours already used and the next new one**
  (`allowedColors k u = {0, …, u}`), the *first-occurrence* rule, i.e. the colour-permutation
  symmetry reduction, with the invariant `PInv` ("the colours used are exactly `0, …, u-1`") and
  `PFilled` ("the meaningful slots filled are exactly those below `d`").

The correspondence between the combinatorial and the `Finset` world — the part that any use of the
search has to pay for — is proved:

* **`quadEdges_eq`**: the six edges of an increasing quadruple are **exactly** the edges of the
  complete graph on its four vertices, `edgeFinset (quadSet q) = quadEdges q`;
* **`quadColors_toFinset`**: the six colours of a `K₄` (as a *list*) are exactly
  `colorsOn c (quadSet q)`; hence **`quad_ok_of_admissible`**: a `K₄` of an admissible colouring
  spans five colours in the form the search tests;
* **`quadOK_of`**: the pruning test is **sound** — a partial colouring agreeing with a total
  colouring on all slots `≤ d` passes the test for every `K₄` completed at `d`;
* **`admissible_swapCol`** (with `swp`, `swp_involutive`, `card_colorsOn_swapCol`): relabelling the
  palette by a transposition of two colours **preserves admissibility** — the ingredient the
  completeness proof needs for the symmetry step;
* the invariants and their preservation: `PInv_update`, `PFilled_update`, `PFilled_skip`,
  `PSpec_update`.

The search itself (`tabOf`, **`searchAuxS`**, `hasAdmissibleSym`) is computable, and
`native_decide` settles `hasAdmissibleSym 4 3 = false` and `hasAdmissibleSym 5 3 = false`: the new
engine reproduces the two certificates of round 18.  Measured in Python
(`discovery/JSP-000140/eg3_symmetry_nodes2.py`): *no admissible 6-colouring of `K₇` exists* (13 301 689
nodes), so with `Construction.EG_le_sumCol 7` one gets `f(7,4,5) = 7` — **the first order at which
`f` exceeds the counting bound `5(n-1)/6 = 5`**; `n = 8` with six colours needs `> 7.5·10⁷` nodes in
900 s.

**NOT proved this round: the completeness theorem `searchAuxS_iff`** (blocker B1 in
`discovery/JSP-000140/policy.json`) — that the symmetry-reduced search returns `true` iff some
admissible colouring extends the partial one.  The induction on the fuel is drafted and every
ingredient it needs is in the file; what remains is ~8 tactic-level errors in the `succ` case, all
of one mechanical kind (turning `decide (Admissible c) = true` into `Admissible c`; rewriting inside
an equation rather than in a goal).  Without it no `native_decide` certificate may be used, so the
lower-bound engine `hasAdmissibleSym_iff` / `EG_ge_of_certSym` cannot be stated yet, and
`f(7,4,5) = 7` cannot be concluded.

## Status (round 18)

`lake build`: **OK**.  `sorry`/`admit`: **0**.  `harness/score.py --strict-prize`
(invoked on `problems/JSP-000140/lean`):
`partial_ok = true`, `prize_ready = false`, `missing_theorems = ["jsp_000140_main"]`.

**ROUND 18 CHANGES THE ATTACK FAMILY A THIRD TIME: instead of classifying admissible
colourings (rounds 2–15) or certifying explicit constructions (round 16), it BUILDS A COMPLETE,
MACHINE-CHECKED EXHAUSTIVE SEARCH FOR THE VALUE OF `f(n,4,5)` ITSELF** — the quantity the
catalog question actually asks for ("how many edge colors are necessary if every four-vertex
clique must contain at least five colors?").

New file `lean/JSPProblem/Search.lean` (456 lines, 30 declarations, zero `sorry`):

* `slotOf`, `slotOf_slotEdge`, `slotOf_inj`, `slotOf_lt` — the **slot** of an edge `e = s(a,b)`
  is `min(a,b)*n + max(a,b)`; the slots which carry an edge of `K_n` are exactly the
  `d < n*n` with `d/n < d%n` (`meaningfulSlot`), and `slotEdge` is the inverse;
* `Prefix`, `group`, `fourGroups`, `prefix_last` — **`group n d` = the four-element vertex
  sets which become *complete* when slot `d` is filled in**; every `K₄` of `K_n` lies in
  exactly one group, and `prefix_last` says every `K₄` is complete by the last slot;
* `searchAux` — **the search**: a depth-first search which fills the slots `0, 1, 2, …` in
  order, branching over the colours, and **prunes a branch as soon as one of the cliques
  completed by the slot being filled fails the catalog condition**.  Each `K₄` is checked
  exactly once, at the moment its last slot is filled, and only prefixes consistent with every
  `K₄` seen so far are visited;
* **`searchAux_iff` — THE COMPLETENESS THEOREM**: the search returns `true` on the colouring
  `T` at level `d` **iff some extension of `T` which agrees with it on the edges of the slots
  `< d` is an admissible colouring**.  It is proved by induction on the remaining fuel and
  assumes nothing whatever about the search; this is the mathematical content of the file;
* `hasAdmissible_iff` — `hasAdmissible n k = true ↔` some `k+1`-colouring of `K_n` is
  admissible;
* `liftCol`, `card_colorsOn_liftCol`, `admissible_liftCol` — relabelling the palette preserves
  admissibility;
* **`EG_ge_of_cert` — THE LOWER-BOUND ENGINE**: a certificate `hasAdmissible n k = false`
  (a statement settled by `native_decide` in seconds, with no search required of the reader)
  is a Lean proof that **no admissible colouring of `K_n` with `k+1` colours exists**, and
  hence that `f(n,4,5) ≥ k+2`.

Certificates and exact values (`Main.lean` gains `EG_four`, `EG_five`, `EG_four_le`,
`EG_four_five_real`, `small_values`, `search_certificates_are_bounds`):

* `cert_four_four` — no admissible 4-colouring of `K₄`;
* `cert_five_four` — **no admissible 4-colouring of `K₅`**: the sharp catalog lower bound
  `⌈5(n-1)/6⌉ = 4` is **not attained** at `n = 5`;
* **`Main.EG_four : f(4,4,5) = 5`** and **`Main.EG_five : f(5,4,5) = 5`** (upper bounds: the
  5-colouring of `K₄`, and the round-robin colouring `c({a,b}) = a+b` of `K₅`), so
  `Main.small_values : f(4,4,5) = f(5,4,5) = f(6,4,5) = 5` — the first three exact values of
  the Erdős–Gyárfás function in this development, obtained by three different means.

**The next single ingredient is the colour-permutation symmetry reduction of the search**
(branch only over colours in order of first occurrence).  Measured in Python, it cuts the
node count of "no admissible 6-colouring of `K₇`" from `> 2·10⁷` to `1.3·10⁶`, after which
`hasAdmissible 7 5 = false` and `hasAdmissible 8 5 = false` become `native_decide`-able and
give `f(7,4,5) = 7` and `f(8,4,5) = 7` — the first orders at which `f` exceeds the counting
bound `5(n-1)/6`.  The full design (definitions, the four open membership lemmas, and the
relabelling step) is written out in `discovery/JSP-000140/policy.json` under `blockers`, and
the node counts in `discovery/JSP-000140/eg3_symmetry_nodes.py`.

Note that the round-16 "collision identity" is **no longer on the critical path**: the pruned
search checks every `K₄` at the moment it becomes complete, so no hand proof of the identity
is needed to certify the computational results of round 16.

## Status (round 16)

`lake build`: **OK**.  `sorry`/`admit`: **0**.  `harness/score.py --strict-prize`
(invoked on `problems/JSP-000140/lean`):
`partial_ok = true`, `prize_ready = false`, `missing_theorems = ["jsp_000140_main"]`.

**ROUND 16 CHANGES THE ATTACK FAMILY: instead of classifying admissible colourings, it BUILDS
them and certifies them in Lean.**  The observation that makes this possible:
`JSP140.Admissible` is a *decidable* predicate for a concrete colouring — it quantifies over
the finitely many four-element `Finset (Verts n)` — so an explicit colouring whose
admissibility is discharged by `native_decide` is a genuine Lean proof of the upper bound
`f(n,4,5) ≤ k`, independent of whichever search produced the colouring.

New file `lean/JSPProblem/Tables.lean` (132 lines, 12 declarations, zero `sorry`):

* `tableCol`, `listCol` — the **verified construction engine**: a colouring of `K_n` written
  down as a literal table (the pair `{a,b}`, `a < b`, receives the entry `a*n+b`);
* **`EG_ge_ceil_five_sixth` — THE CATALOG LOWER BOUND IN INTEGRAL FORM**,
  `⌈5(n-1)/6⌉ ≤ f(n,4,5)` for every `n ≥ 4`;
* **`EG_le_of_listCol` / `EG_eq_of_listCol`** — a `native_decide` certificate yields
  `f(n,4,5) ≤ k`, and yields the **exact** value `f(n,4,5) = ⌈5(n-1)/6⌉` whenever the
  verified colouring uses that many colours;
* `sixCol`, **`admissible_sixCol`** (the 1-factorisation of `K₆` with five colours is
  admissible, verified over all `C(6,4) = 15` four-element vertex sets), `sixCol_tight`
  (the `K₄ {0,1,2,3}` spans *exactly* five colours — the catalog condition `q = 5` is tight);
* **`EG_six : EG 6 = 5` — THE FIRST EXACT VALUE OF `f(n,4,5)` IN THIS DEVELOPMENT.**  The
  sharp constant `5/6` of the catalog answer is attained (up to the integrality of
  `5(n-1)/6`) already at `n = 6`.

`Main.lean` gains `EG_six_exact`, `six_catalogue_estimate`
(`|f(6,4,5) − 5·6/6| = 5/6 ≤ n/6`), `EG_ge_ceil`, `catalogue_condition_is_tight`.

### Rigorous computational results (not yet Lean theorems)

An exact-cover search over *admissible colour classes* (each colour class of an admissible
colouring is a disjoint union of two-edge paths and isolated single edges —
`Cherry.nb_eq_singleton`, `Cherry.not_Single_of_path_edge`, `Extremal.pathEdges_disjoint`):

* **no admissible 6-colouring of `K₇` exists** (2197 candidates, 1 008 774 nodes, search space
  exhausted) — so `f(7,4,5) = 7`, a strict improvement of `Extremal.EG_seven_ge_six`;
* **no admissible 6-colouring of `K₈` exists** (10 175 candidates, 244 049 nodes, exhausted) —
  so `f(8,4,5) ≥ 7`, where only `f(8,4,5) ≤ 9` was available;
* **the resolvable Steiner triple system `AG(2,3)` construction fails at `n = 9`**: it would
  give `f(9,4,5) ≤ (n-1)/2 + n/3 = 7 = ⌈5(n-1)/6⌉` colours (four colours for the four parallel
  classes of two-edge paths, three for the twelve leaf edges), but over all
  `27⁴ = 531 441` centre assignments no admissible colouring exists.  Analytically the
  obstruction is that for a `K₄ {v,a,b,x}` with `{v,a,b}` a block centred at `v`, the leaf edge
  `ab` (colour `λ`) forbids the colours of `vx`, `ax`, `bx`, and the leaf-edge conflict graph
  has degree `≈ 2n` — far more than the `n/3` colours available.  **This is the most
  informative negative result of the round: the natural design-theoretic route to the extremal
  family breaks already at the smallest admissible order, which is why the published
  construction is probabilistic.**

The missing lemma needed to turn the first two items into Lean theorems is the **collision
identity** `4·Paths c + Σᵢ binom(componentsᵢ, 2) = Σ_{|S| = 4} (6 − colours(S))`: each
two-edge path lies in exactly `n−3` four-subsets, each pair of components of one colour spans
exactly one four-subset, and each four-subset carries at most one repeated colour.  For
`n = 7, k = 6` it leaves only `Paths c ∈ {3,4,5}` to be eliminated.

## Status (round 15)

`lake build`: **OK**.  `sorry`/`admit`: **0**.  `harness/score.py --strict-prize`
(invoked on `problems/JSP-000140/lean`):
`partial_ok = true`, `prize_ready = false`, `missing_theorems = ["jsp_000140_main"]`.

**Round 15 EXTRACTS THE PARITY OF THE EXTREMAL CASE, REPAIRS THE ROUND-14 REDUCTION, AND COMPLETES
THE STRUCTURE OF THE EXTREMAL COLOURINGS.**  Three new files, 908 lines, 39 declarations, zero `sorry`.

### 1. The arithmetic of extremality (`lean/JSPProblem/Extremal.lean`, 349 lines)

* `oneB_even` — **THE HANDSHAKING LEMMA FOR A COLOUR CLASS.**  In a colour class every vertex has
  colour-degree `0`, `1` or `2` and the degree sum is `2 * |E_i|`, hence the number of degree-`1`
  vertices is **even**: they come in pairs.  This is the parity input which the counting lemmas of
  `Cherry.lean` and `Paths.lean` discard (they compare cardinalities linearly).
* `pathEdges`, `card_pathEdges`, `pathEdges_disjoint`, `two_mul_twoA_le_classIn` — the two edges of a
  two-edge path, two per path, pairwise disjoint inside a colour class: `2 * |A_i| ≤ |E_i|`.
* `tight_three_mul_twoA_le` — in the extremal case `3 * |A_i| ≤ n` for every colour `i`.
* **`tight_twoA_odd` — in the extremal case every colour class contains an ODD number of two-edge
  paths** (`|A_i| = n - |B_i|`, `n ≡ 1 (mod 6)` odd, `|B_i|` even), hence
* `tight_twoA_le` — `|A_i| ≤ (n-4)/3`, and `tight_paths_le`;
* **`tight_ge_thirteen` — AN EXTREMAL ADMISSIBLE COLOURING OF `K_n` REQUIRES `n ≥ 13`**
  (`(6t+1)t ≤ 5t(2t-1) ⟹ t ≥ 2` for `n = 6t+1`);
* `no_five_colouring_of_K7`, **`EG_seven_ge_six`: `f(7,4,5) ≥ 6 > 5 = 5(7-1)/6`** — the first
  *strict* improvement of the sharp `5/6` lower bound at a concrete `n`.

### 2. The faithful `o(n)` hypothesis (`lean/JSPProblem/Slack.lean`, 194 lines)

The round-14 hypothesis (`6k = 5(m-1)` for every `m ≡ 1 (mod 6)`) is **strictly stronger than the
published result** `f(n,4,5) = 5n/6 + o(n)`, which only gives `6k ≤ 5(m-1) + δm` for every `δ > 0`.
This file states the hypothesis the paper actually supplies and proves the upper half from it:

* `STSFamily` / `SlackFamily` — for every `δ > 0` and all large `m ≡ 1 (mod 6)`, an admissible
  `k`-colouring of `K_m` with `6k ≤ 5(m-1) + δm` (and, for `STSFamily`, with a Steiner triple system
  of two-edge paths);
* `fiveSixthUpper_of_slack_family` — `f(n,4,5) ≤ 5n/6 + εn` for all
  `n ≥ max (M(ε/2)+7, ⌈10/ε⌉+1)`;
* **`jsp_000140_main_of_STS_slack_family` — THE REQUIRED STATEMENT REDUCED TO THE TRUE CONTENT OF
  arXiv:2207.02920**; `STSFamily_of_extremal` shows nothing of round 14 is lost.

### 3. The single-edge half of the extremal structure (`lean/JSPProblem/Singles.lean`, 365 lines)

* `singleFinset`, `mem_singleFinset`; `twoA_oneB_or_zero`; `single_or_center`;
* **`mem_classIn_single_or_path` — every edge of a colour class is a path edge or an isolated single
  edge**; `card_single_in_classIn`;
* **`card_singleFinset` — THE SINGLE-EDGE IDENTITY `|E(K_n)| = 2 * Paths c + (number of single
  edges)`**; `paths_le_singles` (`Paths c ≤ #single edges`, the dual of
  `Cherry.three_mul_paths_le_edges`); `leafEdge_subset_single`, `leafEdge_disjoint`;
* **`tight_card_singles` and `tight_single_is_leaf` — IN THE EXTREMAL CASE THE SINGLE EDGES ARE EXACTLY
  THE LEAF EDGES OF THE TWO-EDGE PATHS, one for each**, i.e. the `n(n-1)/6` single edges are in
  canonical bijection with the blocks of the Steiner triple system of `Rigidity`;
* `Main.extremal_structure_complete` collects the whole extremal case in one theorem.

## Status (round 14)

`lake build`: **OK**.  `sorry`/`admit`: **0**.  `harness/score.py --strict-prize`
(invoked on `problems/JSP-000140/lean`):
`partial_ok = true`, `prize_ready = false`, `missing_theorems = ["jsp_000140_main"]`.

**Round 14 CLOSES THE LOGICAL GAP LEFT BY ROUND 13: the prize now reduces to ONE hypothesis.**

New file `lean/JSPProblem/Restriction.lean` (261 lines, 12 declarations, zero `sorry`):

* `restrictCol`, `mem_edgeFinset_image`, `mem_edgeFinset_mk_image`, `colorsOn_restrictCol` —
  restriction of an edge colouring along an injection `Fin m ↪ Fin n`: the colours of a restricted
  `K₄` are **exactly** the colours it has in `K_n`;
* `Admissible.restrict` — **the catalog condition survives restriction**;
* `EG_mono` — **monotonicity of `f(n,4,5)`** (`m ≤ n → f(m,4,5) ≤ f(n,4,5)`), the one elementary
  fact about `f` that had never been formalised here;
* `exists_one_mod_six_ge` — for every `n ≥ 6` there is `m ≡ 1 (mod 6)` with `n ≤ m ≤ n + 6`;
* `fiveSixthUpper_of_family_const` — **THE REDUCTION.**  If for every `m ≡ 1 (mod 6)` there is an
  admissible `k`-colouring of `K_m` with `6k ≤ 5(m-1) + 6D` for a *fixed* constant `D`, then
  `f(n,4,5) ≤ 5n/6 + ε n` for every `ε > 0` and all `n ≥ max(7, ⌈(D+5)/ε⌉+1)`: monotonicity
  absorbs the five other residue classes and the `O(1)` slack is absorbed by `ε n`;
* `fiveSixthUpper_of_extremal_family` (the same with `D = 0`), `fiveSixth_of_extremal_family` and
  **`jsp_000140_main_of_STS_family` — THE REQUIRED STATEMENT REDUCED TO ONE HYPOTHESIS**:

      (extremal colourings of `K_m`, `6k = 5(m-1)`, whose two-edge paths form a Steiner triple
       system, for every `m ≡ 1 (mod 6)`)  ⟹  `jsp_000140_target`.

`Rigidity.lean` gained **`tight_covers`** and **`tight_degree`**: in the extremal case
`(twoA c i) ∪ (oneB c i) = univ` for every colour `i`, i.e. **no colour class of an extremal
colouring wastes a vertex** (each colour class is a spanning union of two-edge paths and isolated
single edges, `2a_i + 3b_i = n`), with the corollary `Main.extremal_no_isolated_vertex`.

So the *whole* remaining content of the required theorem is the construction of arXiv:2207.02920
(Bennett–Cushman–Dudek–Prałat), which is **probabilistic** (random triangle removal + differential
equation method) — there is no explicit admissible colouring of `K_m` with `5(m-1)/6` colours in the
literature to formalise.

## Status (round 13)

`lake build`: **OK**.  `sorry`/`admit`: **0**.  `harness/score.py --strict-prize`
(invoked on `problems/JSP-000140/lean`):
`partial_ok = true`, `prize_ready = false`, `missing_theorems = ["jsp_000140_main"]`.

**Round 13 CHARACTERISES THE MISSING HALF: the extremal colourings are exactly the Steiner
triple systems.**

New file `lean/JSPProblem/Rigidity.lean` (583 lines, 25 declarations, zero `sorry`):

* `pathSet c i v` — the **three vertices** of a two-edge path of colour `i` centred at `v`
  (the centre and its two leaves); `card_pathSet`: three elements for `v ∈ twoA c i`.
* `cherry_leaf_pair` — the two leaves span an **isolated single edge of a different colour**
  (cardinality `1` at each leaf) — the "leaf edge" part of `Cherry.nb_eq_singleton_of_cherry`.
* `pathSet_dichotomy` — for `x ≠ y` in a `pathSet`: either `v ∈ {x,y}` and `c s(x,y) = i` (a *path*
  pair), or `x, y` are the two leaves and `c s(x,y) ≠ i` (the *leaf* edge).  Exclusive dichotomy.
* **`pathSet_sub_inter` — THE PACKING LEMMA**: two two-edge paths of an admissible colouring
  (`n ≥ 4`) cannot have a common two-element vertex set unless they are the *same* path.  Four
  cases: both pairs path pairs (`not_two_centres`); path pair / leaf edge in either order (the leaf
  edge is a private single edge, contradicting the two colour-`i` neighbours of the centre);
  both pairs leaf edges (`centre_eq_of_leaves'`).
* `pathFinset c`, `card_pathFinset` (its cardinality is `Paths c`), `card_filter_pairIn_le`
  (at most one `pathSet` contains a given pair), `sum_pairIn_three`, and
  `sum_card_filter_pairIn` — **the double counting** of pairs inside the `pathSet`s:
  `Σ_p #{B ∋ p} = 3 * (pathFinset c).card`.
* `IsSTS B` — a **Steiner triple system** on `Fin n`: three-element sets in which every pair of
  distinct vertices lies in exactly one member.
* **`tight_pathFinset_is_STS` — THE RIGIDITY THEOREM.**  If the counting lemma of `Cherry.lean`
  is an equality, `3 * Paths c = |E(K_n)|`, then the `pathSet`s of `c` are a Steiner triple system
  on `Fin n` (every pair is in at most one, the double count makes every summand `1`).
* **`tight_attained` — the converse.**  An admissible colouring with the extremal number
  `6 * k = 5(n-1)` of colours *forces* `3 * Paths c = |E(K_n)|`.  Hence:

      an admissible colouring of `K_n` uses the extremal number `5(n-1)/6` of colours
      **iff** its two-edge paths form a Steiner triple system of order `n`.
* `tight_paths` (`Paths c = n(n-1)/6`), **`tight_mod6`** (the extremal value is only attainable for
  `n ≡ 1 (mod 6)`, so the sharp constant `5/6` is *not* attained on the other five residue
  classes), `tight_classes_span` (in the extremal case every colour class spans the vertex set:
  `2a_i + 3b_i = n`, the equality case of `Paths.two_mul_classIn_le_add`).

`Main.lean` consequences: `fiveSixth_at_extremal` (at an extremal `n`:
`5n/6 - n/6 ≤ f(n,4,5) ≤ 5n/6`) and **`extremal_is_STS`** (an extremal colouring exists ⟹ its
two-edge paths form a Steiner triple system, together with the two-sided bound).  So the **upper
half of `jsp_000140_main` is now exactly the statement**: for all large `n ≡ 1 (mod 6)` there is a
Steiner triple system of order `n` together with a choice of a centre in each block and a colouring
of the blocks — the object built by the *random triangle removal* process of arXiv:2207.02920.

Abandoned in round 13 (documented in `discovery/JSP-000140/policy.json`):

* the **1-factorisation of `K_n`** for even `n` (`Z_{n-1} ∪ {∞}`, colour of `{x,y}` = `(x+y)/2`, of
  `{∞,x}` = `x`): it is admissible **iff** `3 ∤ n-1`; a `K₄` on `{∞, a, a+t, a-t}` with `3t ≡ 0`
  carries two monochromatic opposite pairs (only four colours).  So it adds nothing beyond the ghost
  colouring of `Ghost.lean` and does not help for `n ≡ 4 (mod 6)`;
* an **integrality argument** extracting the exact value `5(n-1)/6` from the `o(n)` form: it was
  formalised, found **false** by Lean (`linarith`) and removed — in `FiveSixthUpper` the threshold
  `N` depends on `ε`, so for a fixed `n` the error `ε n` cannot be pushed below `1/6`;
* the probabilistic construction of the upper half itself: not formalisable, there is no explicit
  colouring in the literature.

## Status (round 10)

`lake build`: **OK**.  `sorry`/`admit`: **0**.  `harness/score.py --strict-prize`
(invoked on `problems/JSP-000140/lean`):
`partial_ok = true`, `prize_ready = false`, `missing_theorems = ["jsp_000140_main"]`.

**Round 10 PROVES THE COMPLETE LOWER HALF OF THE CATALOG ANSWER, with the sharp constant `5/6`.**

**Round 10 added the second, independent half of the development.**

1. `lean/JSPProblem/Cherry.lean` (new, 730 lines, zero sorry) — **the `5/6` lower bound of
   arXiv:2207.02920, in full**.  Round 4 had isolated the whole lower bound in the single concrete
   hypothesis `Paths c ≤ n(n-1)/6` (at most `n²/6` two-edge paths, i.e. at least two thirds of all
   edges lie in *single-edge* components of their colour class).  Round 10 **proves that
   hypothesis** with three new structural lemmas and one counting lemma:

   * `cherry_four_ne` — **the constraint of the `K₄` through a two-edge path.**  If `a - v - b` is
     a two-edge path of colour `i` and `x` is a fourth vertex, then the *other four* edges of the
     `K₄` on `{v, a, b, x}` carry **four pairwise distinct colours, none of them `i`**: the `K₄`
     already carries `i` twice (on `s(v,a)`, `s(v,b)`), must span five colours, and may not carry
     `i` a third time (`classIn_card_le_two`).
   * `centre_eq_of_leaves`, `centre_eq_of_leaves'` — **a pair of leaves determines the centre**:
     two two-edge paths with the same two leaves are the same path (two applications of
     `cherry_four_ne`).
   * `nb_eq_singleton_of_cherry` — **the edge joining the two leaves is an isolated single edge**:
     with `j = c s(a,b)` one has `j ≠ i`, `nb c j a = {b}` and `nb c j b = {a}`, i.e. `s(a,b)` is
     the only edge of its (necessarily different) colour class at `a` and at `b`.
   * `not_two_centres`, `leaf_not_centre` — no edge of `K_n` joins two centres of one colour, and
     the leaves of a two-edge path are never centres of its colour.
   * `cherryEdges` / `card_cherryEdges` / `cherryEdges_disjoint` — **the counting**: the two
     edges of a two-edge path together with the single edge between its leaves form a *three-element*
     set of edges, and **the sets belonging to different two-edge paths are pairwise disjoint**
     (four cases: two path edges — excluded by `not_two_centres`; path edge vs. leaf edge —
     excluded because a path edge is never a single edge and a leaf edge always is; two leaf edges
     — excluded by `centre_eq_of_leaves'`).
   * **`Cherry.three_mul_paths_le_edges` — THE `5/6` COUNTING LEMMA**:
     `3 * Paths c ≤ |E(K_n)| = n(n-1)/2`, i.e. `Paths c ≤ n(n-1)/6`, *unconditionally*, for every
     admissible colouring.  (`six_mul_paths_le`, `paths_le`.)
   * `Cherry.five_sixth_lower` — **every admissible `k`-colouring of `K_n` (`n ≥ 4`) uses at least
     `5(n-1)/6` colours**, i.e. `5(n-1) ≤ 6k`; `EG_ge_five_sixth`, `EG_ge_five_sixth_real`.
   * `Cherry.fiveSixthLower_eps` — **the lower half of the headline in ε-form**: for every
     `ε > 0` and all `n ≥ max (⌈5/(6ε)⌉, 4)`, `5n/6 - ε n ≤ f(n,4,5)`.

   Consequently (`Main.lean`): `fiveSixthLower_eg : FiveSixthLower EG` (**the lower half of
   `jsp_000140_main`, complete**), `admissibleLower_eps : AdmissibleLower 1` (the same in the
   `Admissible`-colouring language of the reduction theorem `jsp_000140_target_iff`),
   `fiveSixthShape_five_sixth` (`5n/6 - 5/6 ≤ f(n,4,5) ≤ 5n/6 + n/6 + 1` for all `n ≥ 4` — the
   lower side improves from `n/12 + 3/4` of round 9 to the sharp `5/6`), and
   `fiveSixthShape_sixth_residue'` (`|f(n,4,5) - 5n/6| ≤ n/6` for all `n ≥ 5` with `n ≢ 4 (mod 6)`,
   the *symmetric* form, which round 9 could not prove), hence
   `fiveSixth_ge_sixth` and `fiveSixth_eps_ge_sixth`: the catalogue estimate
   `|f(n,4,5) - 5n/6| ≤ ε n` for **every `ε ≥ 1/6`** (on `n ≢ 4 (mod 6)`), now with the sharp
   constant on *both* sides (round 9 only had `ε ≥ 1/4`).

   The classical counting constant `3/4` of Erdős–Gyárfás (1977) is thereby replaced by the sharp
   `5/6` of BCDP22 with no `o(n)` loss.  What remains open is only the *upper* half.

2. `Main.lean` consequences as listed above; the file now imports `JSPProblem.Cherry`.

**Rounds 2–4 added the classical and constructive development.**

### Proved (all zero-sorry, `lean/JSPProblem/`)

`Cherry.lean` (**new in round 10** — the `5/6` lower bound)
* `six_edges_ne` (the six edges of a `K₄` are pairwise distinct), `card_two_eq`;
* `cherry_four_ne` (**the `K₄` constraint through a two-edge path**), `colorsOn_cherry_fourSet`
  (such a `K₄` spans exactly five colours);
* `centre_eq_of_leaves`, `centre_eq_of_leaves'` (a pair of leaves determines the centre);
* `nb_eq_singleton_of_cherry` (**the edge between the leaves is an isolated single edge**);
* `not_two_centres`, `leaf_not_centre`; `Nbrs`, `mem_Nbrs`, `card_twoA`, `image_pairs_two`;
* `leafEdge`, `cherryEdges`, `card_cherryEdges` (three edges), `cherryEdges_subset_edgeFinset`,
  `Single`, `Single_of_leaf`, `not_Single_of_path_edge`, `cherryEdges_disjoint`;
* `cherryFinset`, `card_cherryFinset` (its cardinality is `Paths c`);
* **`three_mul_paths_le_edges` (`3 * Paths c ≤ |E(K_n)|`), `six_mul_paths_le`, `paths_le`**
  (`Paths c ≤ n(n-1)/6`);
* **`five_sixth_lower` (`5(n-1) ≤ 6k` for every admissible colouring), `EG_ge_five_sixth`,
  `EG_ge_five_sixth_real`, `fiveSixthLower_eps` (the lower half of the headline)**.

`Definitions.lean`
* `Col n k` (an edge colouring of `K_n` as a function on unordered pairs), `edgeFinset S`
  (the edges of `K` on `S`), `colorsOn c S`, `Admissible c`, `classIn c i S`.
* `classIn_card_le_two` — **the key local structure theorem**: no four vertices carry three
  edges of one colour.
* `EG n` (the Erdős–Gyárfás function `f(n,4,5)` via `sInf`), `EG_le` (minimality),
  `EG_admissible` (attained), `EG_le_sq` (an explicit admissible colouring with `n²` colours),
  `FiveSixth`, `FiveSixthLower`, `FiveSixthUpper`, `fiveSixth_iff`.

`ColorClass.lean`
* `nbrsIn_card_le_two` — a vertex has at most two neighbours in any one colour class;
  `no_mono_triangle` (moved here from `Main.lean`); `three_edges_ne`.
* `classIn_avoid` — if `v` (outside `S`) has two colour-`i` neighbours `a ≠ b` in `S`, then no
  colour-`i` edge of `S` is incident to `a` or `b`: the path `a – v – b` is an **isolated
  two-edge path** of the colour class.
* `classIn_avoid_in` (**new in round 2**) — the same statement with **no condition on `v`**:
  `classIn c i S \ {s(v,a), s(v,b)} ⊆ classIn c i (S \ {a,b})`.  This is the single missing
  ingredient of the counting argument identified in round 1.
* the counting toolkit (`card_ge_three`, `card_fourSet`, `mem_fourSet_*`, `threeSet`,
  `card_threeSet`, `exists_three_mem`).

`Counting.lean` (**new in round 2** — the classical counting argument)
* `nb`, `mem_nb`, `nb_card_le_two` — colour-`i` neighbours of a vertex.
* `nb_mem_eq`, `nb_eq_singleton` — **the structural core**: if `v` has two colour-`i` neighbours
  `a, b` then the *only* colour-`i` edge at `a` is `s(a,v)`.  Together with `classIn_avoid_in`
  this says every colour class of an admissible colouring is a disjoint union of single edges
  and two-edge paths.
* `card_nb_eq_filter`, `degree_sum` — the degree sum identity `∑_v deg(v) = 2·|E_i|`.
* `two_mul_cardA_le_cardB` — the two vertices of the two-edge paths are pairwise disjoint
  (`2·|A| ≤ |B|`), the counting step of the classical proof.
* `three_mul_classIn_le` — **the counting lemma** `3 · |E_i| ≤ 2n`.
* `sum_card_classIn` — the colour classes partition the edges.
* `card_edgeFinset_univ_two` — `2·|E(K_n)| = n(n-1)`.
* `classical_lower_bound`, `EG_ge_classical`.

`Construction.lean` (**new in round 3** — the round-robin construction)
* `sumColMod m n h` / `sumCol` — the sum (round-robin) colouring `c({a,b}) = (a+b) mod m`.
* `natCast_zmod_inj`, `natCast_zmod_eq_iff`, `fin_zmod_inj` — arithmetic in `ZMod m`.
* `two_mul_inj` — **odd modulus**: multiplication by `2` in `ZMod m` is injective for odd `m`.
* `sumColMod_eq_iff` — two edges have the same colour iff the vertex sums agree mod `m`.
* `sumColMod_adj_ne`, `sumColMod_adj_ne_last`, `sumColMod_adj_ne_mid` — properness.
* `sumColMod_one_collision` — at most one monochromatic pair of opposite edges in a `K₄`.
* `admissible_sumColMod`, `admissible_sumCol` — **the construction is admissible for odd `m`**.
* `EG_le_sumCol` (`f ≤ n` for odd `n`), `EG_le_succ` (`f ≤ n+1`), `EG_le_linear` (`f = Θ(n)`).

`Paths.lean` (**new in round 4** — the quantitative counting argument and the `5/6` criterion)
* `Paths` (the number of two-edge paths), `twoA_oneB_card_le`, `sum_nb_card_eq`,
  `two_mul_classIn_le_add`, `mul_n_sub_one_le` (the quantitative identity),
  `three_mul_paths_le`, `classical_lower_bound'`, `five_sixth_of_paths` (the `5/6` criterion),
  `EG_ge_five_sixth_of_paths`, `EG_ge_five_sixth_of_paths_real`, `five_sixth_of_no_paths`.

`Ghost.lean` (**new in round 4** — the ghost-vertex construction)
* `val_eq_last`, `ghostEdge`, `ghostEdge_comm`, `ghostEdge_base`, `ghostEdge_last`, `modFin`,
  `ghostCol`, `ghostCol_val_mk`, `ghostCol_swap`;
* `ghostCol_eq_iff`, `ghostCol_eq_of_zmod`, `ghostZ_base`, `ghostZ_last`, `fin_zmod_base_inj`;
* `ghostCol_ne_last`, `ghostCol_ne_first`, `ghostCol_last_ne` (properness in all three forms);
* `three_mul_inj` (**`3` is a unit in `ZMod m` when `3 ∤ m`**), `collision_12`, `collision_13`,
  `collision_23`, `cross_12`, `cross_13`, `cross_23` (**at most one collision** in a `K₄`);
* `mem_B_base_ab`, `mem_B_base_ac`, `mem_B_base_ad`, `mem_B_last`, `ghost_four_base`,
  `ghost_four_last`, `admissible_ghost`, `EG_le_ghost`.

`Main.lean`
* `jsp_000140_target` — the statement of the required theorem, as a `def`;
* `EG_le_ghost_sub`, `EG_le_sixth_residue`, `EG_le_sixth_residue_real`,
  `fiveSixthUpper_sixth_residue`, `fiveSixthUpper_sixth_ge`, `fiveSixthShape_sixth_residue`,
  `fiveSixth_quarter`, `fiveSixth_ge_quarter_ge`, `admissibleLower_five_sixth_of_paths`
  (**new in round 4**).
* `fiveSixthLower_iff`, `fiveSixthUpper_iff`, `jsp_000140_target_iff` — a **proved reduction**
  of the headline statement to the two purely combinatorial bounds
  `AdmissibleLower 1 ∧ AdmissibleUpper 1`.
* `three_edges_ne`, `no_mono_triangle`, `upper_bound_sq`; the corollaries
  `EG_ge_classical_real`, `EG_ge_third`, `fiveSixthLower_at_eighth`; and, **new in round 3**,
  `EG_le_succ_real`, `EG_le_of_odd_real`, **`fiveSixthShape`** (the two-sided
  `|f(n,4,5) - 5n/6| ≤ n/6 + 1`), `fiveSixth_ge_one`, `fiveSixthUpper_at_third`,
  `admissibleUpper_at_third`, `fiveSixthUpper_odd_at_sixth`, `fiveSixthUpper_odd_ge`,
  `admissibleLower_at_third`.

### Not yet proved (blockers, see `discovery/JSP-000140/policy.json`)

0. **NOTHING is missing on the lower side**: `FiveSixthLower EG` holds for *every* `ε > 0` with the
   sharp constant `5/6` (`Main.fiveSixthLower_eg`, `Main.admissibleLower_eps`,
   `Cherry.fiveSixthLower_eps`).  Round 4's blocker C ("the BCDP22 lower bound, now isolated as
   `Paths c ≤ n(n-1)/6`") is **closed** in round 10 by `Cherry.three_mul_paths_le_edges`.

1. **The upper half for `0 < ε < 1/6`** (the construction of arXiv:2207.02920).  Round 13
   established that this is a **Steiner triple system** problem: by
   `Rigidity.tight_attained`, `Rigidity.tight_pathFinset_is_STS` and `Main.extremal_is_STS`, an
   admissible colouring with the extremal `5(n-1)/6` colours has its two-edge paths forming a
   Steiner triple system of order `n`, and `Rigidity.tight_mod6` shows this needs `n ≡ 1 (mod 6)`.
   The constructions available here (round-robin: `n` colours; ghost: `n-1` colours for
   `n ≡ 0, 2 (mod 6)`; the 1-factorisation of `K_n`, which round 13 checked and found admissible
   only for `3 ∤ n-1`) all stop at `5n/6 + O(n)`.  The paper's own construction is *probabilistic*
   (random triangle removal), so there is no explicit colouring to formalise.  The next formal
   step is `restrictCol`/`EG_mono` (monotonicity of `f(n,4,5)`), after which a family of extremal
   colourings for `n ≡ 1 (mod 6)` yields the upper half with an `O(1)` error.
2. **The upper half at `ε = 1/6` for the residue class `n ≡ 4 (mod 6)`**: for these `n` only
   `f(n,4,5) ≤ n+1` is available, because the ghost colouring needs `3 ∤ (n-1)` and the
   round-robin colouring needs odd `n`.  The ghost construction is *provably* not admissible when
   `3 ∣ m`: the `K₄` `{∞, 0, m/3, 2m/3}` then carries only three colours.  A `K₄` on a duplicate
   vertex pair shows that the "duplicate a vertex" trick cannot work, and the classical
   1-factorisation `c(s(∞,a)) = 2a` is *not* admissible (a `K₄` on `{∞, a, b, c}` with
   `a+b = 2c` spans only four colours).
3. ~~**The lower half for `0 < ε < 1/8`**~~ — **CLOSED in round 10** by `Cherry.lean` (see
   above): the required global argument across different colour classes is the injection
   "two-edge path → its three edges" (`cherryEdges_disjoint`), and the missing ingredient turned
   out to be the `K₄` constraint `cherry_four_ne` plus the two consequences "leaves determine the
   centre" and "the edge between the leaves is isolated".
