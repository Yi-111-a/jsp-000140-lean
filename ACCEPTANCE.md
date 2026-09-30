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
> | Publications | `[BCDP22]` arXiv:2207.02920 — *The Erdős–Gyárfás function `f(n,4,5) = 5n/6 + o(n)` — so Gyárfás was right*; `[JoMu22]` arXiv:2208.12563 |

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

## Status (round 3)

`lake build`: **OK**.  `sorry`/`admit`: **0**.  `harness/score.py --strict-prize`
(invoked on `problems/JSP-000140/lean`):
`partial_ok = true`, `prize_ready = false`, `missing_theorems = ["jsp_000140_main"]`.

**Round 3 added the linear construction side of the problem** (new file
`lean/JSPProblem/Construction.lean`, zero sorry): the classical **sum (round-robin) colouring**

    c({a, b}) = a + b  (mod m)

of `K_n` with `m` colours (`n ≤ m`), proved admissible whenever `m` is **odd**.  The two
structural ingredients are the ones the round-robin colouring is built on:

* `sumColMod_adj_ne` — **properness**: two edges with a common endpoint get different colours, so
  a `K₄` carries two edges of one colour only if they are *disjoint*;
* `sumColMod_one_collision` — **at most one monochromatic pair of opposite edges**: if
  `a+b = c+d` and `a+c = b+d` then `2a = 2d` in `ZMod m`, and `2` is invertible for odd `m`
  (`two_mul_inj`), so `a = d`, contradicting distinctness.

Hence (`admissible_sumColMod`)

* `EG_le_sumCol` — `f(n,4,5) ≤ n` for every **odd** `n` (take `m = n`);
* `EG_le_succ` — `f(n,4,5) ≤ n + 1` for every `n` (take `m = n+1`, odd when `n` is even);
* so `f(n,4,5) = Θ(n)`.

Combined with the classical counting bound `f(n,4,5) ≥ 3(n-1)/4` of round 2 this gives the
**first genuine two-sided statement about the headline constant**:

* `Main.fiveSixthShape` — `|f(n,4,5) - 5n/6| ≤ n/6 + 1` for all `n ≥ 4`, i.e.
  `f(n,4,5) = 5n/6 + O(n)`;
* `Main.fiveSixth_ge_one` — the headline estimate `|f(n,4,5) - 5n/6| ≤ ε n` for every `ε ≥ 1`
  and all `n ≥ 4`;
* `Main.fiveSixthUpper_at_third`, `Main.admissibleUpper_at_third` — the **upper half** for
  `ε ≥ 1/3` (all `n ≥ 6`), also in the `Admissible`-colouring language of the reduction theorem;
* `Main.fiveSixthUpper_odd_at_sixth`, `Main.fiveSixthUpper_odd_ge` — the upper half for **odd**
  `n` already at `ε = 1/6` (the round-robin colouring meets `5n/6 + n/6 = n` exactly);
* `Main.admissibleLower_at_third` — the **lower half** in `Admissible`-colouring form for
  `ε ≥ 1/3`.

Together with round 2's `fiveSixthLower_at_eighth` (lower half for `ε ≥ 1/8`), the state of the
headline is now: **lower half proved for `ε ≥ 1/8`, upper half proved for `ε ≥ 1/3` (and for
`ε ≥ 1/6` on odd `n`), and the two-sided `O(n)` shape bound proved.**  The remaining content is
the two BCDP22 steps (see *Not yet proved*).

### Proved (all zero-sorry, `lean/JSPProblem/`)

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

`Main.lean`
* `jsp_000140_target` — the statement of the required theorem, as a `def`.
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

1. **The upper half for `0 < ε < 1/3`** (the BCDP22 construction).  The round-robin colouring
   uses `n = 5n/6 + n/6` colours, so it reaches the headline constant only up to the `O(n)`
   error.  It cannot be improved by *merging* colour classes: each colour class of the sum
   colouring is a perfect matching, so the union of two of them is a disjoint union of even
   cycles, and a `K₄` on a 4-cycle spans at most three colours.  One needs the BCDP22 /
   JoMu22 style construction (1-factorisations of hypergraph matchings, then a weighted blow-up),
   which is a genuinely new colouring mechanism rather than a post-processing of `sumCol`.
2. **The upper half for even `n` at `ε = 1/6`**: currently even `n` only gets `f(n,4,5) ≤ n+1`
   (sum colouring mod `n+1`).  A `K₄` on a duplicate vertex pair shows that the "duplicate a
   vertex" trick cannot work, and the classical 1-factorisation `c(s(∞,a)) = 2a` is *not*
   admissible (a `K₄` on `{∞, a, b, c}` with `a+b = 2c` spans only four colours).
3. **The lower half for `0 < ε < 1/8`** (the BCDP22 structural sharpening `3/4 → 5/6`): in the
   framework of `Counting.lean` this is the statement that at least two thirds of the edges lie
   in single-edge components of their colour class, i.e. `|{two-edge paths}| ≤ n²/6 + o(n²)`;
   the present proof gives only `2|A| ≤ |B|` (two-edge paths are vertex-disjoint), which yields
   `3/4`.
