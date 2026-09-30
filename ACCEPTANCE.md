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

## Status (round 4)

`lake build`: **OK**.  `sorry`/`admit`: **0**.  `harness/score.py --strict-prize`
(invoked on `problems/JSP-000140/lean`):
`partial_ok = true`, `prize_ready = false`, `missing_theorems = ["jsp_000140_main"]`.

**Round 4 added the second, independent half of the development.**

1. `lean/JSPProblem/Paths.lean` (new, zero sorry) — **the quantitative form of the counting
   argument, i.e. the `5/6` criterion for the lower half**:

   * `Paths c` — the total number of two-edge paths `a - v - b` over all colour classes of `c`
     (a vertex with two colour-`i` neighbours is the centre of exactly one such path);
   * `two_mul_classIn_le_add` — the *refined* per-colour counting lemma `2 * |E_i| ≤ n + p`, where
     `p` is the number of two-edge paths of that colour class (the classical lemma `3 * |E_i| ≤ 2n`
     throws `p` away);
   * `mul_n_sub_one_le` — **the quantitative identity** `n * (n-1) ≤ n * k + Paths c`, i.e.
     `k ≥ (n-1) - Paths c / n`;
   * `five_sixth_of_paths` — **the `5/6` criterion**: if `Paths c ≤ n(n-1)/6` (equivalently: at
     least two thirds of all edges lie in *single-edge* components of their colour class) then
     `5 * (n-1) ≤ 6 * k`, i.e. `k ≥ 5(n-1)/6 = 5n/6 - 5/6`;
   * `three_mul_paths_le` + `classical_lower_bound'` — the classical bound `3(n-1) ≤ 4k` re-derived
     from the new identity, so the new framework subsumes the old one.

   The lower half of the catalog answer is therefore reduced to the *single concrete hypothesis*
   `Paths c ≤ n(n-1)/6` — the BCDP22 lower bound, in the form of one inequality on the number of
   two-edge paths.

2. `lean/JSPProblem/Ghost.lean` (new, zero sorry) — **a second construction**, the ghost-vertex
   colouring

       c({a, b}) = a + b   (a, b < m),        c({∞, a}) = 2a

   of `K_{m+1}` with `m` colours, for `m` odd and `3 ∤ m`.  A `K₄` containing `∞` spans the six
   colours `2x, 2y, 2z, x+y, x+z, y+z`; the only possible coincidences are the three "cross"
   equalities, and two of them give `3x = 3y`, i.e. `x = y` because `3` is a unit in `ZMod m`
   (`three_mul_inj`, the analogue of `two_mul_inj` for the sum colouring).  Hence

   * `admissible_ghost` — **the ghost colouring of `K_{m+1}` with `m` colours is admissible**;
   * `EG_le_ghost` — `f(m+1, 4, 5) ≤ m`, i.e. **`f(n,4,5) ≤ n - 1` for `n ≡ 0, 2 (mod 6)`**, which
     improves round 3's `f ≤ n + 1` for two thirds of the even `n`.

   Consequently (`Main.lean`): `EG_le_sixth_residue` (`f(n,4,5) ≤ n` for every `n ≢ 4 (mod 6)`),
   `fiveSixthUpper_sixth_residue` / `fiveSixthUpper_sixth_ge` (**the upper half of the headline at
   the sharp value `ε = 1/6` for all `n ≢ 4 (mod 6)`, not only for odd `n`**),
   `fiveSixthShape_sixth_residue` (`5n/6 - (n/12+3/4) ≤ f(n,4,5) ≤ 5n/6 + n/6` — the upper side
   loses the additive constant), `fiveSixth_quarter` (`|f - 5n/6| ≤ n/4` for `n ≥ 5`, `n ≢ 4 (mod 6)`)
   and `admissibleLower_five_sixth_of_paths` (the `5/6` criterion in the `Admissible`-colouring
   language of the reduction theorem).

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

1. **The upper half for `0 < ε < 1/6`** (the BCDP22 construction).  Round 4 improved the available
   constructions: the round-robin colouring uses `n` colours and the ghost colouring `n - 1`
   colours on `K_n` for `n ≡ 0, 2 (mod 6)`, i.e. `5n/6 + O(n)`.  Neither can be improved by
   post-processing: each colour class of the sum colouring is a perfect matching, so the union of
   two of them is a disjoint union of even cycles and a `K₄` on a 4-cycle spans at most three
   colours; and the six colours of a `K₄` in the ghost colouring already have the maximal possible
   number of coincidences (one).  With `k = 5n/6` colours, every colour class would have to have
   `3n/5` edges, i.e. be a spanning disjoint union of `n/5` single edges and `n/5` two-edge paths —
   a new mechanism.  One needs the BCDP22 / JoMu22 style construction (1-factorisations of
   hypergraph matchings, then a weighted blow-up).
2. **The upper half at `ε = 1/6` for the residue class `n ≡ 4 (mod 6)`**: for these `n` only
   `f(n,4,5) ≤ n+1` is available, because the ghost colouring needs `3 ∤ (n-1)` and the
   round-robin colouring needs odd `n`.  The ghost construction is *provably* not admissible when
   `3 ∣ m`: the `K₄` `{∞, 0, m/3, 2m/3}` then carries only three colours.  A `K₄` on a duplicate
   vertex pair shows that the "duplicate a vertex" trick cannot work, and the classical
   1-factorisation `c(s(∞,a)) = 2a` is *not* admissible (a `K₄` on `{∞, a, b, c}` with
   `a+b = 2c` spans only four colours).
3. **The lower half for `0 < ε < 1/8`** (the BCDP22 structural sharpening `3/4 → 5/6`): round 4
   reduced this to the single hypothesis `Paths c ≤ n(n-1)/6` of the proved theorem
   `Paths.five_sixth_of_paths` (equivalently: at least two thirds of the edges lie in single-edge
   components, i.e. `|{two-edge paths}| ≤ n²/6 + o(n²)`).  The quantitative identity
   `Paths.mul_n_sub_one_le` shows that nothing else enters, and the present proof only uses
   `2|A| ≤ |B|` (two-edge paths of one colour class are vertex-disjoint), which yields `3/4`.
   Round 4 also checked that the single-colour count is exhausted: the map "vertex with two
   colour-`i` neighbours" ↦ "two-edge path" is a bijection and every double count over leaves,
   opposite edges or agreeing colour rows is an identity, so the improvement must use a global
   argument across *different* colour classes.
