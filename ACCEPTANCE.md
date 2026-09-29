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

## Status (round 2)

`lake build`: **OK**.  `sorry`/`admit`: **0**.  `harness/score.py --strict-prize`:
`partial_ok = true`, `prize_ready = false`, `missing_theorems = ["jsp_000140_main"]`.

**Round 2 proved the classical counting bound in full** (this is the main new result):

* `Counting.classical_lower_bound` — every admissible `k`-colouring of `K_n`, `n ≥ 4`, satisfies
  `3 * (n-1) ≤ 4 * k`, i.e. **`f(n,4,5) ≥ 3(n-1)/4`** — the classical Erdős–Gyárfás bound
  (1977) for `p = 4, q = 5`, which is exactly the `3/4` that the BCDP22 paper sharpens to `5/6`.
* `Counting.EG_ge_classical`, `Main.EG_ge_classical_real`, `Main.EG_ge_third` — the bound for
  the Erdős–Gyárfás function itself, in `ℕ` and in `ℝ` (`f(n,4,5) ≥ n/3` for `n ≥ 4`).
* `Main.fiveSixthLower_at_eighth` — the lower half of the headline for every `ε ≥ 1/8` and
  `n ≥ 18`; hence the part of the headline still missing is precisely the range
  `0 < ε < 1/8` of the lower bound, i.e. the passage `3/4 → 5/6`.

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

`Main.lean`
* `jsp_000140_target` — the statement of the required theorem, as a `def`.
* `fiveSixthLower_iff`, `fiveSixthUpper_iff`, `jsp_000140_target_iff` — a **proved reduction**
  of the headline statement to the two purely combinatorial bounds
  `AdmissibleLower 1 ∧ AdmissibleUpper 1`.
* `three_edges_ne`, `no_mono_triangle`, `upper_bound_sq`; and the new corollaries
  `EG_ge_classical_real`, `EG_ge_third`, `fiveSixthLower_at_eighth`.

### Not yet proved (blockers, see `discovery/JSP-000140/policy.json`)

1. **A linear construction** (round-robin / 1-factorisation): an admissible colouring of `K_n`
   with `n` (odd) or `n-1` (even) colours.  The natural candidate is
   `c(s(a,b)) = a + b mod n`, which is a *proper* edge colouring for every `n` (each colour
   class is a matching), and for **odd** `n` it gives `≥ 5` colours in every `K₄`; for even `n`
   one needs the extra step `c(s(∞,a)) = 2a`, i.e. the classical 1-factorisation, which uses
   that `2` is invertible mod `n-1`.  With this, `3(n-1)/4 ≤ f(n,4,5) ≤ n` would give
   `f(n,4,5) = Θ(n)` and a two-sided `|f(n,4,5) - 5n/6| ≤ O(n)` bound.
2. **The upper half of the headline** (BCDP22 construction): for every `ε > 0` and all large
   `n` an admissible colouring with at most `5n/6 + εn` colours.  This is the construction
   side of the paper.
3. **The lower half for `ε < 1/8`** (BCDP22 structural analysis): the sharpening of the
   counting constant `3/4` to `5/6`.  In the counting framework used here this is the
   statement `|{two-edge paths}| ≤ n²/6 + o(n²)`, i.e. that at least two thirds of all edges
   lie in single-edge (matching) components of their colour class.
