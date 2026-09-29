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

## Status (round 1)

`lake build`: **OK**.  `sorry`/`admit`: **0**.  `harness/score.py`: `partial_ok = true`,
`prize_ready = false`, `missing_theorems = ["jsp_000140_main"]`.

### Proved (all zero-sorry, `lean/JSPProblem/`)

`Definitions.lean`
* `Col n k` (an edge colouring of `K_n` as a function on unordered pairs), `edgeFinset S`
  (the edges of `K` on `S`), `colorsOn c S`, `Admissible c`, `classIn c i S`.
* `classIn_card_le_two` — **the key local structure theorem**: in an admissible colouring, no
  four vertices carry three edges of one colour (i.e. every colour class meets a `K₄` in at
  most two edges).  Proved from the counting lemma `colorsOn_card_le_four`.
* `EG n` (the Erdős–Gyárfás function `f(n,4,5)` via `sInf`), `EG_le` (minimality),
  `EG_admissible` (attained), `EG_le_sq` (an explicit admissible colouring with `n²` colours),
  `FiveSixth`, `FiveSixthLower`, `FiveSixthUpper`, `fiveSixth_iff`.

`ColorClass.lean`
* `nbrsIn_card_le_two` — a vertex has **at most two neighbours in any one colour class**.
* `no_mono_triangle` (in `Main.lean`) — **no monochromatic triangle** (for `n ≥ 4`).
* `classIn_avoid` — if `v` (outside `S`) has two colour-`i` neighbours `a ≠ b` in `S`, then no
  colour-`i` edge of `S` is incident to `a` or `b`: the path `a – v – b` is an **isolated
  two-edge path** of the colour class.  This is the P₃-decomposition step of the classical
  counting argument.
* `three_of_classIn_fourSet`, `classIn_fourSet_mem`, `exists_vertex_outside` and the counting
  toolkit (`card_ge_three`, `card_fourSet`, `mem_fourSet_*`, `threeSet`, `card_threeSet`).

`Main.lean`
* `jsp_000140_target` — the statement of the required theorem, as a `def`.
* `fiveSixthLower_iff`, `fiveSixthUpper_iff`, `jsp_000140_target_iff` — a **proved reduction**
  of the headline statement to the two purely combinatorial bounds
  `AdmissibleLower 1 ∧ AdmissibleUpper 1` (all admissible `k`-colourings use `≥ 5n/6 - n`
  colours, and some admissible colouring uses `≤ 5n/6 + n`).
* `three_edges_ne`, `no_mono_triangle`, `upper_bound_sq`.

### Not yet proved (blockers, see `discovery/JSP-000140/policy.json`)

1. `three_mul_classIn_le : 3 * (classIn c i S).card ≤ 2 * S.card` — the counting lemma
   (each colour class is a disjoint union of edges and 2-edge paths, so it has at most
   `2|S|/3` edges).  The vertex-adding induction proves the deg-0 and deg-2 cases; the deg-1
   case is arithmetically false in that form and needs the *pair* removal
   (`a, v` with `a` a degree-1 neighbour), which requires `classIn_avoid` in the variant where
   the centre `v` **lies in** `S` (current `classIn_avoid` assumes `v ∉ S`).
2. `sum_card_classIn : ∑ i : Fin k, (classIn c i S).card = (edgeFinset S).card` — the colour
   classes partition the edges; needed to sum (1) over the colours.
3. From (1)+(2): `four_mul_k_ge : ∀ c : Col n k, Admissible c → 3 * (n - 1) ≤ 4 * k`, i.e. the
   **classical bound** `f(n,4,5) ≥ 3(n-1)/4`; then `FiveSixthLower EG` with `ε = 1/2`.
4. A **linear** construction (round-robin proper edge colouring of `K_n`, `n` colours) to
   replace `EG_le_sq`; with (3) this gives `|EG n - 5n/6| ≤ n/2` for `n ≥ 2`, i.e. a
   two-sided `o(n)`-shaped bound, and pins `EG n = Θ(n)`.
5. The research content itself (BCDP22): sharpen the lower bound `3/4 → 5/6` and the
   construction `1 → 5/6`.  These are the two lemmas `AdmissibleLower`/`AdmissibleUpper` for
   arbitrarily small `ε`, and they are what `jsp_000140_main` needs.
