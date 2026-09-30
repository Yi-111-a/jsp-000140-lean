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
