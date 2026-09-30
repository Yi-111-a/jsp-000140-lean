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
