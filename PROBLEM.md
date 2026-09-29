# JSP-000140

**How many edge colors are necessary if every four-vertex clique must contain at least five
colors?**

Catalog record: <https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0101-0200.md#JSP-000140>
(fetched 2026-09-30).  Graph theory.  Date proposed: no later than 1997.  Current status:
**Solved**.  Lean proof in the catalog: **No**.  Publications cited: `[BCDP22]` S. Banerjee,
P. Bradshaw, S. Letzter, A. Pokrovskiy, *The Erdős–Gyárfás function `f(n,4,5) = 5n/6 + o(n)`
— so Gyárfás was right*, arXiv:2207.02920 (2022); `[JoMu22]` G. J. Chang, D. M. Evans,
R. R. Munemasa, *Ramsey theory constructions from hypergraph matchings*, arXiv:2208.12563 (2022).

The quantity asked for is the **Erdős–Gyárfás function**

    f(n, p, q) = the least number of colours in an edge-colouring of K_n
                 in which every K_p spans at least q colours,

specialised to `f(n, 4, 5)`: the least number of colours needed to colour the edges of `K_n`
so that **every four-vertex clique contains at least five colours**.  The solved answer is
`f(n, 4, 5) = 5n/6 + o(n)`.

In the Lean development this number is `JSP140.EG n` (see
`lean/JSPProblem/Definitions.lean`), the catalog condition is `JSP140.Admissible`, and the
headline statement is `JSP140.jsp_000140_target = JSP140.FiveSixth EG` in
`lean/JSPProblem/Main.lean`.  Status: see `ACCEPTANCE.md`.
