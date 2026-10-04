import JSPProblem.Miss
import JSPProblem.Extend
import JSPProblem.Singles
import JSPProblem.Surplus
import JSPProblem.Extremal

/-!
# JSP-000140 — round 75: THE COMPLETE CELL CENSUS

Rounds 71–74 read the extremal colouring off the grid `V × Palette` of `(vertex, colour)` pairs:

* round 71 (`Grid.lean`) — in the **extremal** case the crosses of the labelled triangles *cover
  the whole grid*, hence `3 a_j + 2 b_j = n` for every colour `j` (`Grid.cellCount`);
* round 72 (`Template.lean`) — the same equation re-read on the colour classes, **still in the
  extremal case** (`Template.class_eq_two_mul_cherry_add_leaf`, `|E_j| = 2 a_j + b_j`);
* round 74 (`Miss.lean`) — the **miss profile** `Miss.miss c i` for *arbitrary* admissible
  colourings, with the identity `2 |E_i| + miss_i = n + |A_i|` (`Miss.slack`) and the budget
  `6 ∑_i miss_i + 5 n (n-1) ≤ 6 n k` (`Miss.budget`).

**This file closes the loop: the cell equation of round 71 holds for EVERY admissible colouring,
with the empty cells on the right-hand side.**

    **`3 · a_i + 2 · b_i + miss_i = n`**      (`Cell.cells`)

Here `a_i = |twoA c i|` (the cherries of colour `i`) and `b_i = leaf c i` (its single edges).  The
three terms count the three kinds of cells of the column `i`:

* `3 a_i` — three cells per cherry: the centre and its two leaves;
* `2 b_i` — two cells per single edge: its two ends (both of colour-degree `1`);
* `miss_i` — the empty cells.

**Why this is not a restatement.**  `3 a_j + 2 b_j = n` of round 71 was available only when the grid
is fully covered, i.e. only at `6k = 5(n-1)`; `Miss.slack` of round 74 is the *edge-count* version
(`2 |E_i| + miss_i = n + a_i`) and does not mention the single edges at all.  The identity proved
here is the **column sum of the grid, for an arbitrary colouring**, and it is derived from the
*component structure* of the colour class (a colour class of an admissible colouring is a disjoint
union of cherries and single edges, `card_single_in_classIn`), never from a grid
decomposition.  Conversely it *re-derives* round 71's equation at the extremal order
(`Cell.cells_tight`) — a second, independent route to `Grid.cellCount`.

## The census, globally

Summing `Cell.census` over the palette:

    **`3 · Paths c + 2 · (#single edges) + (∑_i miss_i) = n · k`**

the three kinds of cells of the whole grid.  Two exact identities follow from the defect parameters
of round 65, and they are the honest accounting of rounds 65 and 74:

* **`Cell.sum_miss_eq_isolated` — `(∑_i miss_i) = Isolated c`.**  The `Isolated c` of round 65
  (`Isolated c = ∑_i |zeroA c i|`, the number of `(vertex, colour)` pairs of colour-degree `0`) **is**
  the empty-cell count of rounds 71–74.  So the miss profile of round 74 is not an independent
  invariant: it is `Isolated c`, split over the palette;
* **`Cell.refined_sum_miss` — at `6k = 5n+1` (the shape of benchmark B5) the colouring misses
  exactly `n` cells.**  Round 74 proved `∑_i miss_i ≤ n` (`Miss.budget_refined`); the bound is an
  **equality**, so an admissible `(5n+1)/6`-colouring of `K_n` has exactly `n` empty
  `(vertex, colour)` cells, i.e. on average `6n/(5n+1) < 6/5` cells per colour;
* **`Cell.budget_iff_paths`** — round 74's `Miss.budget` is *equivalent* to `6 · Paths c ≤ n (n-1)`,
  the classical `Cherry.six_mul_paths_le`.  The budget carries no information beyond the classical
  counting lemma.  Recorded as honest accounting, not as a defect.

## Consequences (search filters)

* `Cell.parity` — the number of cherries of a colour class has the **parity of the number of
  vertices carrying that colour**: `a_i ≡ n - miss_i (mod 2)` (`Cell.parity_active`:
  `a_i ≡ |active_i|`).  Round 72 could only state this at the extremal order (`a_j ≡ n`);
* `Cell.twoA_le`, `Cell.leaf_le` — `3 a_i ≤ n`, `2 b_i ≤ n`, valid for **every** colour of
  **every** admissible colouring (`Miss.three_mul_twoA_le_active` is the sharper per-class version);
* **`Cell.refined_pigeonhole` — at `6k = 5n+1` some colour class is present at all but at most one
  vertex** (`miss_i ≤ 1`), and `Cell.anchor_pigeonhole` — at `6k = 5n+6` (the shape of the verified
  witness `EG 12 = 11`) some colour class is present at at least `n - 2` vertices;
* `Cell.profile_test` — the whole per-class acceptance test of a candidate colouring at a given
  order, in one statement.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace JSP140
namespace Cell

variable {n k : ℕ}

open Classical

/-! ### §0  The single edges of a colour class -/

/-- **THE SINGLE EDGES OF THE COLOUR CLASS `i`.**  `leaf c i = |singleFinset c ∩ E_i|`: the edges of
colour `i` which are not the two edges of any two-edge path (`card_single_in_classIn` shows
this is `|E_i| - 2 a_i`).  Round 72 wrote the same number as `b_j` (`Grid.cellCount`) and could only
place it in a cell equation at the extremal order. -/
def leaf (c : Col n k) (i : Fin k) : ℕ :=
  (singleFinset c ∩ classIn c i (Finset.univ : Finset (Verts n))).card

/-! ### §1  THE CELL EQUATION, FOR AN ARBITRARY ADMISSIBLE COLOURING -/

/-- **THE DEGREE SUM OF A COLOUR CLASS, SPLIT BY COLOUR-DEGREE.**  `2 |E_i| = 2 a_i + |B_i|`
(the two edges of every cherry are counted at their two ends, the two ends of every single edge at
one each). -/
private theorem twoA_oneB_degree {c : Col n k} (hc : Admissible c) (i : Fin k) :
    2 * (classIn c i (Finset.univ : Finset (Verts n))).card
      = 2 * (twoA c i).card + (oneB c i).card := by
  have h := Miss.identity hc i
  rw [Miss.card_active] at h
  omega

private theorem twoA_oneB_degree' {c : Col n k} (hc : Admissible c) (i : Fin k) :
    2 * (classIn c i (Finset.univ : Finset (Verts n))).card
      = (Miss.active c i).card + (twoA c i).card := (Miss.identity hc i).symm

/-- **THE EDGE PROFILE OF A COLOUR CLASS.**  `|E_i| = 2 a_i + b_i` for **every** colour of **every**
admissible colouring: the colour class is a vertex-disjoint union of `a_i` cherries and `b_i`
isolated single edges.  (Rounds 71–72 could state this only in the extremal case,
`Template.class_eq_two_mul_cherry_add_leaf`.) -/
theorem class_eq_twoA_add_leaf {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n) (i : Fin k) :
    2 * (twoA c i).card + leaf c i
      = (classIn c i (Finset.univ : Finset (Verts n))).card := by
  have hle := two_mul_twoA_le_classIn hc hn i
  have h := card_single_in_classIn hc hn i
  calc 2 * (twoA c i).card + leaf c i = leaf c i + 2 * (twoA c i).card := by ring
    _ = (classIn c i (Finset.univ : Finset (Verts n))).card := by
        rw [leaf, h]
        exact Nat.sub_add_cancel hle

/-- **THE HAND SHAKE OF A COLOUR CLASS.**  `|B_i| = 2 (a_i + b_i) = 2 · (#components of `E_i`)`: the
degree-`1` vertices of colour `i` are exactly the two leaves of every cherry together with the two
ends of every single edge.  `Extremal.oneB_even` is its parity shadow. -/
theorem oneB_eq_two_mul_components {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n) (i : Fin k) :
    (oneB c i).card = 2 * ((twoA c i).card + leaf c i) := by
  have h1 := twoA_oneB_degree hc i
  have h2 := class_eq_twoA_add_leaf hc hn i
  have h3 := Miss.card_active (c := c) i
  omega

/-- **THE CELL EQUATION.**  For every colour `i` of every admissible colouring of `K_n` (`n ≥ 4`):

    **`3 · a_i + 2 · b_i + miss_i = n`**,

i.e. the `n` cells of the column `i` of the `(vertex, colour)` grid are covered by three cells per
cherry, two per single edge, and the empty cells.  Round 71's `Grid.cellCount`
(`3 a_j + 2 b_j = n`) is the case `miss_j = 0`. -/
theorem cells {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n) (i : Fin k) :
    3 * (twoA c i).card + 2 * leaf c i + Miss.miss c i = n := by
  have h5 : 4 * (twoA c i).card + 2 * leaf c i
      = 2 * (classIn c i (Finset.univ : Finset (Verts n))).card := by
    calc 4 * (twoA c i).card + 2 * leaf c i
        = 2 * (2 * (twoA c i).card + leaf c i) := by ring
      _ = 2 * (classIn c i (Finset.univ : Finset (Verts n))).card :=
          class_eq_twoA_add_leaf hc hn i ▸ rfl
  have h7 : (3 * (twoA c i).card + 2 * leaf c i) + (twoA c i).card
      = (Miss.active c i).card + (twoA c i).card := by
    calc (3 * (twoA c i).card + 2 * leaf c i) + (twoA c i).card
        = 4 * (twoA c i).card + 2 * leaf c i := by ring
      _ = 2 * (classIn c i (Finset.univ : Finset (Verts n))).card := h5
      _ = (Miss.active c i).card + (twoA c i).card := twoA_oneB_degree' hc i
  have hkey : 3 * (twoA c i).card + 2 * leaf c i = (Miss.active c i).card := Nat.add_right_cancel h7
  have hmiss := Miss.miss_add_active (c := c) i
  calc 3 * (twoA c i).card + 2 * leaf c i + Miss.miss c i
      = (Miss.active c i).card + Miss.miss c i := by rw [hkey]
    _ = n := (Nat.add_comm _ _).trans hmiss

/-- **THE CELL EQUATION WITHOUT THE EMPTY CELLS.**  The column `i` of the grid holds exactly
`3 a_i + 2 b_i` covered cells. -/
theorem covered_cells {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n) (i : Fin k) :
    n - Miss.miss c i = 3 * (twoA c i).card + 2 * leaf c i := by
  have h := cells hc hn i
  omega

/-- **THE VERTEX COUNT OF A COLOUR CLASS.**  `|active_i| = 3 a_i + 2 b_i`: the vertices carrying
colour `i` are the centre and the two leaves of every cherry and the two ends of every single
edge. -/
theorem active_eq {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n) (i : Fin k) :
    (Miss.active c i).card = 3 * (twoA c i).card + 2 * leaf c i := by
  have h1 := cells hc hn i
  have h2 := Miss.miss_add_active (c := c) i
  omega

/-- **ROUND 71'S CELL EQUATION, RE-DERIVED.**  At the extremal order `6k = 5(n-1)` the grid is fully
covered (`Miss.tight_all_active`, i.e. `Grid.decomposes_of_tight` in per-colour language), so

    `3 · a_i + 2 · b_i = n`

for every colour — the equation of `Grid.cellCount`, obtained here from the component structure of
the colour class and not from a grid decomposition. -/
theorem cells_tight {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n) (hk : 6 * k = 5 * (n - 1))
    (i : Fin k) : 3 * (twoA c i).card + 2 * leaf c i = n := by
  have h1 := cells hc hn i
  have h0 := Miss.tight_all_active hc hn hk i
  omega

/-! ### §2  The per-class consequences -/

private lemma three_add_two_mod_two (a b : ℕ) : (3 * a + 2 * b) % 2 = a % 2 := by
  have e : 3 * a + 2 * b = a + 2 * (a + b) := by ring
  rw [e]
  have h2 : (2 * (a + b)) % 2 = 0 := by
    rw [Nat.mul_mod]
    show (2 % 2) * ((a + b) % 2) % 2 = 0
    rw [show (2 : ℕ) % 2 = 0 by omega, Nat.zero_mul]
  rw [Nat.add_mod, h2, Nat.add_zero]
  exact Nat.mod_eq_of_lt (by omega)

/-- **THE PARITY OF THE CHERRY COUNT.**  `a_i ≡ n - miss_i (mod 2)`: the number of cherries of a
colour class has the parity of the number of vertices carrying that colour.  (Round 72's
`Template.cherry_parity`, `a_j ≡ n`, is the case `miss_j = 0`.) -/
theorem parity {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n) (i : Fin k) :
    (twoA c i).card % 2 = (n - Miss.miss c i) % 2 := by
  have h := covered_cells hc hn i
  rw [h]
  exact (three_add_two_mod_two _ _).symm

/-- **THE PARITY IN THE `active` LANGUAGE.**  `a_i ≡ |active_i| (mod 2)`. -/
theorem parity_active {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n) (i : Fin k) :
    (twoA c i).card % 2 = (Miss.active c i).card % 2 := by
  have h := active_eq hc hn i
  rw [h]
  exact (three_add_two_mod_two _ _).symm

/-- **THE PER-CLASS WINDOW OF THE CHERRIES.**  `3 a_i ≤ n`: a colour class carries at most `n/3`
cherries.  (`Miss.three_mul_twoA_le_active` is the sharper version `3 a_i ≤ |active_i|`.) -/
theorem twoA_le {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n) (i : Fin k) :
    3 * (twoA c i).card ≤ n := by
  have h := cells hc hn i
  omega

/-- **THE PER-CLASS WINDOW OF THE SINGLE EDGES.**  `2 b_i ≤ n`. -/
theorem leaf_le {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n) (i : Fin k) :
    2 * leaf c i ≤ n := by
  have h := cells hc hn i
  omega

/-! ### §3  THE CENSUS: THE THREE KINDS OF CELLS OF THE WHOLE GRID -/

/-- **THE SINGLE EDGES SPLIT OVER THE COLOUR CLASSES.**  `∑_i b_i = #single edges`: the single edges
of `K_n` are partitioned by their colour (`card_singleFinset` counts them globally). -/
theorem sum_leaf_eq {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n) :
    (∑ i : Fin k, leaf c i) = (singleFinset c).card := by
  have hkey : ∀ i : Fin k,
      2 * (twoA c i).card + leaf c i
        = (classIn c i (Finset.univ : Finset (Verts n))).card :=
    fun i => class_eq_twoA_add_leaf hc hn i
  have h5 : (∑ i : Fin k, (classIn c i (Finset.univ : Finset (Verts n))).card)
      = ∑ i : Fin k, (2 * (twoA c i).card + leaf c i) :=
    Finset.sum_congr rfl fun i _ => (hkey i).symm
  have hmul : (∑ i : Fin k, 2 * (twoA c i).card) = 2 * ∑ i : Fin k, (twoA c i).card :=
    (Finset.mul_sum (Finset.univ : Finset (Fin k)) (fun i : Fin k => (twoA c i).card) 2).symm
  have h6 : (∑ i : Fin k, (2 * (twoA c i).card + leaf c i))
      = (∑ i : Fin k, leaf c i) + 2 * ∑ i : Fin k, (twoA c i).card := by
    rw [Finset.sum_add_distrib, ← hmul]
    exact Nat.add_comm _ _
  have hle : 2 * ∑ i : Fin k, (twoA c i).card
      ≤ ∑ i : Fin k, (classIn c i (Finset.univ : Finset (Verts n))).card := by
    rw [← hmul]
    exact Finset.sum_le_sum fun i _ => two_mul_twoA_le_classIn hc hn i
  have key : (∑ i : Fin k, (classIn c i (Finset.univ : Finset (Verts n))).card)
      - 2 * ∑ i : Fin k, (twoA c i).card = ∑ i : Fin k, leaf c i := by
    rw [h5, h6]
    omega
  rw [← key]
  calc (∑ i : Fin k, (classIn c i (Finset.univ : Finset (Verts n))).card)
      - 2 * ∑ i : Fin k, (twoA c i).card
      = (edgeFinset (Finset.univ : Finset (Verts n))).card - 2 * Paths c := by
        rw [sum_card_classIn c (Finset.univ : Finset (Verts n)), Paths]
    _ = (singleFinset c).card := (card_singleFinset hc hn).symm

private theorem sum_n (n k : ℕ) : (∑ _i : Fin k, (n : ℕ)) = n * k := by
  calc (∑ _i : Fin k, (n : ℕ)) = (Finset.univ : Finset (Fin k)).card • n := Finset.sum_const _
    _ = Fintype.card (Fin k) * n := by rw [Finset.card_univ]; exact nsmul_eq_mul _ _
    _ = n * k := by rw [Fintype.card_fin, Nat.mul_comm]

/-- **THE CENSUS OF THE THREE KINDS OF CELLS.**  For every admissible colouring of `K_n` with `k`
colours,

    **`3 · Paths c + 2 · (#single edges) + (∑_i miss_i) = n · k`**,

the three kinds of `(vertex, colour)` cells of the grid of rounds 71–74: the cherry cells, the
single-edge cells and the empty cells.  `3 Paths c + 2 (#single edges)` is the number of covered
cells and `n k` the size of the grid. -/
theorem census {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n) :
    3 * Paths c + 2 * (singleFinset c).card + (∑ i : Fin k, Miss.miss c i) = n * k := by
  have hkey : ∀ i : Fin k,
      3 * (twoA c i).card + 2 * leaf c i + Miss.miss c i = n := fun i => cells hc hn i
  have h1 : (∑ i : Fin k, (3 * (twoA c i).card + 2 * leaf c i + Miss.miss c i))
      = ∑ _i : Fin k, n := Finset.sum_congr rfl fun i _ => hkey i
  have h2 : (∑ i : Fin k, (3 * (twoA c i).card + 2 * leaf c i + Miss.miss c i))
      = 3 * ∑ i : Fin k, (twoA c i).card + 2 * ∑ i : Fin k, leaf c i
        + ∑ i : Fin k, Miss.miss c i := by
    calc (∑ i : Fin k, (3 * (twoA c i).card + 2 * leaf c i + Miss.miss c i))
        = (∑ i : Fin k, (3 * (twoA c i).card + 2 * leaf c i))
            + ∑ i : Fin k, Miss.miss c i := by rw [Finset.sum_add_distrib]
      _ = ((∑ i : Fin k, 3 * (twoA c i).card) + ∑ i : Fin k, 2 * leaf c i)
            + ∑ i : Fin k, Miss.miss c i := by rw [Finset.sum_add_distrib]
      _ = 3 * ∑ i : Fin k, (twoA c i).card + 2 * ∑ i : Fin k, leaf c i
            + ∑ i : Fin k, Miss.miss c i := by
          rw [Finset.mul_sum (Finset.univ : Finset (Fin k))
              (fun i : Fin k => (twoA c i).card) 3,
            Finset.mul_sum (Finset.univ : Finset (Fin k)) (fun i : Fin k => leaf c i) 2]
  calc 3 * Paths c + 2 * (singleFinset c).card + (∑ i : Fin k, Miss.miss c i)
      = 3 * ∑ i : Fin k, (twoA c i).card + 2 * ∑ i : Fin k, leaf c i
        + ∑ i : Fin k, Miss.miss c i := by
        rw [Paths, sum_leaf_eq hc hn]
    _ = ∑ i : Fin k, (3 * (twoA c i).card + 2 * leaf c i + Miss.miss c i) := h2.symm
    _ = ∑ _i : Fin k, n := h1
    _ = n * k := sum_n n k

/-- **THE EMPTY CELLS OF A COLOURING ARE THE `Isolated c` OF ROUND 65.**  `Isolated c` counts the
`(vertex, colour)` pairs of colour-degree `0` (`Isolated c = ∑_i |zeroA c i|`, and
`zeroA c i` is the complement of `twoA c i ∪ oneB c i = Miss.active c i` in `K_n`); the miss census
of rounds 71–74 counts the same pairs.  So the whole miss profile of round 74 is `Isolated c`, split
over the palette: it is not an independent invariant. -/
theorem sum_miss_eq_isolated {c : Col n k} (hc : Admissible c) :
    (∑ i : Fin k, Miss.miss c i) = Isolated c := by
  have key : ∀ i : Fin k, Miss.miss c i = (zeroA c i).card := by
    intro i
    have h1 := Miss.miss_add_active (c := c) i
    have h2 := Miss.card_active (c := c) i
    have h3 := card_twoA_oneB_zeroA hc i
    omega
  calc (∑ i : Fin k, Miss.miss c i) = ∑ i : Fin k, (zeroA c i).card :=
      Finset.sum_congr rfl fun i _ => key i
    _ = Isolated c := rfl

/-- **THE MISS CENSUS IN TERMS OF THE DEFECT PARAMETERS.**  `∑_i miss_i = n k + Paths c - n (n-1)`
(`global_identity`): the empty-cell count is determined by `n`, `k` and the number of
two-edge paths alone. -/
theorem sum_miss_eq_surplus {c : Col n k} (hc : Admissible c) :
    (∑ i : Fin k, Miss.miss c i) = n * k + Paths c - n * (n - 1) := by
  have h1 := sum_miss_eq_isolated hc
  have h2 := global_identity hc
  omega

/-- **THE REFINED ORDER: EXACTLY `n` EMPTY CELLS.**  If `6k = 5n+1` and `k+2 ≤ n` (the shape of
benchmark B5, `EG 13 = 11`) then

    **`∑_i miss_i = n`**

— round 74's `Miss.budget_refined` (`∑_i miss_i ≤ n`) is an **equality**.  An admissible
`(5n+1)/6`-colouring of `K_n` therefore misses exactly `n` of its `n(5n+1)/6` cells, i.e. on average
`6n/(5n+1) < 6/5` cells per colour, and (by `Cell.refined_pigeonhole`) one colour class is present
at all but at most one vertex. -/
theorem refined_sum_miss {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n) (hk : k + 2 ≤ n)
    (heq : 6 * k = 5 * n + 1) : (∑ i : Fin k, Miss.miss c i) = n := by
  have h1 := sum_miss_eq_isolated hc
  have h2 := isolated_eq_n_defect_eq_zero hc hn hk heq
  omega

/-- **THE EXTREMAL ORDER: NO EMPTY CELL.**  At `6k = 5(n-1)` the colouring covers its grid
completely: `∑_i miss_i = 0` (this is `Miss.budget_tight`, restated in the census form). -/
theorem extremal_sum_miss {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n) (hk : 6 * k = 5 * (n - 1)) :
    (∑ i : Fin k, Miss.miss c i) = 0 := Miss.budget_tight hc hn hk

/-- **THE MISS BUDGET IS THE CLASSICAL COUNTING LEMMA.**  Round 74's `Miss.budget`
(`6 ∑_i miss_i + 5 n (n-1) ≤ 6 n k`) is *equivalent* to `6 Paths c ≤ n (n-1)`, the classical
`Cherry.six_mul_paths_le`: once `∑_i miss_i = n k + Paths c - n (n-1)` is known, the budget carries
no information beyond the classical counting lemma.  Recorded as honest accounting. -/
theorem budget_iff_paths {c : Col n k} (hc : Admissible c) :
    6 * (∑ i : Fin k, Miss.miss c i) + 5 * (n * (n - 1)) ≤ 6 * (n * k)
      ↔ 6 * Paths c ≤ n * (n - 1) := by
  have hrel : (∑ i : Fin k, Miss.miss c i) + (n * (n - 1)) = n * k + Paths c := by
    have h2 := global_identity hc
    have hle : n * (n - 1) ≤ n * k + Paths c := by omega
    have h := sum_miss_eq_surplus hc
    rw [h]
    exact Nat.sub_add_cancel hle
  have hkey : (6 * (∑ i : Fin k, Miss.miss c i) + 5 * (n * (n - 1))) + (n * (n - 1))
      = 6 * (n * k) + 6 * Paths c := by
    calc (6 * (∑ i : Fin k, Miss.miss c i) + 5 * (n * (n - 1))) + (n * (n - 1))
        = 6 * ((∑ i : Fin k, Miss.miss c i) + n * (n - 1)) := by ring
      _ = 6 * (n * k + Paths c) := by rw [hrel]
      _ = 6 * (n * k) + 6 * Paths c := by ring
  constructor
  · intro h
    have h1 : 6 * (n * k) + 6 * Paths c ≤ 6 * (n * k) + n * (n - 1) := by
      rw [← hkey]
      exact Nat.add_le_add_right h _
    exact Nat.le_of_add_le_add_left h1
  · intro h
    have h1 : 6 * (n * k) + 6 * Paths c ≤ 6 * (n * k) + n * (n - 1) :=
      Nat.add_le_add_left h (6 * (n * k))
    have h2 : (6 * (∑ i : Fin k, Miss.miss c i) + 5 * (n * (n - 1))) + (n * (n - 1))
        ≤ 6 * (n * k) + n * (n - 1) := by
      rw [hkey]
      exact h1
    exact Nat.le_of_add_le_add_right h2

/-! ### §4  Pigeonhole consequences: the profiles a candidate must have -/

/-- **AT THE REFINED ORDER SOME COLOUR CLASS IS ALMOST COMPLETE.**  If `6k = 5n+1` and `k+2 ≤ n`
then some colour class is present at all but at most **one** of the `n` vertices
(`Cell.refined_sum_miss` gives `∑_i miss_i = n`, and `2 k > n`).  For `n = 13, k = 11` this says:
an admissible 11-colouring of `K₁₃` — if it exists — has a colour class present at `12` or `13`
vertices, hence a profile `(a_i, b_i)` with `3 a_i + 2 b_i ∈ {12, 13}`, i.e. one of
`(0,6), (1,5), (2,3), (3,2), (4,0)`. -/
theorem refined_pigeonhole {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n) (hk : k + 2 ≤ n)
    (heq : 6 * k = 5 * n + 1) : ∃ i : Fin k, Miss.miss c i ≤ 1 := by
  have h1 := refined_sum_miss hc hn hk heq
  have h2 : 2 * k > n := by
    obtain ⟨q, hq⟩ := Nat.exists_eq_add_of_le (by omega)
    omega
  by_contra hcon
  push_neg at hcon
  have h3 : (∑ i : Fin k, Miss.miss c i) ≥ 2 * k := by
    calc (∑ i : Fin k, Miss.miss c i) ≥ ∑ _i : Fin k, (2 : ℕ) := Finset.sum_le_sum fun i _ => hcon i
      _ = 2 * k := sum_n _ _
  omega

/-- **AT THE ANCHOR ORDER SOME COLOUR CLASS IS ALMOST COMPLETE.**  If `6k = 5n+6` (the shape of the
verified witness `EG 12 = 11`) then some colour class is present at at least `n - 2` vertices: a
candidate colouring of `K₁₂` with 11 colours has a colour class on at least `10` vertices. -/
theorem anchor_pigeonhole {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n) (hk : 6 * k = 5 * n + 6) :
    ∃ i : Fin k, Miss.miss c i ≤ 2 := by
  have h1 := Miss.budget_anchor hc hn hk
  have h2 : 3 * k > 11 * n / 6 := by
    obtain ⟨q, hq⟩ := Nat.exists_eq_add_of_le (by omega)
    omega
  by_contra hcon
  push_neg at hcon
  have h3 : (∑ i : Fin k, Miss.miss c i) ≥ 3 * k := by
    calc (∑ i : Fin k, Miss.miss c i) ≥ ∑ _i : Fin k, (3 : ℕ) := Finset.sum_le_sum fun i _ => hcon i
      _ = 3 * k := sum_n _ _
  omega

/-! ### §5  The whole per-class acceptance test -/

/-- **THE PER-CLASS ACCEPTANCE TEST.**  For every colour `i` of an admissible colouring of `K_n`
(`n ≥ 4`) the three statements

    `|E_i| = 2 a_i + b_i`,   `|B_i| = 2 (a_i + b_i)`,   `3 a_i + 2 b_i + miss_i = n`

hold simultaneously: the colour class is a disjoint union of `a_i` cherries and `b_i` single edges
covering `3 a_i + 2 b_i` of the `n` cells of its own column.  This is the complete local acceptance
test for a candidate colouring, in the profile language of rounds 71–74. -/
theorem profile_test {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n) (i : Fin k) :
    2 * (twoA c i).card + leaf c i
        = (classIn c i (Finset.univ : Finset (Verts n))).card
      ∧ (oneB c i).card = 2 * ((twoA c i).card + leaf c i)
      ∧ 3 * (twoA c i).card + 2 * leaf c i + Miss.miss c i = n :=
  ⟨class_eq_twoA_add_leaf hc hn i, oneB_eq_two_mul_components hc hn i, cells hc hn i⟩

/-- **THE PROFILE OF THAT COLOUR CLASS.**  Under the hypotheses of `Cell.refined_pigeonhole` there is
a colour `i` with `n - 1 ≤ 3 a_i + 2 b_i`: the almost-complete colour class covers all but at most
one cell of its own column. -/
theorem refined_profile {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n) (hk : k + 2 ≤ n)
    (heq : 6 * k = 5 * n + 1) :
    ∃ i : Fin k, Miss.miss c i ≤ 1 ∧ 3 * (twoA c i).card + 2 * leaf c i ≥ n - 1 := by
  obtain ⟨i, hi⟩ := refined_pigeonhole hc hn hk heq
  obtain ⟨h1, h2, h3⟩ := profile_test hc hn i
  refine ⟨i, hi, ?_⟩
  omega

end Cell
end JSP140