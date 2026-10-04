import JSPProblem.Cell
import JSPProblem.Pairs
import JSPProblem.Rigidity

/-!
# JSP-000140 — the **collision identity**, corrected: the four-set spectrum is a function of the
`(vertex, colour)` cell profile

Round 14 of this development (`ACCEPTANCE.md`, §15) named, as "the missing lemma needed to turn the
first two items into Lean theorems", the **collision identity**

    `4 · Paths c  +  Σᵢ binom(componentsᵢ, 2)  =  Σ_{|S| = 4} (6 − colours(S))`,

with the remark "each two-edge path lies in exactly `n−3` four-subsets, each pair of components of
one colour spans exactly one four-subset, and each four-subset carries at most one repeated
colour".  **Both numbers of that formula are wrong**, and the errors are of different kinds:

* a two-edge path lies in `n − 3` four-subsets, **not in `4`**, so the path term is
  `(n − 3) · Paths`;
* a pair of *components* does not in general span one four-subset: a **single edge** together with
  a **two-edge path** of the same colour determines **two** disjoint pairs (each of the two edges
  of the path is disjoint from the single edge), and two two-edge paths determine **four**.  The
  right weight of a pair of components is therefore not `binom(·, 2)` but the number of *disjoint
  pairs of edges* the two components determine.

This file proves the corrected identity, verifies it numerically on the explicit colourings of
`Tables.lean`, **refutes the naive identity of round 14 by computation** (§5), and reads the whole
four-set spectrum off the `(vertex, colour)` cell accounting of `Cell.lean` (§3) — the first time
the two halves of this development (the four-set census of rounds 60–62 and the grid accounting of
rounds 71–75) occur in one formula.

## Main results

* **`card_fiveFourSets_eq_sum_collision`** — the total collision count `Σ_{|S| = 4} (6 − colours(S))`
  is the number of five-coloured four-sets;
* **`card_fiveFourSets_disj` — THE CORRECTED COLLISION IDENTITY**

      `|fiveFourSets c| = (n − 3) · Paths c + Σᵢ |disjPairs c i|`,

  every collision of a `K₄` being either a two-edge path (in `n − 3` four-sets) or a pair of
  *disjoint* same-coloured edges (in exactly one);
* **`disjPairs_cell` — THE CLOSED FORM OF THE COLLISION COUNT OF ONE COLOUR**

      `2 |disjPairs c i| + 2 missᵢ + 5 |Eᵢ| = |Eᵢ|² + 2n`,

  and **`disjPairs_components`**, its component-by-component reading
  `2|disjPairs c i| = 8binom(aᵢ,2) + 4aᵢbᵢ + 2binom(bᵢ,2)` — "two cherries span four disjoint
  pairs, a cherry and a single edge two, two single edges one", the weight the naive identity of
  round 14 replaced by `binom(componentsᵢ,2)`;
* **`card_fiveFourSets_cell` — THE SPECTRUM IS A FUNCTION OF THE CELL PROFILE**

      `2|fiveFourSets c| + 2Σᵢmissᵢ + 5|E(K_n)| = 2(n−3)·Paths c + Σᵢ|Eᵢ|² + 2nk`,

  and its extremal form **`card_fiveFourSets_cell_tight`**
  `12|fiveFourSets c| = 6Σᵢ|Eᵢ|² + n(n−1)(2n−11)`;
* **`card_fiveFourSets_ge`, `tight_fourSets_eq`, `tight_fourSets_ge_four` — A DENSITY STATEMENT FOR
  THE EXTREMAL CASE**: in an extremal colouring of `K_n` at least the fraction `4/(n−2)` of the
  four-vertex sets span exactly five colours, and the excess over that fraction is exactly
  `(n−2) Σᵢ |disjPairs c i|`;
* **`naive_ne_nineCol` (with `naive_ne_tenCol`, `naive_ne_elevenCol`) — THE ROUND-14 IDENTITY IS
  FALSE**: for the certified colouring `Tables.nineCol` of `K₉` the naive right-hand side is `64`
  while the true collision count is `84`.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

namespace JSP140

variable {n k : ℕ}

open Classical

/-! ### §1  collisions of a vertex set -/

/-- **THE COLLISION COUNT OF A VERTEX SET**: how many of the `6` edge colours of its complete graph
are repeats, i.e. `6 − |colours(S)|`.  For a four-element `S` of an admissible colouring it is `0`
or `1` (`collision_le_one`) and it counts the *doubled* colours of `S` exactly
(`collision_eq_doubledIn`). -/
def collision {n k : ℕ} (c : Col n k) (S : Finset (Verts n)) : ℕ := 6 - (colorsOn c S).card

/-- **A FOUR-SET CARRIES AT MOST ONE COLLISION** — the local form of admissibility. -/
theorem collision_le_one {n k : ℕ} {c : Col n k} (hc : Admissible c) {S : Finset (Verts n)}
    (hS : S.card = 4) : collision c S ≤ 1 := by
  rcases card_colorsOn_four_five_or_six hc hS with h5 | h6
  · unfold collision; omega
  · unfold collision; omega

/-- The collision count of a four-set is its number of doubled colours. -/
theorem collision_eq_doubledIn {n k : ℕ} {c : Col n k} (hc : Admissible c) {S : Finset (Verts n)}
    (hS : S.card = 4) : collision c S = (doubledIn c S).card := by
  have h := card_colorsOn_add_doubledIn hc hS
  unfold collision
  omega

/-! ### §2  the total collision count -/

/-- **THE TOTAL COLLISION COUNT IS THE NUMBER OF FIVE-COLOURED FOUR-SETS.**  Each of the `binom(n,4)`
four-sets of an admissible colouring carries `0` or `1` collisions, and it carries `1` exactly when
it spans five colours. -/
theorem card_fiveFourSets_eq_sum_collision {n k : ℕ} {c : Col n k} (hc : Admissible c) :
    (fiveFourSets c).card = ∑ S ∈ (fourSets n : Finset (Finset (Verts n))), collision c S := by
  rw [fiveFourSets, Finset.card_eq_sum_ones, Finset.sum_filter]
  refine Finset.sum_congr rfl ?_
  intro S hS
  have h56 := card_colorsOn_four_five_or_six hc (mem_fourSets.mp hS)
  by_cases h5 : (colorsOn c S).card = 5
  · rw [if_pos h5]
    unfold collision
    omega
  · rw [if_neg h5]
    have h6 : (colorsOn c S).card = 6 := h56.resolve_left h5
    unfold collision
    omega

/-- **THE CORRECTED COLLISION IDENTITY.**  For every admissible colouring of `K_n` (`n ≥ 4`):

    **`|fiveFourSets c| = (n − 3) · Paths c + Σᵢ |disjPairs c i|`**

i.e. the total number of collisions of `K_n` is the number of *adjacent* same-coloured pairs (one
per two-edge path, each lying in `n − 3` four-sets) plus the number of *disjoint* same-coloured
pairs (each lying in exactly one four-set).  This is the identity round 14 named, with both of its
coefficients corrected; the naive form is refuted in §5. -/
theorem card_fiveFourSets_disj {n k : ℕ} {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n) :
    (fiveFourSets c).card = (n - 3) * Paths c + ∑ i : Fin k, (disjPairs c i).card := by
  have hsub : ∀ i : Fin k, meetingFourSets c i ⊆ twoFourSets c i := by
    intro i S hS
    obtain ⟨v, hv, hpath⟩ := (mem_meetingFourSets i).mp hS
    obtain ⟨h1, h2, _, _⟩ := mem_pathFourSets.mp hpath
    exact mem_twoFourSets.mpr ⟨h1, h2⟩
  rw [← sum_twoFourSets hc]
  calc ∑ i : Fin k, (twoFourSets c i).card
      = ∑ i : Fin k, ((meetingFourSets c i).card + (nonMeetingFourSets c i).card) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        have h := Finset.card_sdiff_of_subset (hsub i)
        have hsd : (nonMeetingFourSets c i).card
            = (twoFourSets c i).card - (meetingFourSets c i).card := h
        have hle := Finset.card_le_card (hsub i)
        omega
    _ = ∑ i : Fin k, ((twoA c i).card * (n - 3) + (disjPairs c i).card) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [card_meetingFourSets hc i hn, card_nonMeetingFourSets hc i]
    _ = (n - 3) * Paths c + ∑ i : Fin k, (disjPairs c i).card := by
        have hP : Paths c = ∑ i : Fin k, (twoA c i).card := rfl
        have hL : (∑ i : Fin k, (twoA c i).card * (n - 3))
            = (n - 3) * ∑ i : Fin k, (twoA c i).card := by
          calc (∑ i : Fin k, (twoA c i).card * (n - 3))
              = ∑ i : Fin k, (n - 3) * (twoA c i).card :=
                Finset.sum_congr rfl fun i _ => Nat.mul_comm _ _
            _ = (n - 3) * ∑ i : Fin k, (twoA c i).card := by rw [← Finset.mul_sum]
        rw [Finset.sum_add_distrib, hL, hP]

/-- The corrected identity, in the form of a total collision count. -/
theorem sum_collision_eq_disj {n k : ℕ} {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n) :
    (∑ S ∈ (fourSets n : Finset (Finset (Verts n))), collision c S)
      = (n - 3) * Paths c + ∑ i : Fin k, (disjPairs c i).card := by
  rw [← card_fiveFourSets_eq_sum_collision hc, card_fiveFourSets_disj hc hn]

/-! ### §3  the closed form: the spectrum is a function of the cell profile -/

/-- **THE PAIRS OF COLOUR-`i` EDGES, COUNTED**: `2|disjPairs c i| + 2|twoA c i| = |Eᵢ|(|Eᵢ|−1)`.
The disjoint pairs are all pairs of distinct colour-`i` edges except the `|twoA c i|` pairs of
edges of a two-edge path, and both sides are counted twice. -/
theorem two_mul_disjPairs {n k : ℕ} {c : Col n k} (hc : Admissible c) (i : Fin k) :
    2 * (disjPairs c i).card + 2 * (twoA c i).card
      = (classF c i).card * ((classF c i).card - 1) := by
  have h1 := sum_card_meet_disj hc i
  have h2 := card_meetPairs hc i
  have h3 := two_mul_choose_two (classF c i).card
  calc 2 * (disjPairs c i).card + 2 * (twoA c i).card
      = 2 * ((disjPairs c i).card + (twoA c i).card) := by ring
    _ = 2 * ((meetPairs c i).card + (disjPairs c i).card) := by rw [← h2, add_comm]
    _ = 2 * Nat.choose (classF c i).card 2 := by rw [h1]
    _ = (classF c i).card * ((classF c i).card - 1) := h3

private theorem mul_pred_add (m : ℕ) : m * (m - 1) + m = m * m := by
  cases m with
  | zero => simp
  | succ r =>
      show (r + 1) * ((r + 1) - 1) + (r + 1) = (r + 1) * (r + 1)
      rw [Nat.add_sub_cancel]
      ring

/-- **THE CLOSED FORM OF THE COLLISION COUNT OF ONE COLOUR.**  For every colour `i` of every
admissible colouring,

    **`2 |disjPairs c i| + 2 missᵢ + 5 |Eᵢ| = |Eᵢ|² + 2n`**.

So the number of disjoint pairs of a colour class is a quadratic function of the size of the class
and of the number of vertices that colour misses (`Miss.miss`).  This is the first formula in which
the pair census (`Pairs.disjPairs`) and the cell accounting (`Miss.miss`) meet. -/
theorem disjPairs_cell {n k : ℕ} {c : Col n k} (hc : Admissible c) (i : Fin k) :
    2 * (disjPairs c i).card + 2 * Miss.miss c i + 5 * (classF c i).card
      = (classF c i).card * (classF c i).card + 2 * n := by
  have h1 := two_mul_disjPairs hc i
  have h2 := Miss.slack hc i
  have h2' : 2 * (classF c i).card + Miss.miss c i = n + (twoA c i).card := h2
  have h3 := mul_pred_add (classF c i).card
  have h5 : 2 * (disjPairs c i).card + 2 * (twoA c i).card + (classF c i).card
      = (classF c i).card * (classF c i).card := by omega
  have h6 : 4 * (classF c i).card + 2 * Miss.miss c i
      = 2 * n + 2 * (twoA c i).card := by
    calc 4 * (classF c i).card + 2 * Miss.miss c i
        = 2 * (2 * (classF c i).card + Miss.miss c i) := by ring
      _ = 2 * (n + (twoA c i).card) := by rw [h2']
      _ = 2 * n + 2 * (twoA c i).card := by ring
  rw [h5.symm]
  omega

/-- **THE COLLISION COUNT OF ONE COLOUR, COMPONENT BY COMPONENT.**  With `aᵢ = |twoA c i|` cherries
and `bᵢ = |Cell.leaf c i|` single edges of colour `i`,

    **`2 |disjPairs c i| = 8 binom(aᵢ,2) + 4 aᵢ bᵢ + 2 binom(bᵢ,2)`**:

**two cherries of one colour span four disjoint pairs, a cherry and a single edge two, two single
edges one.**  This is the correct weight of a pair of components, and it is *not*
`binom(componentsᵢ,2)`. -/
theorem disjPairs_components {n k : ℕ} {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n) (i : Fin k) :
    2 * (disjPairs c i).card + 4 * (twoA c i).card + Cell.leaf c i
      = 8 * Nat.choose (twoA c i).card 2 + 4 * (twoA c i).card * Cell.leaf c i
        + 2 * Nat.choose (Cell.leaf c i) 2 + 4 * (twoA c i).card + Cell.leaf c i := by
  have h1 := two_mul_disjPairs hc i
  have h2 := Cell.class_eq_twoA_add_leaf hc hn i
  have h2' : 2 * (twoA c i).card + Cell.leaf c i = (classF c i).card := h2
  have h3 := two_mul_choose_two (twoA c i).card
  have h4 := two_mul_choose_two (Cell.leaf c i)
  have h7 := mul_pred_add (twoA c i).card
  have h8 := mul_pred_add (Cell.leaf c i)
  have h5 : 2 * (disjPairs c i).card + 2 * (twoA c i).card + (classF c i).card
      = (classF c i).card * (classF c i).card := by
    calc 2 * (disjPairs c i).card + 2 * (twoA c i).card + (classF c i).card
        = (classF c i).card * ((classF c i).card - 1) + (classF c i).card := by omega
      _ = (classF c i).card * (classF c i).card := mul_pred_add _
  have h5' : 2 * (disjPairs c i).card + 2 * (twoA c i).card
      + (2 * (twoA c i).card + Cell.leaf c i)
      = (2 * (twoA c i).card + Cell.leaf c i) * (2 * (twoA c i).card + Cell.leaf c i) := by
    rw [← h2'] at h5
    exact h5
  have h11 : 2 * (disjPairs c i).card + 4 * (twoA c i).card + Cell.leaf c i
      = (2 * (twoA c i).card + Cell.leaf c i) * (2 * (twoA c i).card + Cell.leaf c i) := by
    calc 2 * (disjPairs c i).card + 4 * (twoA c i).card + Cell.leaf c i
        = 2 * (disjPairs c i).card + 2 * (twoA c i).card
            + (2 * (twoA c i).card + Cell.leaf c i) := by ring
      _ = _ := h5'
  have h9 : (2 * (twoA c i).card + Cell.leaf c i) * (2 * (twoA c i).card + Cell.leaf c i)
      = 4 * ((twoA c i).card * (twoA c i).card) + 4 * (twoA c i).card * Cell.leaf c i
        + (Cell.leaf c i * Cell.leaf c i) := by ring
  have h10 : 2 * (disjPairs c i).card + 4 * (twoA c i).card + Cell.leaf c i
      = 4 * ((twoA c i).card * ((twoA c i).card - 1))
          + 4 * (twoA c i).card * Cell.leaf c i
          + (Cell.leaf c i * (Cell.leaf c i - 1)) + 4 * (twoA c i).card + Cell.leaf c i := by
    calc 2 * (disjPairs c i).card + 4 * (twoA c i).card + Cell.leaf c i
        = (2 * (twoA c i).card + Cell.leaf c i)
            * (2 * (twoA c i).card + Cell.leaf c i) := h11
      _ = 4 * ((twoA c i).card * (twoA c i).card) + 4 * (twoA c i).card * Cell.leaf c i
          + (Cell.leaf c i * Cell.leaf c i) := h9
      _ = 4 * ((twoA c i).card * ((twoA c i).card - 1))
          + 4 * (twoA c i).card * Cell.leaf c i
          + (Cell.leaf c i * (Cell.leaf c i - 1)) + 4 * (twoA c i).card + Cell.leaf c i := by
        rw [← h7, ← h8]; ring
  have h12 : 8 * Nat.choose (twoA c i).card 2
      = 4 * ((twoA c i).card * ((twoA c i).card - 1)) := by omega
  have h13 : 2 * Nat.choose (Cell.leaf c i) 2
      = (Cell.leaf c i * (Cell.leaf c i - 1)) := by omega
  rw [h12, h13]
  exact h10

/-- **THE COLLISION COUNT OF ONE COLOUR, COMPONENT BY COMPONENT** (cancelled form):
`2|disjPairs c i| = 8binom(aᵢ,2) + 4aᵢbᵢ + 2binom(bᵢ,2)` with `aᵢ = |twoA c i|` cherries and
`bᵢ = |Cell.leaf c i|` single edges of colour `i`.  **Two cherries of one colour span four
disjoint pairs, a cherry and a single edge two, two single edges one** — the correct weight of a
pair of components, and *not* `binom(componentsᵢ,2)`. -/
theorem disjPairs_components_eq {n k : ℕ} {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n)
    (i : Fin k) :
    2 * (disjPairs c i).card
      = 8 * Nat.choose (twoA c i).card 2 + 4 * (twoA c i).card * Cell.leaf c i
        + 2 * Nat.choose (Cell.leaf c i) 2 := by
  have h := disjPairs_components hc hn i
  exact Nat.add_right_cancel (Nat.add_right_cancel h)

/-- **THE FOUR-SET SPECTRUM IS A FUNCTION OF THE CELL PROFILE.**  For every admissible colouring of
`K_n` (`n ≥ 4`)

    **`2|fiveFourSets c| + 2 Σᵢmissᵢ + 5|E(K_n)| = 2(n−3)·Paths c + Σᵢ|Eᵢ|² + 2nk`**

i.e. the number of five-coloured four-sets is determined by the number of two-edge paths, the
**second moment of the colour-class sizes**, the number of colours, and the number of *empty cells*
of the `(vertex, colour)` grid.  This is the first formula in which the four-set census of rounds
60–62 and the cell accounting of rounds 71–75 occur together. -/
theorem card_fiveFourSets_cell {n k : ℕ} {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n) :
    2 * (fiveFourSets c).card
        + (2 * (∑ i : Fin k, Miss.miss c i)
          + 5 * (∑ i : Fin k, (classF c i).card))
      = 2 * (n - 3) * Paths c
        + ((∑ i : Fin k, (classF c i).card * (classF c i).card) + 2 * n * k) := by
  have hA := card_fiveFourSets_disj hc hn
  have hS : (∑ i : Fin k, (2 * (disjPairs c i).card + 2 * Miss.miss c i
        + 5 * (classF c i).card))
      = ∑ i : Fin k, ((classF c i).card * (classF c i).card + 2 * n) := by
    refine Finset.sum_congr rfl fun i _ => disjPairs_cell hc i
  have hB : 2 * (∑ i : Fin k, (disjPairs c i).card)
        + (2 * (∑ i : Fin k, Miss.miss c i) + 5 * (∑ i : Fin k, (classF c i).card))
      = ∑ i : Fin k, (2 * (disjPairs c i).card + 2 * Miss.miss c i + 5 * (classF c i).card) := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
      Finset.sum_add_distrib (s := (Finset.univ : Finset (Fin k)))
        (f := fun i => 2 * (disjPairs c i).card + 2 * Miss.miss c i)
        (g := fun i => 5 * (classF c i).card),
      Finset.sum_add_distrib (s := (Finset.univ : Finset (Fin k)))
        (f := fun i => 2 * (disjPairs c i).card)
        (g := fun i => 2 * Miss.miss c i)]
    ring
  have hX : 2 * ((n - 3) * Paths c + ∑ i : Fin k, (disjPairs c i).card)
      = 2 * (n - 3) * Paths c + 2 * (∑ i : Fin k, (disjPairs c i).card) := by ring
  calc 2 * (fiveFourSets c).card
        + (2 * (∑ i : Fin k, Miss.miss c i) + 5 * (∑ i : Fin k, (classF c i).card))
      = (2 * (n - 3) * Paths c + 2 * (∑ i : Fin k, (disjPairs c i).card))
          + (2 * (∑ i : Fin k, Miss.miss c i) + 5 * (∑ i : Fin k, (classF c i).card)) := by
        rw [hA, hX]
    _ = 2 * (n - 3) * Paths c + (∑ i : Fin k, (2 * (disjPairs c i).card + 2 * Miss.miss c i
        + 5 * (classF c i).card)) := by rw [← hB]; ring
    _ = 2 * (n - 3) * Paths c
          + ∑ i : Fin k, ((classF c i).card * (classF c i).card + 2 * n) := by rw [hS]
    _ = 2 * (n - 3) * Paths c
          + ((∑ i : Fin k, (classF c i).card * (classF c i).card) + 2 * n * k) := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin]; ring

/-- **THE SAME IN GLOBAL FORM**: the four-set spectrum is a function of the cell profile,

    **`2|fiveFourSets c| + 2Σᵢmissᵢ + 5|E(K_n)| = 2(n−3)·Paths c + Σᵢ|Eᵢ|² + 2nk`**. -/
theorem card_fiveFourSets_cell_edges {n k : ℕ} {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n) :
    2 * (fiveFourSets c).card
        + (2 * (∑ i : Fin k, Miss.miss c i)
          + 5 * (edgeFinset (Finset.univ : Finset (Verts n))).card)
      = 2 * (n - 3) * Paths c
        + ((∑ i : Fin k, (classF c i).card * (classF c i).card) + 2 * n * k) := by
  have hD : (∑ i : Fin k, (classF c i).card)
      = (edgeFinset (Finset.univ : Finset (Verts n))).card :=
    sum_card_classIn c (Finset.univ : Finset (Verts n))
  rw [← hD, card_fiveFourSets_cell hc hn]

/-- **THE SPECTRUM AT THE EXTREMAL ORDER.**  If `6k = 5(n−1)` then no cell of the
`(vertex, colour)` grid is missed (`Cell.extremal_sum_miss`), so the four-set spectrum is a
function of the number of two-edge paths, the **second moment of the colour-class sizes** and the
number of colours:

    **`2|fiveFourSets c| + 5|E(K_n)| = 2(n−3)·Paths c + Σᵢ|Eᵢ|² + 2nk`.**

This is the extremal form of the census: an extremal colouring carries no empty cell, and its
tight four-sets are read off the profile of its colour classes alone. -/
theorem card_fiveFourSets_cell_tight {n k : ℕ} {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n)
    (hk : 6 * k = 5 * (n - 1)) :
    2 * (fiveFourSets c).card + 5 * (edgeFinset (Finset.univ : Finset (Verts n))).card
      = 2 * (n - 3) * Paths c
        + ((∑ i : Fin k, (classF c i).card * (classF c i).card) + 2 * n * k) := by
  have h0 := card_fiveFourSets_cell hc hn
  have hD : (∑ i : Fin k, (classF c i).card)
      = (edgeFinset (Finset.univ : Finset (Verts n))).card :=
    sum_card_classIn c (Finset.univ : Finset (Verts n))
  rw [hD, Cell.extremal_sum_miss hc hn hk] at h0
  simp only [Nat.mul_zero, Nat.zero_add] at h0
  exact h0

/-! ### §4  how many four-sets are tight? -/

/-- `|fourSets n| = binom(n,4)`. -/
theorem card_fourSets_choose (n : ℕ) : (fourSets n).card = Nat.choose n 4 := by
  have h2 : (Finset.univ : Finset (Finset (Verts n))).filter
        (fun S : Finset (Verts n) => S.card = 4)
      = (Finset.powerset (Finset.univ : Finset (Verts n))).filter
        (fun S : Finset (Verts n) => S.card = 4) := by
    ext S
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_univ, Finset.subset_univ]
  rw [fourSets, h2, ← Finset.powersetCard_eq_filter, Finset.card_powersetCard]
  simp

/-- **EVERY ADMISSIBLE COLOURING HAS AT LEAST `(n−3) · Paths c` TIGHT FOUR-SETS** — disjoint pairs
only add to the count. -/
theorem card_fiveFourSets_ge {n k : ℕ} {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n) :
    (n - 3) * Paths c ≤ (fiveFourSets c).card := by
  have h1 := card_fiveFourSets_disj hc hn
  omega

private theorem choose_three_6 : ∀ m, 3 ≤ m → 6 * Nat.choose m 3 = m * (m - 1) * (m - 2) := by
  intro m hm
  induction m with
  | zero => omega
  | succ r ih =>
    rcases Nat.lt_or_ge r 3 with h3 | h3
    · interval_cases r <;> native_decide
    · have h1 := Nat.choose_succ_succ' r 2
      have h4 := ih h3
      rw [h1]
      calc 6 * (Nat.choose r 2 + Nat.choose r (2 + 1))
          = 6 * Nat.choose r 2 + 6 * Nat.choose r (2 + 1) := by ring
        _ = 6 * Nat.choose r 2 + r * (r - 1) * (r - 2) := by rw [h4]
        _ = 3 * (2 * Nat.choose r 2) + r * (r - 1) * (r - 2) := by ring
        _ = 3 * (r * (r - 1)) + r * (r - 1) * (r - 2) := by rw [two_mul_choose_two r]
        _ = r * (r - 1) * (3 + (r - 2)) := by ring
        _ = r * (r - 1) * (r + 1) := by rw [show 3 + (r - 2) = r + 1 by omega]
        _ = (r + 1) * r * (r - 1) := by ring
        _ = (r + 1) * ((r + 1) - 1) * ((r + 1) - 2) := by
          have e1 : (r + 1) - 1 = r := by omega
          have e2 : (r + 1) - 2 = r - 1 := by omega
          rw [e1, e2]

private theorem choose_four_24 : ∀ m, 4 ≤ m →
    24 * Nat.choose m 4 = m * (m - 1) * (m - 2) * (m - 3) := by
  intro m hm
  induction m with
  | zero => omega
  | succ r ih =>
    rcases Nat.lt_or_ge r 4 with h4 | h4
    · interval_cases r <;> native_decide
    · have h1 := Nat.choose_succ_succ' r 3
      have h6 : 3 ≤ r := by omega
      have h3 := choose_three_6 r h6
      have h5 := ih h4
      rw [h1]
      calc 24 * (Nat.choose r 3 + Nat.choose r 4)
          = 24 * Nat.choose r 3 + 24 * Nat.choose r 4 := by ring
        _ = 24 * Nat.choose r 3 + r * (r - 1) * (r - 2) * (r - 3) := by rw [h5]
        _ = 4 * (6 * Nat.choose r 3) + r * (r - 1) * (r - 2) * (r - 3) := by ring
        _ = 4 * (r * (r - 1) * (r - 2)) + r * (r - 1) * (r - 2) * (r - 3) := by rw [h3]
        _ = r * (r - 1) * (r - 2) * (4 + (r - 3)) := by ring
        _ = r * (r - 1) * (r - 2) * (r + 1) := by rw [show 4 + (r - 3) = r + 1 by omega]
        _ = (r + 1) * ((r + 1) - 1) * ((r + 1) - 2) * ((r + 1) - 3) := by
          have e1 : (r + 1) - 1 = r := by omega
          have e2 : (r + 1) - 2 = r - 1 := by omega
          have e3 : (r + 1) - 3 = r - 2 := by omega
          rw [e1, e2, e3]
          ring

/-- **`12 binom(n,4) = (n−2)(n−3) binom(n,2)`**: four-vertex sets against pairs of vertices, in
the division-free form used below. -/
theorem choose_four_twelve {n : ℕ} (hn : 4 ≤ n) :
    12 * Nat.choose n 4 = (n - 2) * (n - 3) * Nat.choose n 2 := by
  have h1 := choose_four_24 n hn
  have h2 := two_mul_choose_two n
  have h3 : 2 * (12 * Nat.choose n 4) = 2 * ((n - 2) * (n - 3) * Nat.choose n 2) := by
    calc 2 * (12 * Nat.choose n 4) = 24 * Nat.choose n 4 := by ring
      _ = n * (n - 1) * (n - 2) * (n - 3) := h1
      _ = (n - 2) * (n - 3) * (2 * Nat.choose n 2) := by rw [h2]; ring
      _ = 2 * ((n - 2) * (n - 3) * Nat.choose n 2) := by ring
  omega

/-- **THE EXTREMAL CASE: `4/(n−2)` OF THE FOUR-SETS ARE TIGHT, PLUS THE DISJOINT PAIRS.**  If
`6k = 5(n−1)` then

    **`(n−2)|fiveFourSets c| = 4|fourSets n| + (n−2) Σᵢ|disjPairs c i|`**.

So the extremal colourings are *not* locally six-coloured: a fraction `4/(n−2)` of their four-sets
spans exactly five colours, and every further tight four-set is accounted for by a disjoint pair of
equally coloured edges. -/
theorem tight_fourSets_eq {n k : ℕ} {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n)
    (hk : 6 * k = 5 * (n - 1)) :
    (n - 2) * (fiveFourSets c).card = 4 * (fourSets n).card
      + (n - 2) * (∑ i : Fin k, (disjPairs c i).card) := by
  have h1 := card_fiveFourSets_disj hc hn
  have h2 := tight_attained hc hn hk
  have h3 := card_fourSets_choose n
  have h4 := choose_four_twelve hn
  have hE : Nat.choose n 2 = (edgeFinset (Finset.univ : Finset (Verts n))).card := by
    have := two_mul_choose_two n
    have := card_edgeFinset_univ_two n
    omega
  have hF : 4 * (fourSets n).card = (n - 2) * (n - 3) * Paths c := by
    have h5 : 3 * (4 * (fourSets n).card) = 3 * ((n - 2) * (n - 3) * Paths c) := by
      calc 3 * (4 * (fourSets n).card) = 12 * (fourSets n).card := by ring
        _ = 12 * Nat.choose n 4 := by rw [h3]
        _ = (n - 2) * (n - 3) * Nat.choose n 2 := h4
        _ = (n - 2) * (n - 3) * (edgeFinset (Finset.univ : Finset (Verts n))).card := by rw [hE]
        _ = 3 * ((n - 2) * (n - 3) * Paths c) := by rw [← h2]; ring
    omega
  rw [hF, h1]
  ring

/-- **IN AN EXTREMAL COLOURING AT LEAST A FRACTION `4/(n−2)` OF THE FOUR-SETS SPANS FIVE COLOURS** —
a density statement about the extremal colourings, and a constraint on any construction aiming at
`5(n−1)/6` colours: it must be locally five-coloured on a positive proportion of its four-vertex
sets. -/
theorem tight_fourSets_ge_four {n k : ℕ} {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n)
    (hk : 6 * k = 5 * (n - 1)) :
    4 * (fourSets n).card ≤ (n - 2) * (fiveFourSets c).card := by
  have h := tight_fourSets_eq hc hn hk
  omega

/-! ### §5  the round-14 identity is false -/

/-- **THE NUMBER OF CONNECTED COMPONENTS OF A COLOUR CLASS**: `aᵢ` cherries and `bᵢ` single edges
give `aᵢ + bᵢ = |Eᵢ| − aᵢ` components. -/
def components {n k : ℕ} (c : Col n k) (i : Fin k) : ℕ := (classF c i).card - (twoA c i).card

/-- **THE NAIVE COLLISION IDENTITY OF ROUND 14**: `4 · Paths c + Σᵢ binom(componentsᵢ,2)`.  It is
**false** (§5.1). -/
def naiveCollision {n k : ℕ} (c : Col n k) : ℕ :=
  4 * Paths c + ∑ i : Fin k, Nat.choose (components c i) 2

/-! #### §5.1  the falsification, on the certified colouring of `K₉` -/

set_option maxRecDepth 10000 in
/-- **THE TRUE COLLISION COUNT OF `Tables.nineCol`** (`n = 9`, `k = 8`; an admissible colouring of
`K₉` certified by `admissible_nineCol`). -/
theorem card_fiveFourSets_nineCol : (fiveFourSets nineCol).card = 84 := by
  unfold fiveFourSets
  native_decide

set_option maxRecDepth 10000 in
/-- **`Paths nineCol = 4`.** -/
theorem paths_nineCol : Paths nineCol = 4 := by native_decide

set_option maxRecDepth 10000 in
/-- **`Σᵢ |disjPairs nineCol i| = 60`**: sixty of the `84` collisions of `Tables.nineCol` come from
*disjoint* pairs of equally coloured edges. -/
theorem sum_disjPairs_nineCol : (∑ i : Fin 8, (disjPairs nineCol i).card) = 60 := by
  native_decide

set_option maxRecDepth 10000 in
/-- **THE CORRECTED IDENTITY ON `Tables.nineCol`**: `(n−3)·Paths + Σᵢ|disjPairs| = 84`, the number of
five-coloured four-sets. -/
theorem collision_sum_nineCol :
    (9 - 3) * Paths nineCol + (∑ i : Fin 8, (disjPairs nineCol i).card) = 84 := by
  have h1 := card_fiveFourSets_disj (c := nineCol) admissible_nineCol (by norm_num)
  rw [card_fiveFourSets_nineCol] at h1
  omega

set_option maxRecDepth 10000 in
/-- **THE NAIVE VALUE ON `Tables.nineCol` IS `64`.** -/
theorem naiveCollision_nineCol : naiveCollision nineCol = 64 := by
  unfold naiveCollision components
  native_decide

/-- **THE ROUND-14 COLLISION IDENTITY IS FALSE.**  For the certified admissible colouring
`Tables.nineCol` of `K₉` the naive right-hand side `4 · Paths c + Σᵢ binom(componentsᵢ,2)` is `64`,
while the true total collision count `Σ_{|S| = 4} (6 − colours(S)) = |fiveFourSets|` is `84`.  The
two defects are visible separately: the path term should be `(n−3)·Paths = 24`, not `16`, and the
disjoint pairs of `Tables.nineCol` number `60`, not `Σᵢ binom(componentsᵢ,2) = 48`. -/
theorem naive_ne_nineCol : naiveCollision nineCol ≠ (fiveFourSets nineCol).card := by
  rw [naiveCollision_nineCol, card_fiveFourSets_nineCol]
  norm_num

/-! #### §5.2  the same on `K₁₀` and `K₁₁`, and where the naive form happens to hold -/

set_option maxRecDepth 10000 in
/-- **`Σᵢ |disjPairs tenCol i| = 82`.** -/
theorem sum_disjPairs_tenCol : (∑ i : Fin 9, (disjPairs tenCol i).card) = 82 := by
  native_decide

set_option maxRecDepth 10000 in
/-- `Tables.tenCol` has `138` five-coloured four-sets. -/
theorem card_fiveFourSets_tenCol : (fiveFourSets tenCol).card = 138 := by
  unfold fiveFourSets
  native_decide

set_option maxRecDepth 10000 in
/-- **THE NAIVE VALUE ON `Tables.tenCol` IS `90`, NOT `138`.** -/
theorem naive_ne_tenCol : naiveCollision tenCol ≠ (fiveFourSets tenCol).card := by
  unfold naiveCollision components
  native_decide

set_option maxRecDepth 10000 in
/-- `Tables.elevenCol` has `195` five-coloured four-sets. -/
theorem card_fiveFourSets_elevenCol : (fiveFourSets elevenCol).card = 195 := by
  unfold fiveFourSets
  native_decide

set_option maxRecDepth 10000 in
/-- **THE NAIVE VALUE ON `Tables.elevenCol` IS `120`, NOT `195`.** -/
theorem naive_ne_elevenCol : naiveCollision elevenCol ≠ (fiveFourSets elevenCol).card := by
  unfold naiveCollision components
  native_decide

set_option maxRecDepth 10000 in
/-- **THE NAIVE FORM IS NOT ALWAYS FALSE**: for `Tables.sixCol`, whose colour classes are perfect
matchings (so `Paths = 0` and every component is a single edge, which is precisely the case where
`binom(componentsᵢ,2)` is the right weight), the naive value coincides with the collision count.
The falsification of §5.1 is a statement about the weight of *mixed* pairs of components. -/
theorem naive_sixCol : naiveCollision sixCol = (fiveFourSets sixCol).card := by
  unfold naiveCollision components
  native_decide

end JSP140