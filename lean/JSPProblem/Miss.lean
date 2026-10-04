import JSPProblem.Template

/-!
# JSP-000140 — round 74: THE MISS PROFILE: the per-COLOUR grid defect

Rounds 71–72 (`Grid.lean`, `Template.lean`) read the extremal case off the grid `V × Palette`:
a family of labelled triangles **covers the whole grid**, and therefore

* every colour is present at **every** vertex (`Grid.decomposes_of_tight`),
* every colour class satisfies `3 a_j + 2 b_j = n` (`Grid.cellCount`),
* `2 |E_j| = n + |A_j|`, `3 |E_j| + b_j = 2n`, `|E_j| ∈ [(n+1)/2, 2(n-1)/3]` (`Template.*`).

Both the cell equation and the equality `2 |E_j| = n + |A_j|` are stated there **only for the
extremal case** `6k = 5(n-1)`, because that is the case in which the grid is fully covered.  **This
file removes the extremality hypothesis.**  It introduces the *miss profile*

    `miss c i = n - |{v : v is incident with an edge of colour i}|`,

and proves the exact accounting identity valid for **every** admissible colouring

    **`|active_i| + |A_i| = 2 · |E_i|`**,   equivalently   **`2 · |E_i| + miss_i = n + |A_i|`**,

so that **the slack of the refined counting lemma `Paths.two_mul_classIn_le_add`
(`2 |E_i| ≤ n + |A_i|`) is exactly the number of vertices that miss the colour**.  No earlier file
states this; rounds 71–72 could state the extremal equality only because they had no object for a
*partially* covered grid.

## What is proved here

* `Miss.active`, `Miss.miss`, `Miss.card_active`, `Miss.miss_add_active` — the vertices a colour
  reaches, the vertices it misses, and `miss_i + |active_i| = n`;
* **`Miss.identity`** — `|active_i| + |A_i| = 2 |E_i|` and **`Miss.slack`** — `2 |E_i| + miss_i =
  n + |A_i|`, for every admissible colouring;
* `Miss.class_ge` — `n - miss_i ≤ 2 |E_i|`: a colour missing `m` vertices still has at least
  `(n - m)/2` edges;
* `Miss.incidence` — the global census of cells: `∑_i |active_i| + Paths c = n (n-1)`; its
  per-vertex reading is `Window.missing_at`;
* **`Miss.budget`** — **if `6k = 5n + D` then the colouring misses at most `n(D+5)/6` cells**:
  the `O(n)`-slack version of the grid-coverage statement of round 71, in the form the
  *constructive* side of the catalog answer needs (a construction with an `O(1)` slack in the
  colour count has an `O(n)`-slack grid);
* `Miss.tight_all_active` / `Miss.class_eq_of_tight` — the regime `D = -6` (extremal: nothing is
  missed at all, and the refined counting lemma is an equality — a *second, independent* route to
  `Template.class_two_mul_eq_add_twoA`);
* `Miss.refined_sum_le`, `Miss.anchor_sum_le` — the regimes `D = 1` (refined: at most `n` cells)
  and `D = 6` (the verified anchor `EG 12 = 11` of `Window`: at most `11 n / 6` cells).

## Why this matters for `jsp_000140_main`

`jsp_000140_main = FiveSixth EG` still needs the existence of labelled-triangle systems with a
*partial* triangle packing (arXiv:2207.02920 §4, arXiv:2208.12563 Thm 4.2).  The uncovered pairs of
such a packing are exactly the empty cells of this grid, and `Miss.budget` says how much of the grid
a construction with `6k = 5n + D` colours is *allowed* to leave empty: at most `n(D+5)/6` cells.
With `D = O(n^{1-δ})` (the papers' leftover graph `L` of maximum degree `n^{1-δ}`) this is
`O(n^{2-δ})` cells — the grid coverage needed by `Pack.price` is quantitatively compatible with the
counting bound, which is what the second half of the catalog answer requires.

-/

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace JSP140
namespace Miss

variable {n k : ℕ}

open Classical

/-! ### §0  The degree sum of a colour class, split by colour-degree

Fifth repetition of this private tool (`Paths`, `Rigidity`, `Extremal`, `Surplus`, `Template`); it
should be made public once. -/

private theorem sum_nb_card_eq {c : Col n k} (hc : Admissible c) (i : Fin k) :
    (∑ v : Verts n, (nb c i v (Finset.univ : Finset (Verts n))).card)
      = 2 * (twoA c i).card + 1 * (oneB c i).card := by
  have key : ∀ v : Verts n, (nb c i v (Finset.univ : Finset (Verts n))).card
      = (if (nb c i v (Finset.univ : Finset (Verts n))).card = 2 then (2 : ℕ) else 0)
        + (if (nb c i v (Finset.univ : Finset (Verts n))).card = 1 then (1 : ℕ) else 0) := by
    intro v
    by_cases h2 : (nb c i v (Finset.univ : Finset (Verts n))).card = 2
    · rw [if_pos h2, if_neg (by omega)]
      omega
    · rw [if_neg h2]
      by_cases h1 : (nb c i v (Finset.univ : Finset (Verts n))).card = 1
      · rw [if_pos h1]
        omega
      · rw [if_neg h1]
        have hle := nb_card_le_two hc i v (Finset.univ : Finset (Verts n))
        omega
  rw [Finset.sum_congr rfl fun v _ => key v]
  have h1 : (∑ v : Verts n, if (nb c i v (Finset.univ : Finset (Verts n))).card = 2 then (2 : ℕ)
        else 0) = 2 * (twoA c i).card := by
    calc _ = ∑ v ∈ twoA c i, (2 : ℕ) := by
          rw [twoA]
          exact (Finset.sum_filter (fun v : Verts n =>
            (nb c i v (Finset.univ : Finset (Verts n))).card = 2) fun _ => (2 : ℕ)).symm
      _ = (twoA c i).card • (2 : ℕ) := Finset.sum_const _
      _ = 2 * (twoA c i).card := by rw [nsmul_eq_mul]; exact Nat.mul_comm _ _
  have h2 : (∑ v : Verts n, if (nb c i v (Finset.univ : Finset (Verts n))).card = 1 then (1 : ℕ)
        else 0) = 1 * (oneB c i).card := by
    calc _ = ∑ v ∈ oneB c i, (1 : ℕ) := by
          rw [oneB]
          exact (Finset.sum_filter (fun v : Verts n =>
            (nb c i v (Finset.univ : Finset (Verts n))).card = 1) fun _ => (1 : ℕ)).symm
      _ = (oneB c i).card • (1 : ℕ) := Finset.sum_const _
      _ = 1 * (oneB c i).card := by ring
  rw [Finset.sum_add_distrib, h1, h2]

/-! ### §1  The vertices a colour reaches, and the vertices it misses -/

/-- **The vertices carrying colour `i`**: those with two or with exactly one colour-`i`
neighbour.  (`JSP140.zeroA c i` is the complement of this set: round 65's `Vacant` vocabulary.) -/
def active (c : Col n k) (i : Fin k) : Finset (Verts n) := (twoA c i) ∪ (oneB c i)

theorem mem_active {c : Col n k} {i : Fin k} {v : Verts n} :
    v ∈ active c i ↔ v ∈ twoA c i ∨ v ∈ oneB c i := Finset.mem_union

/-- **`twoA` and `oneB` are disjoint**: a vertex has either two or exactly one colour-`i`
neighbour, never both. -/
theorem disjoint_active {c : Col n k} (i : Fin k) : Disjoint (twoA c i) (oneB c i) := by
  refine Finset.disjoint_left.mpr fun w hw1 hw2 => ?_
  have h1 := (Finset.mem_filter.mp hw1).2
  have h2 := (Finset.mem_filter.mp hw2).2
  omega

theorem card_active {c : Col n k} (i : Fin k) :
    (active c i).card = (twoA c i).card + (oneB c i).card :=
  Finset.card_union_of_disjoint (disjoint_active i)

theorem active_subset_univ {c : Col n k} (i : Fin k) :
    active c i ⊆ (Finset.univ : Finset (Verts n)) := Finset.subset_univ _

/-- **THE MISS PROFILE OF A COLOUR.**  `miss c i` is the number of vertices of `K_n` carrying no
edge of colour `i` — the number of *empty* `(vertex, colour)` cells of the grid of round 71. -/
def miss (c : Col n k) (i : Fin k) : ℕ := n - (active c i).card

theorem miss_add_active {c : Col n k} (i : Fin k) : miss c i + (active c i).card = n := by
  have hle : (active c i).card ≤ n := by
    have h := Finset.card_le_card (s := (active c i)) (t := (Finset.univ : Finset (Verts n)))
      (active_subset_univ i)
    simpa using h
  simp only [miss]
  omega

theorem miss_eq_zero_iff_active_univ {c : Col n k} (i : Fin k) :
    miss c i = 0 ↔ (active c i).card = n := by
  constructor
  · intro h
    simp only [miss] at h
    have hle : (active c i).card ≤ n := by
      have hc := Finset.card_le_card (s := (active c i)) (t := (Finset.univ : Finset (Verts n)))
        (active_subset_univ i)
      simpa using hc
    omega
  · intro h
    have hone := miss_add_active (c := c) i
    omega

/-! ### §2  THE IDENTITY: the slack of the refined counting lemma is the miss count -/

/-- **THE DEGREE SUM OF A COLOUR CLASS.**  The colour-`i` edges are counted once at each of their
two endpoints (`Pairs.sum_nb_card_eq_two_mul_classIn_card`), so `∑_v deg_i(v) = 2 |E_i|`. -/
theorem two_mul_classIn_card_eq {c : Col n k} (i : Fin k) :
    (∑ v : Verts n, (nb c i v (Finset.univ : Finset (Verts n))).card)
      = 2 * (classIn c i (Finset.univ : Finset (Verts n))).card := by
  simpa using sum_nb_card_eq_two_mul_classIn_card (c := c) i (Finset.univ : Finset (Verts n))

/-- **THE IDENTITY.**  For every colour `i` of every admissible colouring of `K_n`,

    **`|active_i| + |A_i| = 2 · |E_i|`**,

i.e. the number of vertices carrying colour `i`, plus the number of its two-edge-path centres,
is the *degree sum* of the colour class. -/
theorem identity {c : Col n k} (hc : Admissible c) (i : Fin k) :
    (active c i).card + (twoA c i).card = 2 * (classIn c i (Finset.univ : Finset (Verts n))).card := by
  have h1 := two_mul_classIn_card_eq (c := c) i
  have h2 := sum_nb_card_eq hc i
  have h3 := card_active (c := c) i
  omega

/-- **THE SLACK FORM OF THE IDENTITY.**  `2 |E_i| + miss_i = n + |A_i|` for every colour of every
admissible colouring: **the slack of the refined per-colour counting lemma
`Paths.two_mul_classIn_le_add` is exactly the number of vertices that miss the colour.** -/
theorem slack {c : Col n k} (hc : Admissible c) (i : Fin k) :
    2 * (classIn c i (Finset.univ : Finset (Verts n))).card + miss c i
      = n + (twoA c i).card := by
  have h1 := identity hc i
  have h2 := miss_add_active (c := c) i
  omega

/-- **A COLOUR MISSING `m` VERTICES STILL HAS AT LEAST `(n - m)/2` EDGES.** -/
theorem class_ge {c : Col n k} (hc : Admissible c) (i : Fin k) :
    n - miss c i ≤ 2 * (classIn c i (Finset.univ : Finset (Verts n))).card := by
  have h := slack hc i
  omega

/-! ### §3  The global census of cells -/

private theorem sum_n (n k : ℕ) : (∑ i : Fin k, (n : ℕ)) = n * k := by
  simp [Nat.mul_comm]

/-- **THE GLOBAL CENSUS.**  Every one of the `n k` cells of the grid is active or missed:

    `∑_i miss_i + ∑_i |active_i| = n k`. -/
theorem total_add {c : Col n k} : (∑ i : Fin k, miss c i) + (∑ i : Fin k, (active c i).card)
    = n * k := by
  have h : ∀ i : Fin k, (miss c i + (active c i).card : ℕ) = n := fun i => miss_add_active i
  calc (∑ i : Fin k, miss c i) + ∑ i : Fin k, (active c i).card
      = ∑ i : Fin k, (miss c i + (active c i).card) := by rw [Finset.sum_add_distrib]
    _ = ∑ _i : Fin k, n := Finset.sum_congr rfl (fun i _ => h i)
    _ = n * k := sum_n n k

/-- **THE NUMBER OF ACTIVE CELLS.**  `∑_i |active_i| + Paths c = n (n-1)`: the number of
`(vertex, colour)` incidences of a colouring plus its number of two-edge paths is the number of
ordered pairs of distinct vertices.  Equivalently, the total number of **empty** cells of the grid
is `n k - n (n-1) + Paths c`, the quantity bounded in §4. -/
theorem incidence {c : Col n k} (hc : Admissible c) :
    (∑ i : Fin k, (active c i).card) + Paths c = n * (n - 1) := by
  have hterm : ∀ i : Fin k, (active c i).card + (twoA c i).card
      = 2 * (classIn c i (Finset.univ : Finset (Verts n))).card := fun i => identity hc i
  calc (∑ i : Fin k, (active c i).card) + Paths c
      = ∑ i : Fin k, ((active c i).card + (twoA c i).card) := by rw [Finset.sum_add_distrib, Paths]
    _ = 2 * ∑ i : Fin k, (classIn c i (Finset.univ : Finset (Verts n))).card := by
        rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.mul_sum]
    _ = 2 * (edgeFinset (Finset.univ : Finset (Verts n))).card :=
        by rw [sum_card_classIn c (Finset.univ : Finset (Verts n))]
    _ = n * (n - 1) := card_edgeFinset_univ_two n

/-! ### §4  THE MISS BUDGET: `6k = 5n + D` bounds the number of empty cells -/

/-- **THE MISS BUDGET.**  Every admissible colouring of `K_n` with `k ≥ 4` colours leaves at most

    `(6 n k - 5 n (n-1)) / 6`

empty cells in the `(vertex, colour)` grid, i.e. **if `6k = 5n + D` then at most `n (D+5)/6` cells
are missed**: the colourings that come closest to the catalog bound are exactly the ones whose
palette is nearly complete at every vertex, and the deficit is measured in cells. -/
theorem budget {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n) :
    6 * (∑ i : Fin k, miss c i) + 5 * (n * (n - 1)) ≤ 6 * (n * k) := by
  have htot := total_add (c := c)
  have hinc := incidence hc
  have hP : 6 * Paths c ≤ n * (n - 1) := six_mul_paths_le hc hn
  omega

/-- **THE EMPTY-CELL COUNT IN THE THREE REGIMES.**  For an admissible colouring with `n ≥ 4`,

    * at the extremal shape `6k = 5(n-1)`: `∑ miss = 0` (the grid is completely covered);
    * at the refined shape `6k = 5n+1`: `6 · ∑ miss ≤ 6 n`;
    * at the anchor shape `6k = 5n+6` (the shape of the verified witness `EG 12 = 11`): 
      `6 · ∑ miss ≤ 11 n`. -/
theorem budget_tight {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n) (hk : 6 * k = 5 * (n - 1)) :
    (∑ i : Fin k, miss c i) = 0 := by
  have hb := budget hc hn
  have h6 : 6 * (n * k) = 5 * (n * (n - 1)) := by
    rw [show 6 * (n * k) = n * (6 * k) from by ring, hk]
    ring
  omega

theorem budget_refined {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n) (hk : 6 * k = 5 * n + 1) :
    6 * (∑ i : Fin k, miss c i) ≤ 6 * n := by
  have hb := budget hc hn
  have h6 : 6 * (n * k) = 5 * (n * (n - 1)) + 6 * n := by
    rw [show 6 * (n * k) = n * (6 * k) from by ring, hk,
      show 5 * n + 1 = 5 * (n - 1) + 6 from by omega]
    rw [Nat.mul_add]
    congr 1 <;> ring
  omega

theorem budget_anchor {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n) (hk : 6 * k = 5 * n + 6) :
    6 * (∑ i : Fin k, miss c i) ≤ 11 * n := by
  have hb := budget hc hn
  have h6 : 6 * (n * k) = 5 * (n * (n - 1)) + 11 * n := by
    rw [show 6 * (n * k) = n * (6 * k) from by ring, hk,
      show 5 * n + 6 = 5 * (n - 1) + 11 from by omega]
    rw [Nat.mul_add]
    congr 1 <;> ring
  omega

/-! ### §5  The extremal case: nothing is missed, and the counting lemma is an equality -/

/-- **IN THE EXTREMAL CASE EVERY COLOUR IS PRESENT AT EVERY VERTEX.**  At `6k = 5(n-1)` no cell of
the grid is empty: this is the grid-coverage statement of round 71 (`Grid.decomposes_of_tight`) in
the per-colour language of this file. -/
theorem tight_all_active {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n) (hk : 6 * k = 5 * (n - 1))
    (i : Fin k) : miss c i = 0 := by
  have hsum := budget_tight hc hn hk
  have hone := miss_add_active (c := c) i
  have hle : miss c i ≤ ∑ j : Fin k, miss c j := by
    have h := Finset.single_le_sum (s := (Finset.univ : Finset (Fin k)))
      (fun j _ => Nat.zero_le (miss c j)) (Finset.mem_univ i)
    simpa using h
  omega

/-- **THE REFINED COUNTING LEMMA IS AN EQUALITY IN THE EXTREMAL CASE.**  `2 |E_i| = n + |A_i|`
(`Template.class_two_mul_eq_add_twoA`, re-derived here from `Miss.slack` and
`Miss.tight_all_active`). -/
theorem class_eq_of_tight {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n) (hk : 6 * k = 5 * (n - 1))
    (i : Fin k) : 2 * (classIn c i (Finset.univ : Finset (Verts n))).card
      = n + (twoA c i).card := by
  have h0 := tight_all_active hc hn hk i
  have h := slack hc i
  omega

/-- **THE EXTREMAL WINDOW, IN THE MISS LANGUAGE.**  At `6k = 5(n-1)` every colour class satisfies the
window of `Template.window`: the miss count vanishes and the class size is pinned by
`Miss.class_eq_of_tight` together with `Extremal.tight_twoA_odd`. -/
theorem tight_class_eq_half_plus {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n)
    (hk : 6 * k = 5 * (n - 1)) (i : Fin k) :
    2 * (classIn c i (Finset.univ : Finset (Verts n))).card = n + (twoA c i).card := by
  exact class_eq_of_tight hc hn hk i

/-! ### §6  The per-class window, with the miss count -/

/-- **THREE TIMES THE CHERRY COUNT IS AT MOST THE NUMBER OF VERTICES CARRYING THE COLOUR.**  The
two-edge paths of a colour class are vertex disjoint (`Counting.two_mul_cardA_le_cardB`: each uses
two distinct degree-one vertices), so `3 a_i ≤ |active_i|`.  In the extremal case this reads
`3 a_j ≤ n`, i.e. `a_j ≤ (n - 1) / 2` is the *window* of round 72 in a sharper form. -/
theorem three_mul_twoA_le_active {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n) (i : Fin k) :
    3 * (twoA c i).card ≤ (active c i).card := by
  have h := two_mul_cardA_le_cardB hc hn i
  have hcard := card_active (c := c) i
  omega

/-- **THE PER-CLASS WINDOW, WITH THE MISS COUNT.**  `3 · |E_i| ≤ 2 · (n - miss_i)`: **a colour that
misses `m` vertices has at most `2 (n - m) / 3` edges.**  This refines the classical per-class bound
`3 |E_i| ≤ 2n` (`Counting.three_mul_classIn_le`) by exactly the miss count, and it is the search
filter that the constructive side of the catalog answer needs: at the anchor shape `6k = 5n + 6`
a colour class of an admissible colouring satisfies

    `(n - miss_i)/2 ≤ |E_i| ≤ 2 (n - miss_i)/3`. -/
theorem class_window {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n) (i : Fin k) :
    3 * (classIn c i (Finset.univ : Finset (Verts n))).card ≤ 2 * (n - miss c i) := by
  have hA := identity hc i
  have hthree := three_mul_twoA_le_active hc hn i
  have hone := miss_add_active (c := c) i
  omega

/-- **THE ANCHOR `EG 12 = 11` IN THE MISS LANGUAGE.**  An admissible 11-colouring of `K₁₂` — the
verified witness of `Window.EG_twelve` — leaves at most `22` empty cells of the
`(vertex, colour)` grid: at most eleven of its eleven colours are missed at one vertex each. -/
theorem anchor_twelve {c : Col 12 11} (hc : Admissible c) (hk : 6 * 11 = 5 * 12 + 6) :
    6 * (∑ i : Fin 11, miss c i) ≤ 11 * 12 := budget_anchor hc (by norm_num) hk

end Miss
end JSP140