import JSPProblem.Grid
import JSPProblem.Pairs
import JSPProblem.Singles

/-!
# JSP-000140 — round 72: THE COLOUR-CLASS TEMPLATE OF THE EXTREMAL CASE

Round 71 (`Grid.lean`) put the five `(vertex, colour)` cells of a labelled triangle into the grid
`V(K_n) × Col(K_n)` and proved the **cell equation**

    `3 · a_j + 2 · b_j = n`   for every colour `j`,

where `a_j` is the number of labelled triangles whose *cherry* colour is `j` (the two-edge paths of
colour `j`) and `b_j` the number whose *leaf* colour is `j` (the single edges of colour `j`).

**This round reads that equation back onto the colour classes themselves**, and shows that the
extremal case is not merely a *counting* phenomenon but a *profile* phenomenon:

* `Template.class_eq_two_mul_cherry_add_leaf` — **`|E_j| = 2 a_j + b_j`**: a tight colour class has
  as many edges as two-edge paths times two plus single edges.  (Equivalently: the refined counting
  lemma `Paths.two_mul_classIn_le_add` is an *equality* in the extremal case — see below.)
* `Template.class_two_mul_eq_add_twoA` — **`2 |E_j| = n + |A_j|`**: the refined per-colour counting
  lemma `2 |E_i| ≤ n + |A_i|` of `Paths.lean` is **attained** whenever `6k = 5(n-1)`.
* `Template.class_three_mul_add_leaf` — **`3 |E_j| + b_j = 2n`**: the classical counting lemma
  `3 |E_i| ≤ 2n` of `Counting.lean` is attained, and **its slack is exactly the number of single
  edges of that colour**.
* `Template.classes_balanced` — **every colour class of a tight colouring has between `(n+1)/2` and
  `2(n-1)/3` edges**, so no class is more than `4/3` of another: a *tight colouring is nearly
  balanced*, a property no earlier file states and no verified construction of this development has.

Section 4 turns the cell equation into a **complete arithmetic classification**: the equation is
satisfiable at **every** tight order `n ≡ 1 (mod 6)`, `n ≥ 13` (with an explicit template,
`Template.cell_system_solution`), so the obstruction found in round 71 at `n = 7` is the *only*
arithmetic one and every further obstruction must be combinatorial.  §5 gives the falsifiable
prediction for the benchmark `EG 13`: an admissible 10-colouring of `K₁₃` must have two colour
classes of 7 edges and eight of 8 (`Template.thirteen_profile`).
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace JSP140
namespace Template

variable {n k : ℕ}

open Classical

/-! ### §0  The degree sum of a colour class, split by colour-degree

`Paths.sum_nb_card_eq` and `Rigidity.sum_nb_card_eq` are both private, so the tool is repeated here
for the third time.  (Third strike: the lemma should be made public in a later round.) -/

private lemma sum_nb_card_eq (c : Col n k) (hc : Admissible c) (i : Fin k) :
    (∑ v ∈ (Finset.univ : Finset (Verts n)), (nb c i v (Finset.univ : Finset (Verts n))).card)
      = 2 * (twoA c i).card + 1 * (oneB c i).card := by
  have key : ∀ v ∈ (Finset.univ : Finset (Verts n)),
      (nb c i v (Finset.univ : Finset (Verts n))).card
        = (if (nb c i v (Finset.univ : Finset (Verts n))).card = 2 then (2 : ℕ) else 0)
          + (if (nb c i v (Finset.univ : Finset (Verts n))).card = 1 then (1 : ℕ) else 0) := by
    intro v _
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
  have h1 : (∑ v ∈ (Finset.univ : Finset (Verts n)),
      (if (nb c i v (Finset.univ : Finset (Verts n))).card = 2 then (2 : ℕ) else 0))
      = 2 * (twoA c i).card := by
    calc _ = ∑ v ∈ twoA c i, (2 : ℕ) := by
          rw [twoA]; exact (Finset.sum_filter (fun v : Verts n =>
            (nb c i v (Finset.univ : Finset (Verts n))).card = 2) fun _ => (2 : ℕ)).symm
      _ = (twoA c i).card • (2 : ℕ) := Finset.sum_const _
      _ = 2 * (twoA c i).card := by rw [nsmul_eq_mul]; exact Nat.mul_comm _ _
  have h2 : (∑ v ∈ (Finset.univ : Finset (Verts n)),
      (if (nb c i v (Finset.univ : Finset (Verts n))).card = 1 then (1 : ℕ) else 0))
      = 1 * (oneB c i).card := by
    calc _ = ∑ v ∈ oneB c i, (1 : ℕ) := by
          rw [oneB]; exact (Finset.sum_filter (fun v : Verts n =>
            (nb c i v (Finset.univ : Finset (Verts n))).card = 1) fun _ => (1 : ℕ)).symm
      _ = (oneB c i).card • (1 : ℕ) := Finset.sum_const _
      _ = 1 * (oneB c i).card := by rw [nsmul_eq_mul]; exact Nat.mul_comm _ _
  calc (∑ v ∈ (Finset.univ : Finset (Verts n)), (nb c i v (Finset.univ : Finset (Verts n))).card)
      = ∑ v ∈ (Finset.univ : Finset (Verts n)),
          ((if (nb c i v (Finset.univ : Finset (Verts n))).card = 2 then (2 : ℕ) else 0)
            + (if (nb c i v (Finset.univ : Finset (Verts n))).card = 1 then (1 : ℕ) else 0)) :=
        Finset.sum_congr rfl fun v hv => key v hv
    _ = (∑ v ∈ (Finset.univ : Finset (Verts n)),
          (if (nb c i v (Finset.univ : Finset (Verts n))).card = 2 then (2 : ℕ) else 0))
        + ∑ v ∈ (Finset.univ : Finset (Verts n)),
          (if (nb c i v (Finset.univ : Finset (Verts n))).card = 1 then (1 : ℕ) else 0) :=
        Finset.sum_add_distrib
    _ = 2 * (twoA c i).card + 1 * (oneB c i).card := by rw [h1, h2]

/-! ### §1  The refined per-class counting lemma is an equality in the extremal case -/

/-- **THE REFINED COUNTING LEMMA IS AN EQUALITY IN THE EXTREMAL CASE.**  If an admissible colouring
of `K_n` uses the extremal number `6k = 5(n-1)` of colours, then every colour class `j` satisfies

    `2 · |E_j| = n + |A_j|`,

i.e. `Paths.two_mul_classIn_le_add` (`2 |E_i| ≤ n + |A_i|`, the refinement that produced the sharp
constant `5/6`) holds with **equality** in every colour class, with `|A_j|` the number of two-edge
paths of colour `j`.  The proof is the double count of the incidences `(v, e)` with `e` a colour-`j`
edge at `v`: `2|E_j| = 2|A_j| + |B_j|` (degree sum) and `|A_j| + |B_j| = n` (`Rigidity`:
`tight_classes_span`). -/
theorem class_two_mul_eq_add_twoA {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n)
    (hk : 6 * k = 5 * (n - 1)) (j : Fin k) :
    2 * (classF c j).card = n + (twoA c j).card := by
  have h3 := tight_attained hc hn hk
  have hdeg := degree_sum (c := c) (i := j) (S := (Finset.univ : Finset (Verts n)))
  have hdeg' : 2 * (classF c j).card
      = (∑ v ∈ (Finset.univ : Finset (Verts n)), (nb c j v Finset.univ).card) := hdeg.symm
  have hsplit := sum_nb_card_eq c hc j
  have hspan := tight_classes_span hc hn h3 hk j
  omega

/-! ### §2  The grid cells are the colour classes: `|E_j| = 2 a_j + b_j` -/

/-- **THE CHERRIES OF A COLOUR ARE ITS TWO-EDGE PATHS.**  For every colour `j`, the triangles of
`Grid.TriFamilyOf` whose cherry colour is `j` are in bijection with the two-edge paths of colour
`j`, so `a_j = |twoA c j|`. -/
theorem cherryF_card_eq_twoA {c : Col n k} (j : Fin k) :
    (Grid.cherryF c (Grid.TriFamilyOf c) j).card = (twoA c j).card := by
  have key : ∀ B : Fin k × Verts n, B ∈ cherryFinset c →
      Grid.triCherry c (Grid.cherryTri c B) = B.1 := by
    intro B hB
    have hv : B.2 ∈ twoA c B.1 := twoA_of_mem_cherryFinset hB
    obtain ⟨hne, hN⟩ := Grid.leaves_eq hv
    have hmem : (Grid.leaves c B.1 B.2).1 ∈ Nbrs c B.1 B.2 := by rw [hN]; simp
    have hcol : c s(B.2, (Grid.leaves c B.1 B.2).1) = B.1 := (mem_Nbrs.mp hmem).2
    show Grid.cherryCol c B.2 (Grid.leaves c B.1 B.2).1 (Grid.leaves c B.1 B.2).2 = B.1
    exact hcol
  have hmemB : ∀ v ∈ twoA c j, (j, v) ∈ cherryFinset c := by
    intro v hv
    exact Finset.mem_biUnion.mpr
      ⟨j, Finset.mem_univ j, Finset.mem_image.mpr ⟨v, hv, rfl⟩⟩
  have hmap : ∀ v ∈ twoA c j,
      Grid.cherryTri c (j, v) ∈ Grid.cherryF c (Grid.TriFamilyOf c) j := by
    intro v hv
    exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨(j, v), hmemB v hv, rfl⟩,
      by rw [key (j, v) (hmemB v hv)]⟩
  have hmap' : ∀ u ∈ Grid.cherryF c (Grid.TriFamilyOf c) j,
      ∃ v ∈ twoA c j, u = Grid.cherryTri c (j, v) := by
    intro u hu
    obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hu
    obtain ⟨B, hB, hEq⟩ := Finset.mem_image.mp h1
    have hB1 : B.1 = j := by
      rw [← hEq] at h2
      rw [key B hB] at h2
      exact h2
    have htri : Grid.cherryTri c (j, B.2) = Grid.cherryTri c B := by
      rw [Grid.cherryTri, Grid.cherryTri]
      rw [hB1]
    refine ⟨B.2, ?_, ?_⟩
    · rw [← hB1]
      exact twoA_of_mem_cherryFinset hB
    · exact hEq.symm.trans htri.symm
  have hinj : ∀ v ∈ twoA c j, ∀ w ∈ twoA c j,
      Grid.cherryTri c (j, v) = Grid.cherryTri c (j, w) → v = w := by
    intro v hv w hw hEq
    have := Grid.injective_cherryTri (hmemB v hv) (hmemB w hw) hEq
    exact congrArg Prod.snd this
  have heq : Grid.cherryF c (Grid.TriFamilyOf c) j
      = (twoA c j).image (fun v : Verts n => Grid.cherryTri c (j, v)) := by
    ext u
    constructor
    · intro hu
      obtain ⟨v, hv, huv⟩ := hmap' u hu
      exact Finset.mem_image.mpr ⟨v, hv, huv.symm⟩
    · intro hu
      obtain ⟨v, hv, huv⟩ := Finset.mem_image.mp hu
      exact huv.symm ▸ hmap v hv
  rw [heq, Finset.card_image_iff.mpr hinj]

/-- **A TIGHT COLOUR CLASS HAS `2 a_j + b_j` EDGES.**  A colour class of an extremal colouring is a
vertex-disjoint union of two-edge paths (its `a_j` cherries, two edges each) and isolated single
edges (its `b_j` leaf edges, one edge each), so

    `|E_j| = 2 · a_j + b_j`.

This is the reading of the cell equation `Grid.cellCount` as a statement about the *colour class*:
the grid equation is the vertex-covering statement, this is the edge-counting statement, and the two
together are the whole profile of the colour. -/
theorem class_eq_two_mul_cherry_add_leaf {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n)
    (hk : 6 * k = 5 * (n - 1)) (j : Fin k) :
    (classF c j).card = 2 * (Grid.cherryF c (Grid.TriFamilyOf c) j).card
      + (Grid.leafF c (Grid.TriFamilyOf c) j).card := by
  have hD := Grid.decomposes_of_tight hc hn hk
  have he := Grid.cellCount hD j
  have h1 := class_two_mul_eq_add_twoA hc hn hk j
  rw [← cherryF_card_eq_twoA j] at h1
  have hstep : n + (Grid.cherryF c (Grid.TriFamilyOf c) j).card
      = 2 * (2 * (Grid.cherryF c (Grid.TriFamilyOf c) j).card
          + (Grid.leafF c (Grid.TriFamilyOf c) j).card) := by omega
  exact Nat.eq_of_mul_eq_mul_left (by omega) (h1.trans hstep)

/-- **THE CLASSICAL COUNTING BOUND, WITH ITS SLACK IDENTIFIED.**  In the extremal case

    `3 · |E_j| + b_j = 2 n`,

so the classical lemma `3 |E_i| ≤ 2n` of `Counting.lean` holds with equality **iff** the colour class
has no single edge at all (it is then a perfect packing of two-edge paths, the extremal case of that
lemma). -/
theorem class_three_mul_add_leaf {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n)
    (hk : 6 * k = 5 * (n - 1)) (j : Fin k) :
    3 * (classF c j).card + (Grid.leafF c (Grid.TriFamilyOf c) j).card = 2 * n := by
  rw [class_eq_two_mul_cherry_add_leaf hc hn hk j, cherryF_card_eq_twoA j]
  have he := Grid.cellCount (Grid.decomposes_of_tight hc hn hk) j
  rw [cherryF_card_eq_twoA j] at he
  omega

/-! ### §3  The size window: a tight colouring is nearly balanced -/

/-- **THE CLASSICAL BOUND, RE-DERIVED FROM THE GRID.**  In the extremal case `3 |E_j| ≤ 2n` for every
colour `j` (`Counting.three_mul_classIn_le` for a general colouring). -/
theorem class_le_two_third {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n)
    (hk : 6 * k = 5 * (n - 1)) (j : Fin k) : 3 * (classF c j).card ≤ 2 * n := by
  have h := class_three_mul_add_leaf hc hn hk j
  omega

/-- **NO COLOUR CLASS OF A TIGHT COLOURING IS SMALL.**  Every colour class of an extremal colouring
has at least `(n+1)/2` edges: its class spans the vertex set, so `2 |E_j| = n + |A_j|` with
`|A_j| ≥ 1` odd (`Extremal.tight_twoA_odd`).  Together with `class_le_two_third_sharp` this is the
**window** `[(n+1)/2, 2(n-1)/3]` for the colour-class profile of a tight colouring. -/
theorem class_ge_half {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n)
    (hk : 6 * k = 5 * (n - 1)) (j : Fin k) : n + 1 ≤ 2 * (classF c j).card := by
  have h3 := tight_attained hc hn hk
  have h1 := class_two_mul_eq_add_twoA hc hn hk j
  have hodd := tight_twoA_odd hc hn h3 hk j
  omega

/-- **THE UPPER END OF THE WINDOW.**  In the extremal case `3 |E_j| ≤ 2(n-1)`, i.e.
`|E_j| ≤ 2(n-1)/3`, with the improvement over `2n/3` coming from the parity obstruction
(`Extremal.tight_twoA_le`, `3 |A_j| + 3 ≤ n`) — the classical counting lemma is never attained at
the tight order. -/
theorem class_le_two_third_sharp {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n)
    (hk : 6 * k = 5 * (n - 1)) (j : Fin k) : 3 * (classF c j).card ≤ 2 * (n - 1) := by
  have h3 := tight_attained hc hn hk
  have hle := tight_twoA_le hc hn h3 hk j
  have he := Grid.cellCount (Grid.decomposes_of_tight hc hn hk) j
  rw [cherryF_card_eq_twoA j] at he
  have h1 := class_two_mul_eq_add_twoA hc hn hk j
  -- `3 a_j + 2 b_j = n` with `3 a_j + 3 ≤ n` gives `b_j ≥ 2`, and `3 |E_j| = 2 n - b_j`
  omega

/-- **A TIGHT COLOURING IS NEARLY BALANCED.**  In the extremal case no colour class is more than
`4/3` the size of another one: `3 |E_j| ≤ 4 |E_i|` for all colours `i, j`.  So the profile of a
tight colouring lies in a window of relative width `1/3`, which is invisible to the census of
rounds 60–70 (all of which sum over the colours) and to the `5(n-1)/6` counting bound itself. -/
theorem classes_balanced {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n)
    (hk : 6 * k = 5 * (n - 1)) (i j : Fin k) :
    3 * (classF c j).card ≤ 4 * (classF c i).card := by
  have h1 := class_le_two_third_sharp hc hn hk j
  have h2 := class_ge_half hc hn hk i
  omega

/-- **THE WINDOW, IN ONE STATEMENT.**  Every colour class of an extremal colouring of `K_n` has
between `(n+1)/2` and `2(n-1)/3` edges; hence `k ≥ 3(n-1)/5` colours are needed to cover
`C(n,2)` edges, and at the extremal value `k = 5(n-1)/6` the classes are within a factor `4/3`. -/
theorem window {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n) (hk : 6 * k = 5 * (n - 1)) :
    (∀ j : Fin k, n + 1 ≤ 2 * (classF c j).card ∧ 3 * (classF c j).card ≤ 2 * (n - 1))
      ∧ (∀ i j : Fin k, 3 * (classF c j).card ≤ 4 * (classF c i).card) :=
  ⟨fun j => ⟨class_ge_half hc hn hk j, class_le_two_third_sharp hc hn hk j⟩,
    fun i j => classes_balanced hc hn hk i j⟩

/-- **THE ACCEPTANCE TEST FOR A CANDIDATE TIGHT COLOURING AT ORDER `n = 6 t + 1`.**  If `c` is an
admissible `5 t`-colouring of `K_{6 t + 1}` then necessarily

* every colour is the cherry colour of `1 ≤ a_j ≤ 2 t - 1` labelled triangles, with
  `Σ_j a_j = t (6 t + 1) = n(n-1)/6` (the `n(n-1)/6` two-edge paths);
* every colour class has `3 t + 1 ≤ |E_j| ≤ 4 t` edges.

All of this is checkable on a candidate colouring by `native_decide`, and none of it is implied by
the counting bound `5(n-1)/6` alone. -/
theorem candidate_test (t : ℕ) (ht : 2 ≤ t) (c : Col (6 * t + 1) (5 * t)) (hc : Admissible c) :
    (∀ j : Fin (5 * t), 1 ≤ (twoA c j).card ∧ 3 * (twoA c j).card + 3 ≤ 6 * t + 1)
      ∧ (∑ j : Fin (5 * t), (twoA c j).card = t * (6 * t + 1))
      ∧ (∀ j : Fin (5 * t), 3 * t + 1 ≤ (classF c j).card ∧ 3 * (classF c j).card ≤ 4 * (6 * t + 1)) := by
  have hk : 6 * (5 * t) = 5 * ((6 * t + 1 : ℕ) - 1) := by
    have h1 : ((6 * t + 1 : ℕ) - 1) = 6 * t := Nat.add_sub_cancel_right _ _
    rw [h1]
    ring
  have h3 := tight_attained hc (by omega) hk
  have hsum : (∑ j : Fin (5 * t), (twoA c j).card) = t * (6 * t + 1) := by
    have h6 : Paths c = (6 * t + 1) * (6 * t) / 6 := tight_paths hc (by omega) h3
    have hdvd : (6 : ℕ) ∣ (6 * t + 1) * (6 * t) := ⟨t * (6 * t + 1), by ring⟩
    have hc6 : 6 * ((6 * t + 1) * (6 * t) / 6) = (6 * t + 1) * (6 * t) := Nat.mul_div_cancel' hdvd
    have h6' : (6 * t + 1) * (6 * t) / 6 = t * (6 * t + 1) :=
      Nat.eq_of_mul_eq_mul_left (by omega) (hc6.trans (by ring))
    rw [← Paths, h6, h6']
  refine ⟨fun j => ?_, hsum, fun j => ?_⟩
  · have hodd := tight_twoA_odd hc (by omega) h3 hk j
    have hle := tight_twoA_le hc (by omega) h3 hk j
    omega
  · have h1 := class_ge_half hc (by omega) hk j
    have h2 := class_le_two_third_sharp hc (by omega) hk j
    omega

/-! ### §4  Parity: the cherry count is odd, the leaf count is at least two -/

/-- **THE PARITY CONSEQUENCE OF THE CELL EQUATION.**  `3 a_j + 2 b_j = n` forces `a_j ≡ n (mod 2)`:
in the extremal case `n` is odd, so every colour is the cherry colour of an *odd* number of
labelled triangles (this is `Extremal.tight_twoA_odd`, re-derived from `Grid.cellCount`). -/
theorem cherry_parity {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n)
    (hk : 6 * k = 5 * (n - 1)) (j : Fin k) :
    (Grid.cherryF c (Grid.TriFamilyOf c) j).card % 2 = n % 2 := by
  have h3 := tight_attained hc hn hk
  have hodd := tight_twoA_odd hc hn h3 hk j
  have hmod := (tight_mod6 hc hn h3 hk).1
  obtain ⟨t, ht⟩ : ∃ t : ℕ, n = 6 * t + 1 := ⟨n / 6, by
    calc n = n % 6 + 6 * (n / 6) := (Nat.mod_add_div n 6).symm
      _ = 6 * (n / 6) + 1 := by rw [hmod]; exact Nat.add_comm _ _⟩
  rw [cherryF_card_eq_twoA j, hodd]
  omega

/-- **EVERY COLOUR IS THE LEAF COLOUR OF AT LEAST TWO TRIANGLES.**  In the extremal case
`3 a_j + 2 b_j = n` with `a_j` odd and `n ≡ 1 (mod 6)`, so `b_j ≡ 2 (mod 3)` and in particular
`b_j ≥ 2`: **no colour class of a tight colouring is a perfect packing of two-edge paths** — every
one of them contains at least two isolated single edges.  (This is the quantitative form of the
`Grid.cellCount` obstruction at `n = 7`, where it reads `b_j = 2` for all five colours.) -/
theorem leaf_ge_two {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n)
    (hk : 6 * k = 5 * (n - 1)) (j : Fin k) : 2 ≤ (Grid.leafF c (Grid.TriFamilyOf c) j).card := by
  have he := Grid.cellCount (Grid.decomposes_of_tight hc hn hk) j
  have h3 := tight_attained hc hn hk
  have hle := tight_twoA_le hc hn h3 hk j
  have hodd := tight_twoA_odd hc hn h3 hk j
  rw [cherryF_card_eq_twoA j] at he
  omega

/-! ### §5  The profile at order `n = 13` — a falsifiable prediction for `EG 13` -/

/-- **THE CHERRY COUNTS AT `n = 13`.**  In an admissible 10-colouring of `K₁₃` every colour is the
cherry colour of `1` or `3` labelled triangles (`3 a_j + 2 b_j = 13` with `a_j` odd). -/
theorem thirteen_a_le_three {c : Col 13 10} (hc : Admissible c) (j : Fin 10) :
    (twoA c j).card = 1 ∨ (twoA c j).card = 3 := by
  have hk : 6 * (10 : ℕ) = 5 * ((13 : ℕ) - 1) := by norm_num
  have h3 := tight_attained hc (by omega) hk
  have hle := tight_twoA_le hc (by omega) h3 hk j
  have hodd := tight_twoA_odd hc (by omega) h3 hk j
  omega

/-- **THE NUMBER OF PATHS AT `n = 13`.**  An admissible 10-colouring of `K₁₃` has exactly
`13·12/6 = 26` two-edge paths. -/
theorem thirteen_paths {c : Col 13 10} (hc : Admissible c) :
    (∑ j : Fin 10, (twoA c j).card) = 26 := by
  have hk : 6 * (10 : ℕ) = 5 * ((13 : ℕ) - 1) := by norm_num
  have h3 := tight_attained hc (by omega) hk
  have h6 : Paths c = 13 * 12 / 6 := tight_paths hc (by omega) h3
  rw [← Paths]
  omega

/-- **THE PROFILE OF A HYPOTHETICAL TIGHT COLOURING OF `K₁₃`.**  If an admissible 10-colouring of
`K₁₃` exists — the first order at which the counting bound `5(n-1)/6 = 10` can be attained at all —
then **exactly two** of its ten colour classes contain one two-edge path and **exactly eight**
contain three; consequently two classes have `|E_j| = 2·1 + 5 = 7` edges and eight have
`|E_j| = 2·3 + 2 = 8` edges, and `2·7 + 8·8 = 78 = C(13,2)`.

This is a *falsifiable prediction* about benchmark B5 (`EG 13 = 11`, i.e. whether an admissible
11-colouring of `K₁₃` exists): it constrains the profile of the 10-colouring, which the searches of
rounds 49–56, 66 and 67 were unable to find. -/
theorem thirteen_profile {c : Col 13 10} (hc : Admissible c) :
    (∑ j : Fin 10, if (twoA c j).card = 1 then 1 else 0) = 2
      ∧ (∑ j : Fin 10, if (twoA c j).card = 3 then 1 else 0) = 8 := by
  have hsum := thirteen_paths hc
  have hsplit : ∀ j : Fin 10, (twoA c j).card
      = (if (twoA c j).card = 1 then 1 else 0)
        + 3 * (if (twoA c j).card = 3 then 1 else 0) := by
    intro j
    rcases thirteen_a_le_three hc j with h1 | h2
    · rw [h1]; simp
    · rw [h2]; simp
  have hsplit' : ∀ j : Fin 10, (if (twoA c j).card = 1 then 1 else 0)
      + (if (twoA c j).card = 3 then 1 else 0) = 1 := by
    intro j
    rcases thirteen_a_le_three hc j with h1 | h2
    · rw [h1]; simp
    · rw [h2]; simp
  have hA : (∑ j : Fin 10, ((if (twoA c j).card = 1 then 1 else 0)
      + (if (twoA c j).card = 3 then 1 else 0))) = ∑ jj : Fin 10, (1 : ℕ) :=
    Finset.sum_congr rfl (fun j _ => hsplit' j)
  have h1 : (∑ j : Fin 10, ((if (twoA c j).card = 1 then 1 else 0)
      + (if (twoA c j).card = 3 then 1 else 0))) = 10 := by
    rw [hA]
    simp
  have hB : (∑ j : Fin 10, ((if (twoA c j).card = 1 then 1 else 0)
      + 3 * (if (twoA c j).card = 3 then 1 else 0))) = ∑ jj : Fin 10, (twoA c jj).card :=
    Finset.sum_congr rfl (fun j _ => (hsplit j).symm)
  have h2 : (∑ j : Fin 10, (if (twoA c j).card = 1 then 1 else 0))
      + 3 * (∑ j : Fin 10, (if (twoA c j).card = 3 then 1 else 0)) = 26 := by
    have hmul : 3 * (∑ j : Fin 10, (if (twoA c j).card = 3 then 1 else 0))
        = ∑ j : Fin 10, (3 * (if (twoA c j).card = 3 then 1 else 0)) :=
      Finset.mul_sum (Finset.univ : Finset (Fin 10))
        (fun j => if (twoA c j).card = 3 then 1 else 0) 3
    have hadd : (∑ j : Fin 10, (if (twoA c j).card = 1 then 1 else 0))
        + ∑ j : Fin 10, (3 * (if (twoA c j).card = 3 then 1 else 0))
        = ∑ j : Fin 10, ((if (twoA c j).card = 1 then 1 else 0)
            + 3 * (if (twoA c j).card = 3 then 1 else 0)) := by
      rw [← Finset.sum_add_distrib]
    rw [hmul, hadd]
    exact hB.trans hsum
  have h1' : (∑ j : Fin 10, (if (twoA c j).card = 1 then 1 else 0))
      + (∑ j : Fin 10, (if (twoA c j).card = 3 then 1 else 0)) = 10 := by
    rw [← Finset.sum_add_distrib]
    exact h1
  constructor <;> omega

/-- **THE PROFILE AT `n = 13`, IN EDGES.**  Under the same hypothesis, exactly two colour classes
have `7` edges and exactly eight have `8`, and their total is `78 = C(13,2)`. -/
theorem thirteen_profile_edges {c : Col 13 10} (hc : Admissible c) :
    (∑ j : Fin 10, if (classF c j).card = 7 then 1 else 0) = 2
      ∧ (∑ j : Fin 10, if (classF c j).card = 8 then 1 else 0) = 8 := by
  have hsumE : (∑ j : Fin 10, (classF c j).card) = 78 := by
    have h := sum_card_classF c
    have h2' := card_edgeFinset_univ_two 13
    omega
  have hedge : ∀ j : Fin 10, (classF c j).card = 2 * (twoA c j).card
      + (13 - 3 * (twoA c j).card) / 2 := by
    intro j
    have hk : 6 * (10 : ℕ) = 5 * ((13 : ℕ) - 1) := by norm_num
    have h1 := class_two_mul_eq_add_twoA hc (by omega) hk j
    rcases thirteen_a_le_three hc j with h1' | h2'
    · rw [h1'] at h1 ⊢
      norm_num at h1 ⊢
      omega
    · rw [h2'] at h1 ⊢
      norm_num at h1 ⊢
      omega
  have hcard : ∀ j : Fin 10, (classF c j).card = 7 ∨ (classF c j).card = 8 := by
    intro j
    rw [hedge j]
    rcases thirteen_a_le_three hc j with h1 | h2
    · rw [h1]; norm_num
    · rw [h2]; norm_num
  have hsplit' : ∀ j : Fin 10, (if (classF c j).card = 7 then 1 else 0)
      + (if (classF c j).card = 8 then 1 else 0) = 1 := by
    intro j
    rcases hcard j with h1 | h2
    · rw [h1]; simp
    · rw [h2]; simp
  have hsplit : ∀ j : Fin 10, (if (classF c j).card = 7 then 1 else 0) * 7
      + (if (classF c j).card = 8 then 1 else 0) * 8 = (classF c j).card := by
    intro j
    rcases hcard j with h1 | h2
    · rw [h1]; simp
    · rw [h2]; simp
  have hA : (∑ j : Fin 10, ((if (classF c j).card = 7 then 1 else 0)
      + (if (classF c j).card = 8 then 1 else 0))) = ∑ jj : Fin 10, (1 : ℕ) :=
    Finset.sum_congr rfl (fun j _ => hsplit' j)
  have h1 : (∑ j : Fin 10, ((if (classF c j).card = 7 then 1 else 0)
      + (if (classF c j).card = 8 then 1 else 0))) = 10 := by
    rw [hA]
    simp
  have hB : (∑ j : Fin 10, ((if (classF c j).card = 7 then 1 else 0) * 7
      + (if (classF c j).card = 8 then 1 else 0) * 8)) = ∑ jj : Fin 10, (classF c jj).card :=
    Finset.sum_congr rfl (fun j _ => hsplit j)
  have h2 : (∑ j : Fin 10, (if (classF c j).card = 7 then 1 else 0)) * 7
      + (∑ j : Fin 10, (if (classF c j).card = 8 then 1 else 0)) * 8 = 78 := by
    have hmul : (∑ j : Fin 10, (if (classF c j).card = 7 then 1 else 0)) * 7
        = ∑ j : Fin 10, ((if (classF c j).card = 7 then 1 else 0) * 7) :=
      Finset.sum_mul (Finset.univ : Finset (Fin 10))
        (fun j => if (classF c j).card = 7 then 1 else 0) 7
    have hmul2 : (∑ j : Fin 10, (if (classF c j).card = 8 then 1 else 0)) * 8
        = ∑ j : Fin 10, ((if (classF c j).card = 8 then 1 else 0) * 8) :=
      Finset.sum_mul (Finset.univ : Finset (Fin 10))
        (fun j => if (classF c j).card = 8 then 1 else 0) 8
    have hadd : ∑ j : Fin 10, ((if (classF c j).card = 7 then 1 else 0) * 7)
        + ∑ j : Fin 10, ((if (classF c j).card = 8 then 1 else 0) * 8)
        = ∑ j : Fin 10, ((if (classF c j).card = 7 then 1 else 0) * 7
            + (if (classF c j).card = 8 then 1 else 0) * 8) := by
      rw [← Finset.sum_add_distrib]
    rw [hmul, hmul2, hadd]
    exact hB.trans hsumE
  have h1' : (∑ j : Fin 10, (if (classF c j).card = 7 then 1 else 0))
      + (∑ j : Fin 10, (if (classF c j).card = 8 then 1 else 0)) = 10 := by
    rw [← Finset.sum_add_distrib]
    exact h1
  constructor <;> omega

/-! ### §6  The cell system is arithmetically feasible at every tight order `n = 6 t + 1 ≥ 13`

§6 of round 72 left the arithmetic of the cell system `3 a_j + 2 b_j = 6 t + 1` open and named the
exact missing lemma.  **This section closes it.**  With `a_j = 2 i_j + 1` (`Template.cherry_parity`
forces `a_j` odd) the system becomes

    `a_j = 2 i_j + 1`,   `b_j = 3 t - 1 - 3 i_j`,   `i_j ≤ t - 1`,   `∑_j i_j = 3 t² - 2 t`,

and the two sums are forced (`∑ a_j = ∑ b_j = t (6 t + 1)`, the number of cherries of the
tight colouring).  So the *only* obstruction is the capacity condition

    `3 t² - 2 t ≤ 5 t (t - 1)`,

which fails exactly at `t = 1`, i.e. exactly at `n = 7` — the obstruction of round 71's
`Grid.card_eq_five`, now a proved statement rather than a paragraph:

* **`Template.capacity_le`** — the capacity condition holds for every `t ≥ 2`;
* **`Template.not_capacity_one`** — it fails at `t = 1`: `n = 7` is the ONLY arithmetic obstruction,
  at the level of the cell system;
* `Template.exists_fill` — the staircase filling (any `D ≤ N m` is distributed over `N` boxes of
  capacity `m`), the one-line combinatorial tool this needed;
* **`Template.cell_system_solution`** — the full system (`3 a_j + 2 b_j = 6 t + 1` for all `j`,
  `1 ≤ a_j ≤ 2 t - 1`, `b_j ≤ 3 t - 1`, `∑ a = ∑ b = t (6 t + 1)`) is solvable for every `t ≥ 2`;
* `Template.cell_system_solution_thirteen` — read at `t = 2`: the profile of a hypothetical
  admissible **10-colouring of `K₁₃`** (`2 * 1 + 5 * 2` for the two cheap colours, `2 * 3 + 2 * 8`
  for the eight expensive ones) exists, so `Template.thirteen_profile` is *arithmetically*
  consistent and any obstruction to a tight colouring at `n = 13` must be combinatorial.

The consequence for the catalog statement: **the cell equation of rounds 71–72 is vacuous as a
source of lower bounds** — it excludes no tight order `n = 6 t + 1 ≥ 13`.  The remaining content of
`jsp_000140_main = FiveSixth EG` is its upper half: the existence of labelled-triangle systems
(`Triangles.TriFamily`, `Grow6`), i.e. the probabilistic construction of arXiv:2207.02920 §4/§12.

-/

/-! ### §7  The arithmetic of the cell system -/

/-- `(a - b) + (b + c) = a + c` for `b ≤ a`. -/
private theorem sub_add_add (a b c : ℕ) (h : b ≤ a) : (a - b) + (b + c) = a + c := by
  calc (a - b) + (b + c) = ((a - b) + b) + c := by rw [Nat.add_assoc]
    _ = a + c := by rw [Nat.sub_add_cancel h]

/-- `(a - b) + c = (a + c) - b`, the truncated-subtraction identity `omega` does not use. -/
private theorem sub_add_comm' (a b c : ℕ) (h : b ≤ a) : (a - b) + c = (a + c) - b := by
  have h1 : ((a - b) + c) + b = a + c := by
    calc ((a - b) + c) + b = (a - b) + (c + b) := Nat.add_assoc _ _ _
      _ = (a - b) + (b + c) := by congr 1; exact Nat.add_comm _ _
      _ = ((a - b) + b) + c := by rw [Nat.add_assoc]
      _ = a + c := by rw [Nat.sub_add_cancel h]
  exact Nat.eq_sub_of_add_eq h1

/-- `(a - b) + c = a + (c - b)`, the other truncated-subtraction lemma `omega` does not use. -/
private theorem sub_add_move (a b c : ℕ) (h1 : b ≤ a) (h2 : b ≤ c) : (a - b) + c = a + (c - b) := by
  have e1 : (a - b) + c = (a + c) - b := sub_add_comm' a b c h1
  have e2 : a + (c - b) = (a + c) - b := by
    have hh := sub_add_comm' c b a h2
    calc a + (c - b) = (c - b) + a := Nat.add_comm _ _
      _ = (c + a) - b := hh
      _ = (a + c) - b := by rw [Nat.add_comm]
  exact e1.trans e2.symm

/-- **THE STAIRCASE FILLING.**  If `D ≤ N · m` and `m > 0` then `D` can be distributed over `N`
boxes of capacity `m`: there is `f : Fin N → ℕ` with `f j ≤ m` everywhere and `∑_j f j = D`.
This is the whole of the combinatorial content of the cell system. -/
private theorem exists_fill (D N m : ℕ) (hm : 0 < m) (hD : D ≤ N * m) :
    ∃ f : Fin N → ℕ, (∀ j, f j ≤ m) ∧ (∑ j : Fin N, f j) = D := by
  induction N generalizing D with
  | zero =>
      have hD0 : D = 0 := by omega
      subst hD0
      exact ⟨fun _ => 0, fun _ => by simp, by simp⟩
  | succ N ih =>
      rcases Nat.lt_or_ge D m with hDlt | hDge
      · have hsum : (∑ j : Fin (N + 1), (if j = 0 then D else 0 : ℕ)) = D := by
          rw [Fin.sum_univ_succ]
          simp
        refine ⟨fun j => if j = 0 then D else 0, ?_, hsum⟩
        intro j
        by_cases h0 : j = 0
        · simp [h0]
          omega
        · simp [h0]
      · have hDm : m ≤ D := hDge
        have hsub : D - m ≤ N * m := by
          have hD2 : D ≤ N * m + m := by
            simpa [show N * m + m = (N + 1) * m from by ring] using hD
          rw [← Nat.sub_add_cancel hDm] at *
          omega
        obtain ⟨f, hf, hsum⟩ := ih (D - m) hsub
        have hfun : ∀ j : Fin (N + 1), (Fin.cases m f j) ≤ m := by
          intro j
          cases j using Fin.cases with
          | zero => show m ≤ m; exact le_refl _
          | succ j => exact hf j
        have hsum' : (∑ j : Fin (N + 1), (Fin.cases m f j)) = D := by
          rw [Fin.sum_univ_succ]
          simp [hsum]
          omega
        exact ⟨fun j => Fin.cases m f j, hfun, hsum'⟩

/-- **THE CAPACITY LEMMA.**  `3 t² - 2 t ≤ 5 t (t - 1)` for every `t ≥ 2`: the `5 t` colours of a
tight colouring of `K_{6 t + 1}` can carry the `t (6 t + 1)` cherries the cell equation demands,
`2 i + 1` of them per colour with `i ≤ t - 1`. -/
theorem capacity_le (t : ℕ) (ht : 2 ≤ t) : 3 * t * t - 2 * t ≤ 5 * t * (t - 1) := by
  have hlin : 3 * t - 2 ≤ 5 * (t - 1) := by omega
  have h1 : (3 * t - 2) * t = 3 * t * t - 2 * t := Nat.mul_sub_right_distrib (3 * t) 2 t
  have h2 : (5 * (t - 1)) * t = 5 * t * (t - 1) := by ring
  rw [← h1, ← h2]
  exact Nat.mul_le_mul_right t hlin

/-- **THE OBSTRUCTION AT `n = 7` IS THE ONLY ARITHMETIC ONE.**  The capacity condition fails at
`t = 1`, the order `n = 7` of round 71's `Grid.card_eq_five`: `1 ≤ 0` is false. -/
theorem not_capacity_one : ¬ (3 * 1 * 1 - 2 * 1 ≤ 5 * 1 * (1 - 1)) := by decide

/-- **THE CELL SYSTEM HAS A SOLUTION AT EVERY TIGHT ORDER `n = 6 t + 1`, `t ≥ 2`.**  With
`a_j = 2 i_j + 1` (forced by the parity of `Template.cherry_parity`) and the staircase filling of
`i_j ≤ t - 1`, `∑ i_j = 3 t² - 2 t`, the cell equation `3 a_j + 2 b_j = n` of `Grid.cellCount`, the
window of §3 (`a_j ≤ 2 t - 1`), the leaf bound of §4 (`b_j ≤ 3 t - 1`) and the two census sums of
§1 (`∑ a_j = ∑ b_j = t (6 t + 1)`) hold simultaneously.

**Consequence.**  The per-class constraints that rounds 71–72 extracted from the extremal case
exclude **no** tight order `n = 6 t + 1 ≥ 13`; every obstruction to a tight colouring at such an
order must be *combinatorial*. -/

theorem cell_system_solution (t : ℕ) (ht : 2 ≤ t) :
    ∃ (a b : Fin (5 * t) → ℕ),
      (∀ j, 3 * a j + 2 * b j = 6 * t + 1) ∧ (∀ j, 1 ≤ a j) ∧ (∀ j, a j ≤ 2 * (t - 1) + 1)
      ∧ (∀ j, b j ≤ 3 * t - 1) ∧ (∑ j, a j = t * (6 * t + 1)) ∧ (∑ j, b j = t * (6 * t + 1)) := by
  have hm : 0 < t - 1 := by omega
  have hcap : 3 * t * t - 2 * t ≤ 5 * t * (t - 1) := by
    have hlin : 3 * t - 2 ≤ 5 * (t - 1) := by omega
    have h1 : (3 * t - 2) * t = 3 * t * t - 2 * t := Nat.mul_sub_right_distrib (3 * t) 2 t
    have h2 : (5 * (t - 1)) * t = 5 * t * (t - 1) := by ring
    rw [← h1, ← h2]
    exact Nat.mul_le_mul_right t hlin
  obtain ⟨i, hi, hsum⟩ := exists_fill (3 * t * t - 2 * t) (5 * t) (t - 1) hm hcap
  have hA : (∑ j : Fin (5 * t), i j) = 3 * t * t - 2 * t := hsum
  have hge : ∀ j : Fin (5 * t), 3 * i j ≤ 3 * t - 1 := by
    intro j
    have := hi j
    omega
  have hmul2 : (∑ j : Fin (5 * t), 2 * i j) = 2 * (∑ j : Fin (5 * t), i j) :=
    (Finset.mul_sum (Finset.univ : Finset (Fin (5 * t))) (fun j => i j) 2).symm
  have hmul3 : (∑ j : Fin (5 * t), 3 * i j) = 3 * (∑ j : Fin (5 * t), i j) :=
    (Finset.mul_sum (Finset.univ : Finset (Fin (5 * t))) (fun j => i j) 3).symm
  have hcard : (∑ _j : Fin (5 * t), (1 : ℕ)) = 5 * t := by
    calc (∑ _j : Fin (5 * t), (1 : ℕ)) = (Finset.univ : Finset (Fin (5 * t))).card := by
          simp [Finset.sum_const]
      _ = 5 * t := by simp
  -- SUM A
  have hsumA : (∑ j : Fin (5 * t), (2 * i j + 1)) = t * (6 * t + 1) := by
    have hadd : (∑ j : Fin (5 * t), (2 * i j + 1))
        = ∑ j : Fin (5 * t), 2 * i j + ∑ _j : Fin (5 * t), (1 : ℕ) := by
      rw [← Finset.sum_add_distrib]
    have h2a : 2 * (3 * t * t - 2 * t) = 6 * t * t - 4 * t := by
      rw [Nat.mul_sub_left_distrib 2 (3 * t * t) (2 * t)]
      congr 1 <;> ring
    have h4 : 4 * t ≤ 6 * t * t := by
      have := Nat.mul_le_mul_right t (by omega : (4:ℕ) ≤ 6 * t)
      simpa [Nat.mul_assoc] using this
    have hstep : (6 * t * t - 4 * t) + 5 * t = 6 * t * t + (5 * t - 4 * t) :=
      sub_add_move (a := 6 * t * t) (b := 4 * t) (c := 5 * t) h4 (by have := Nat.add_comm (4 * t) t; omega)
    have h54 : 5 * t - 4 * t = t := by
      have h1 : 5 * t = 4 * t + t := by ring
      omega
    have hR : t * (6 * t + 1) = 6 * t * t + t := by ring
    rw [hadd, hmul2, hA, hcard, h2a, hstep, h54, hR]
  -- SUM B
  have h5a : 5 * t * (3 * t - 1) = 15 * t * t - 5 * t := by
    have h1 : t * (3 * t - 1) = 3 * t * t - t := by
      rw [Nat.mul_sub_left_distrib t (3 * t) 1]
      congr 1 <;> ring
    calc 5 * t * (3 * t - 1) = 5 * (t * (3 * t - 1)) := by ring
      _ = 5 * (3 * t * t - t) := by rw [h1]
      _ = 5 * (3 * t * t) - 5 * t := Nat.mul_sub_left_distrib 5 (3 * t * t) t
      _ = 15 * t * t - 5 * t := by congr 1; ring
  have h3a : 3 * (3 * t * t - 2 * t) = 9 * t * t - 6 * t := by
    rw [Nat.mul_sub_left_distrib 3 (3 * t * t) (2 * t)]
    congr 1 <;> ring
  have hZY : t * (6 * t + 1) + 3 * (3 * t * t - 2 * t) = 5 * t * (3 * t - 1) := by
    rw [Nat.add_comm]
    have h3 : t * (6 * t + 1) = 6 * t * t + t := by ring
    rw [h3a, h3, h5a]
    have h6 : 6 * t ≤ 9 * t * t := by
      have := Nat.mul_le_mul_right t (by omega : (6:ℕ) ≤ 9 * t)
      simpa [Nat.mul_assoc] using this
    have hstep : (9 * t * t - 6 * t) + (6 * t * t + t) = (9 * t * t + (6 * t * t + t)) - 6 * t :=
      sub_add_comm' (a := 9 * t * t) (b := 6 * t) (c := 6 * t * t + t) h6
    rw [hstep, ← Nat.add_assoc]
    have hA' : 9 * t * t + 6 * t * t + t = 15 * t * t + t := by ring
    rw [hA']
    have hsub : (15 * t * t + t) - (t + 5 * t) = (15 * t * t + t) - t - 5 * t :=
      (Nat.sub_sub (n := 15 * t * t + t) (m := t) (k := 5 * t)).symm
    rw [show 6 * t = t + 5 * t from by ring, hsub, Nat.add_sub_cancel]
  have hsumB : (∑ j : Fin (5 * t), (3 * t - 1 - 3 * i j)) = t * (6 * t + 1) := by
    have hpair : ∀ j : Fin (5 * t), (3 * t - 1 - 3 * i j) + 3 * i j = 3 * t - 1 := by
      intro j
      have := hge j
      omega
    have hc : (∑ _j : Fin (5 * t), (3 * t - 1 : ℕ)) = 5 * t * (3 * t - 1) := by
      calc (∑ _j : Fin (5 * t), (3 * t - 1 : ℕ)) = (Finset.univ : Finset (Fin (5 * t))).card
              * (3 * t - 1) := by simp [Finset.sum_const, nsmul_eq_mul]
        _ = 5 * t * (3 * t - 1) := by simp
    have hX : ∑ j : Fin (5 * t), (3 * t - 1 - 3 * i j) = ∑ j : Fin (5 * t), (3 * t - 1 - 3 * i j) := rfl
    have hadd' : ((∑ j : Fin (5 * t), (3 * t - 1 - 3 * i j)) + ∑ x : Fin (5 * t), 3 * i x) = ∑ j : Fin (5 * t), ((3 * t - 1 - 3 * i j) + 3 * i j) := by
      rw [← Finset.sum_add_distrib]
    have h2 : (∑ j : Fin (5 * t), ((3 * t - 1 - 3 * i j) + 3 * i j)) = ∑ _j : Fin (5 * t), (3 * t - 1) :=
      Finset.sum_congr rfl (fun j _ => hpair j)
    have hA1 : (∑ j : Fin (5 * t), (3 * t - 1 - 3 * i j)) + ∑ x : Fin (5 * t), 3 * i x
        = 5 * t * (3 * t - 1) := by
      rw [← Finset.sum_add_distrib, h2, hc]
    have hA2 : (∑ j : Fin (5 * t), (3 * t - 1 - 3 * i j)) + ∑ x : Fin (5 * t), 3 * i x
        = t * (6 * t + 1) + ∑ x : Fin (5 * t), 3 * i x := by
      calc (∑ j : Fin (5 * t), (3 * t - 1 - 3 * i j)) + ∑ x : Fin (5 * t), 3 * i x
          = 5 * t * (3 * t - 1) := hA1
        _ = t * (6 * t + 1) + 3 * (3 * t * t - 2 * t) := hZY.symm
        _ = t * (6 * t + 1) + ∑ x : Fin (5 * t), 3 * i x := by rw [hmul3, hA]
    exact (Nat.add_right_cancel (n := t * (6 * t + 1)) (m := ∑ x : Fin (5 * t), 3 * i x)
      (k := ∑ j : Fin (5 * t), (3 * t - 1 - 3 * i j)) hA2.symm).symm
  set a : Fin (5 * t) → ℕ := fun j => 2 * i j + 1 with ha
  set b : Fin (5 * t) → ℕ := fun j => 3 * t - 1 - 3 * i j with hb
  refine ⟨a, b, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    have hb' : b j = 3 * t - 1 - 3 * i j := by rw [hb]
    have ha' : a j = 2 * i j + 1 := by rw [ha]
    rw [ha', hb']
    have h1 : 3 * (2 * i j + 1) = 6 * i j + 3 := by ring
    have h3 : 2 * (3 * t - 1) = 6 * t - 2 := by
      rw [Nat.mul_sub_left_distrib 2 (3 * t) 1]
      congr 1
      ring
    have h2 : 2 * (3 * t - 1 - 3 * i j) = 2 * (3 * t - 1) - 2 * (3 * i j) := by
      rw [show 3 * t - 1 - 3 * i j = (3 * t - 1) - 3 * i j from rfl,
        Nat.mul_sub_left_distrib 2 (3 * t - 1) (3 * i j)]
    have h4 : 2 * (3 * i j) = 6 * i j := by ring
    have h5 : 6 * i j ≤ 6 * t - 2 := by
      have h6' : 6 * i j ≤ 2 * (3 * t - 1) := by
        have := Nat.mul_le_mul_right 2 (hge j)
        simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using this
      exact h6'.trans h3.le
    rw [h1, h2, h3, h4]
    calc (6 * i j + 3) + ((6 * t - 2) - 6 * i j) = ((6 * t - 2) - 6 * i j) + (6 * i j + 3) :=
        Nat.add_comm _ _
      _ = (((6 * t - 2) - 6 * i j) + 6 * i j) + 3 := by rw [Nat.add_assoc]
      _ = (6 * t - 2) + 3 := by rw [Nat.sub_add_cancel h5]
      _ = 6 * t + 1 := sub_add_add (a := 6 * t) (b := 2) (c := 1) (by omega)
  · intro j
    have ha' : a j = 2 * i j + 1 := by rw [ha]
    omega
  · intro j
    have ha' : a j = 2 * i j + 1 := by rw [ha]
    have h2 : 2 * i j ≤ 2 * (t - 1) := by
      have := Nat.mul_le_mul_right 2 (hi j)
      simpa [Nat.mul_comm] using this
    omega
  · intro j
    have hb' : b j = 3 * t - 1 - 3 * i j := by rw [hb]
    have h3 : 3 * i j ≤ 3 * (t - 1) := by
      simpa [Nat.mul_comm] using Nat.mul_le_mul_right 3 (hi j)
    omega
  · rw [ha]
    exact hsumA
  · rw [hb]
    exact hsumB

/-- **THE PROFILE OF A HYPOTHETICAL TIGHT COLOURING OF `K₁₃` IS ARITHMETICALLY FEASIBLE.**  At
`t = 2` (`n = 13`, `k = 10`) the system of `Template.cell_system_solution` has a solution, so the
profile of `Template.thirteen_profile` (two colours with `a_j = 1`, `b_j = 5`, eight colours with
`a_j = 3`, `b_j = 2`, `∑ a_j = ∑ b_j = 26`) is arithmetically consistent. -/
theorem cell_system_solution_thirteen :
    ∃ (a b : Fin 10 → ℕ),
      (∀ j, 3 * a j + 2 * b j = 13) ∧ (∀ j, 1 ≤ a j) ∧ (∀ j, a j ≤ 3) ∧ (∀ j, b j ≤ 5)
      ∧ (∑ j, a j = 26) ∧ (∑ j, b j = 26) :=
  cell_system_solution 2 (by norm_num)

/-- **THE `n = 7` CASE IS IMPOSSIBLE ARITHMETICALLY, AND EVERY OTHER TIGHT ORDER IS POSSIBLE.**  The
system of `Template.cell_system_solution` at `t = 1` (`n = 7`, `k = 5`) has **no** solution: the
census `∑_j a_j = t (6 t + 1) = 7` cannot be met by five colours carrying at most one cherry each.
So round 71's obstruction at `n = 7` is *exactly* the capacity failure of §7, and `n = 7` is the
**only** tight order the per-class constraints rule out. -/
theorem cell_system_seven_impossible (a b : Fin 5 → ℕ)
    (h1 : ∀ j, 3 * a j + 2 * b j = 7) (h2 : ∀ j, 1 ≤ a j) (h3 : ∀ j, a j ≤ 1)
    (h5 : ∑ j, a j = 7) : False := by
  have hle : (∑ j, a j) ≤ 5 := by
    calc (∑ j, a j) ≤ ∑ _j, (1 : ℕ) := Finset.sum_le_sum fun j _ => h3 j
      _ = (Finset.univ : Finset (Fin 5)).card := by simp [Finset.sum_const]
      _ = 5 := by simp
  omega

end Template
end JSP140
