import JSPProblem.Cherry
import JSPProblem.Tables

/-!
# JSP-000140 — the EXACT surplus identity: what a colouring pays for its two defects

The lower half of the catalog answer `f(n, 4, 5) = 5n/6 + o(n)` is proved in this development
(`Cherry.five_sixth_lower`), and `Paths.mul_n_sub_one_le` proves its quantitative form

    `n * (n - 1) ≤ n * k + Paths c`,      i.e.      `k ≥ (n-1) - Paths c / n`,

where `Paths c` is the total number of two-edge paths of `c`.  **Both of these throw away
information**: the number of colours a colouring needs is an *exact* function of its structure, and
the two quantities which the inequality discards are precisely the two defects a construction can
control.  This file recovers the exact statement.

Two defects of an admissible colouring `c : Col n k` of `K_n`:

* **`Isolated c`** — the number of `(vertex, colour)` incidences on which the colour does not occur
  at all (`zeroA c i`: the vertices which are neither the centre of a two-edge path of colour `i`
  (`Counting.twoA`) nor the endpoint of an isolated single edge of colour `i` (`Counting.oneB`));
* **`Defect c`** — the number of edges of `K_n` that no two-edge path pays for, i.e.
  `|E(K_n)| - 3 · Paths c` (every two-edge path brings three edges with it and these triples are
  pairwise disjoint, `Cherry.cherryEdges_disjoint`).

**THE MAIN THEOREM (`surplus_identity`).**  For every admissible colouring and `n ≥ 4`

        `6 * (n * k) = 5 * n * (n - 1) + 6 * Isolated c + 2 * Defect c`,

so that

        `k = 5(n-1)/6  +  Isolated c / n  +  Defect c / (3n)`,

**the excess of the number of colours over the sharp counting bound is *exactly* the price of the
two defects — in two integers, with no inequality anywhere.**  Equivalently (`surplus_of_k`)

        `6 * Isolated c + 2 * Defect c = n * (6k - 5(n-1))`,

which is simultaneously a *design target* and an *arithmetic restriction*:

* `card_twoA_oneB_zeroA` — the three degree classes of a colour class partition the vertices:
  `|twoA| + |oneB| + |zeroA| = n`, the ingredient which `Counting.twoA_oneB_card_le` states as an
  inequality;
* `two_mul_classIn_eq` — **THE EXACT PER-COLOUR COUNTING IDENTITY `2|E_i| = n + p - z`**, where `p`
  is the number of two-edge-path centres of the colour and `z` the number of vertices it misses:
  the sharp form of `Paths.two_mul_classIn_le_add` (`2|E_i| ≤ n + p`), which kept the `+p` and
  discarded the `-z`;
* `global_identity` — `n(n-1) + Isolated c = n·k + Paths c`, the exact global form of
  `Paths.mul_n_sub_one_le`;
* `clean_of_extremal` / `extremal_of_clean` — a colouring is extremal (`6k = 5(n-1)`) **iff** it has
  no isolated `(vertex, colour)` incidence **and** no unpaid edge.  This is the *converse* to the
  necessity theorems of `Rigidity.tight_pathFinset_is_STS` and
  `Main.extremal_no_isolated_vertex`, and it is what a construction has to achieve to certify
  itself extremal;
* `extremal_of_covered_cherries` — **a colouring in which every edge is paid for by a two-edge path
  and in which every colour reaches every vertex is extremal**: the design target of the first
  stage, in one verifiable statement;
* `defect_budget` — **a colouring that pays `r` colours more than `5(n-1)/6` pays at most `r · n`
  in defects**: with the published `6k ≤ 5(n-1) + δn` this reads `6·Isolated + 2·Defect ≤ δn²`,
  i.e. the first stage of arXiv:2208.12563 §4 / arXiv:2207.02920 §4 (which leaves
  `Θ(n^{2-δ})` edges over) must leave `o(n²)` *defects*, in the exact currency of the catalog
  constant `5/6`;
* `defect_divisible`, `three_mul_isolated_defect_divisible` — `n ∣ (6·Isolated + 2·Defect)`, and for
  odd `n`, `n ∣ (3·Isolated + Defect)`: a cheap *necessary* condition on the output of any
  construction, checkable before one looks at a single four-clique;
* `surplus_real`, `EG_surplus_real` — the same identity over `ℝ`, at the optimum:
  `f(n,4,5) = 5(n-1)/6 + (defects of an optimal colouring)`.

**Why this is the right shape for the missing half of the prize.**  The single prizable object
left is the existence, for every `δ > 0` and all large `n`, of an admissible colouring with
`6k ≤ 5(n-1) + δn` (`Partial.FamGreedyFamily`).  `defect_budget` says that such a colouring must
have `3·Isolated + Defect ≤ δn²/2`: the probabilistic content of the two papers is exactly a
statement about the two integers of this identity, and this file makes that statement a theorem of
the development rather than a remark.
-/

set_option maxHeartbeats 800000

namespace JSP140

variable {n k : ℕ} {c : Col n k}

/-! ### The two defects -/

/-- The vertices on which the colour `i` does not occur at all — the complement of the two-edge-path
centres `Counting.twoA` and of the single-edge vertices `Counting.oneB`. -/
def zeroA (c : Col n k) (i : Fin k) : Finset (Verts n) :=
  Finset.univ.filter fun v => (nb c i v (Finset.univ : Finset (Verts n))).card = 0

theorem mem_zeroA {c : Col n k} {i : Fin k} {v : Verts n} :
    v ∈ zeroA c i ↔ (nb c i v (Finset.univ : Finset (Verts n))).card = 0 := by
  simp [zeroA]

theorem mem_twoA {c : Col n k} {i : Fin k} {v : Verts n} :
    v ∈ twoA c i ↔ (nb c i v (Finset.univ : Finset (Verts n))).card = 2 := by
  simp [twoA]

theorem mem_oneB {c : Col n k} {i : Fin k} {v : Verts n} :
    v ∈ oneB c i ↔ (nb c i v (Finset.univ : Finset (Verts n))).card = 1 := by
  simp [oneB]

/-- **DEFECT I: the number of `(vertex, colour)` incidences on which the colour does not occur.** -/
def Isolated (c : Col n k) : ℕ := ∑ i : Fin k, (zeroA c i).card

/-- **DEFECT II: the edges of `K_n` that no two-edge path pays for.**  Every two-edge path brings
three edges with it (its own two and the isolated single edge between its leaves) and these
triples are pairwise disjoint (`Cherry.cherryEdges_disjoint`), so `Cherry.three_mul_paths_le_edges`
makes this a subtraction of natural numbers. -/
def Defect (c : Col n k) : ℕ :=
  (edgeFinset (Finset.univ : Finset (Verts n))).card - 3 * Paths c

/-- A constant summed over `Fin k` is that constant times `k`. -/
private theorem sum_const_fin' (m : ℕ) : (∑ _i : Fin k, (m : ℕ)) = m * k := by
  calc (∑ _i : Fin k, (m : ℕ)) = ∑ _i ∈ (Finset.univ : Finset (Fin k)), (m : ℕ) := rfl
    _ = (Finset.univ : Finset (Fin k)).card • (m : ℕ) := Finset.sum_const _
    _ = Fintype.card (Fin k) * m := by
      rw [Finset.card_univ]
      exact nsmul_eq_mul _ _
    _ = m * k := by rw [Fintype.card_fin, Nat.mul_comm]

/-- Sums of sums over `Fin k`, in the `Fintype` notation. -/
private theorem sum_add_fin {f g : Fin k → ℕ} :
    (∑ i, (f i + g i)) = (∑ i, f i) + ∑ i, g i := by
  simpa using (Finset.sum_add_distrib (s := (Finset.univ : Finset (Fin k))) (f := f) (g := g))

/-- Every colour misses at most all `n` vertices at each of the `k` colours: `Isolated c ≤ n·k`. -/
theorem Isolated_le (c : Col n k) : Isolated c ≤ n * k := by
  unfold Isolated
  calc ∑ i : Fin k, (zeroA c i).card ≤ ∑ i : Fin k, (n : ℕ) :=
        Finset.sum_le_sum fun i _ =>
          (Finset.card_le_card (Finset.subset_univ _)).trans
            (by rw [Finset.card_univ, Fintype.card_fin])
    _ = n * k := sum_const_fin' n

/-- Every colour class is a vertex-disjoint union of two-edge paths and isolated single edges, so
each of its edges is counted at both endpoints: `∑_v deg_i(v) = 2·|E_i|`.  This is the *exact*
degree sum (`Counting.degree_sum`), used below in split form. -/
private theorem sum_nb_card_eq {c : Col n k} (hc : Admissible c) (i : Fin k) :
    ∑ v ∈ (Finset.univ : Finset (Verts n)),
        (nb c i v (Finset.univ : Finset (Verts n))).card
      = 2 * (twoA c i).card + (oneB c i).card := by
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
      = (oneB c i).card := by
    calc _ = ∑ v ∈ oneB c i, (1 : ℕ) := by
          rw [oneB]; exact (Finset.sum_filter (fun v : Verts n =>
            (nb c i v (Finset.univ : Finset (Verts n))).card = 1) fun _ => (1 : ℕ)).symm
      _ = (oneB c i).card • (1 : ℕ) := Finset.sum_const _
      _ = (oneB c i).card := by rw [nsmul_eq_mul]; exact Nat.mul_one _
  calc (∑ v ∈ (Finset.univ : Finset (Verts n)),
        (nb c i v (Finset.univ : Finset (Verts n))).card)
      = ∑ v ∈ (Finset.univ : Finset (Verts n)),
          ((if (nb c i v (Finset.univ : Finset (Verts n))).card = 2 then (2 : ℕ) else 0)
            + (if (nb c i v (Finset.univ : Finset (Verts n))).card = 1 then (1 : ℕ) else 0)) :=
        Finset.sum_congr rfl fun v hv => key v hv
    _ = (∑ v ∈ (Finset.univ : Finset (Verts n)),
          (if (nb c i v (Finset.univ : Finset (Verts n))).card = 2 then (2 : ℕ) else 0))
        + ∑ v ∈ (Finset.univ : Finset (Verts n)),
          (if (nb c i v (Finset.univ : Finset (Verts n))).card = 1 then (1 : ℕ) else 0) :=
        Finset.sum_add_distrib
    _ = 2 * (twoA c i).card + (oneB c i).card := by rw [h1, h2]

/-! ### The three degree classes partition the vertex set -/

/-- **THE THREE DEGREE CLASSES OF A COLOUR CLASS PARTITION THE VERTICES.**  In an admissible
colouring every vertex carries `0`, `1` or `2` edges of a given colour
(`Counting.nb_card_le_two`), so `twoA`, `oneB` and `zeroA` partition `V`, and

    `|twoA| + |oneB| + |zeroA| = n`.

This is the exact form of `Paths.twoA_oneB_card_le`, which only recorded `≤ n`. -/
theorem card_twoA_oneB_zeroA {c : Col n k} (hc : Admissible c) (i : Fin k) :
    (twoA c i).card + (oneB c i).card + (zeroA c i).card = n := by
  have hdiscAB : Disjoint (twoA c i) (oneB c i) := by
    refine Finset.disjoint_left.mpr fun w hw1 hw2 => ?_
    have h1 := mem_twoA.mp hw1
    have h2 := mem_oneB.mp hw2
    omega
  have hdiscAZ : Disjoint (twoA c i) (zeroA c i) := by
    refine Finset.disjoint_left.mpr fun w hw1 hw2 => ?_
    have h1 := mem_twoA.mp hw1
    have h2 := mem_zeroA.mp hw2
    omega
  have hdiscBZ : Disjoint (oneB c i) (zeroA c i) := by
    refine Finset.disjoint_left.mpr fun w hw1 hw2 => ?_
    have h1 := mem_oneB.mp hw1
    have h2 := mem_zeroA.mp hw2
    omega
  have hdiscU : Disjoint (twoA c i ∪ oneB c i) (zeroA c i) :=
    Finset.disjoint_union_left.mpr ⟨hdiscAZ, hdiscBZ⟩
  have hsub1 : ((twoA c i ∪ oneB c i) ∪ zeroA c i) ⊆ (Finset.univ : Finset (Verts n)) :=
    Finset.subset_univ _
  have hsub2 : (Finset.univ : Finset (Verts n)) ⊆ (twoA c i ∪ oneB c i) ∪ zeroA c i := by
    intro w hw
    by_cases h0 : (nb c i w (Finset.univ : Finset (Verts n))).card = 0
    · exact Finset.mem_union.mpr (Or.inr (mem_zeroA.mpr h0))
    by_cases h1 : (nb c i w (Finset.univ : Finset (Verts n))).card = 1
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr (mem_oneB.mpr h1))))
    · have hle := nb_card_le_two hc i w (Finset.univ : Finset (Verts n))
      exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl (mem_twoA.mpr (by omega)))))
  have hunion : (twoA c i ∪ oneB c i) ∪ zeroA c i = (Finset.univ : Finset (Verts n)) :=
    Finset.Subset.antisymm hsub1 hsub2
  calc (twoA c i).card + (oneB c i).card + (zeroA c i).card
      = ((twoA c i ∪ oneB c i) ∪ zeroA c i).card := by
        rw [Finset.card_union_of_disjoint hdiscU, Finset.card_union_of_disjoint hdiscAB]
    _ = (Finset.univ : Finset (Verts n)).card := congrArg Finset.card hunion
    _ = n := Fintype.card_fin n

/-! ### The exact per-colour counting identity -/

/-- **THE EXACT PER-COLOUR COUNTING IDENTITY.**  The colour class of an admissible colouring which
has `p` two-edge-path centres and misses `z` vertices has exactly

    `2 * |E_i| = n + p - z`

edges — the sharp form of `Paths.two_mul_classIn_le_add` (`2|E_i| ≤ n + p`), which kept the `+p` and
discarded the `-z`.  A colour class which covers every vertex (`z = 0`) attains equality in
`Paths.two_mul_classIn_le_add`. -/
theorem two_mul_classIn_eq {c : Col n k} (hc : Admissible c) (i : Fin k) :
    2 * (classIn c i (Finset.univ : Finset (Verts n))).card
      = n + (twoA c i).card - (zeroA c i).card := by
  have hdeg : (∑ v ∈ (Finset.univ : Finset (Verts n)),
        (nb c i v (Finset.univ : Finset (Verts n))).card)
      = 2 * (classIn c i (Finset.univ : Finset (Verts n))).card :=
    degree_sum (c := c) (i := i) (Finset.univ : Finset (Verts n))
  have hsplit : (∑ v ∈ (Finset.univ : Finset (Verts n)),
        (nb c i v (Finset.univ : Finset (Verts n))).card)
      = 2 * (twoA c i).card + (oneB c i).card := sum_nb_card_eq hc i
  have hpart := card_twoA_oneB_zeroA hc i
  omega

/-- **THE PER-COLOUR COUNTING IDENTITY, WITHOUT SUBTRACTION.**
`2 · |E_i| + (the vertices the colour misses) = n + (its two-edge-path centres)`: this is
`two_mul_classIn_eq` rearranged, and it is the form in which the sum over the colours is taken. -/
theorem two_mul_classIn_add_zero {c : Col n k} (hc : Admissible c) (i : Fin k) :
    2 * (classIn c i (Finset.univ : Finset (Verts n))).card + (zeroA c i).card
      = n + (twoA c i).card := by
  have hdeg : (∑ v ∈ (Finset.univ : Finset (Verts n)),
        (nb c i v (Finset.univ : Finset (Verts n))).card)
      = 2 * (classIn c i (Finset.univ : Finset (Verts n))).card :=
    degree_sum (c := c) (i := i) (Finset.univ : Finset (Verts n))
  have hsplit : (∑ v ∈ (Finset.univ : Finset (Verts n)),
        (nb c i v (Finset.univ : Finset (Verts n))).card)
      = 2 * (twoA c i).card + (oneB c i).card := sum_nb_card_eq hc i
  have hpart := card_twoA_oneB_zeroA hc i
  omega

/-- `Paths.two_mul_classIn_le_add` is the shadow of `two_mul_classIn_eq`: the vertices missed by the
colour class are exactly what makes the inequality strict. -/
theorem two_mul_classIn_le_add' {c : Col n k} (hc : Admissible c) (i : Fin k) :
    2 * (classIn c i (Finset.univ : Finset (Verts n))).card ≤ n + (twoA c i).card := by
  have h := two_mul_classIn_eq hc i
  omega

/-! ### The global identity -/

/-- **THE EXACT GLOBAL IDENTITY (`Paths.mul_n_sub_one_le` with nothing thrown away).**  For every
admissible colouring,

    `2 * |E(K_n)| + Isolated c = n * k + Paths c`,

i.e. `n * k = n(n-1) - Paths c + Isolated c`: the colour count is the number of edges minus what
the two-edge paths pay for, plus what the missed vertices cost. -/
theorem sum_classIn_add_isolated {c : Col n k} (hc : Admissible c) :
    2 * (edgeFinset (Finset.univ : Finset (Verts n))).card + Isolated c = n * k + Paths c := by
  have h2 : (∑ i : Fin k,
      ((2 * (classIn c i (Finset.univ : Finset (Verts n))).card) + (zeroA c i).card))
      = ∑ i : Fin k, (n + (twoA c i).card) := by
    apply Finset.sum_congr rfl
    intro i _
    exact two_mul_classIn_add_zero hc i
  have h3 : (∑ i : Fin k, (n + (twoA c i).card)) = n * k + Paths c := by
    rw [sum_add_fin, sum_const_fin', Paths]
  calc 2 * (edgeFinset (Finset.univ : Finset (Verts n))).card + Isolated c
      = 2 * (∑ i : Fin k, (classIn c i (Finset.univ : Finset (Verts n))).card) + Isolated c := by
        rw [sum_card_classIn c, Isolated]
    _ = (∑ i : Fin k, (2 * (classIn c i (Finset.univ : Finset (Verts n))).card)) + Isolated c := by
        rw [Finset.mul_sum]
    _ = (∑ i : Fin k, (2 * (classIn c i (Finset.univ : Finset (Verts n))).card))
        + ∑ i : Fin k, (zeroA c i).card := rfl
    _ = ∑ i : Fin k,
        ((2 * (classIn c i (Finset.univ : Finset (Verts n))).card) + (zeroA c i).card) :=
        Finset.sum_add_distrib.symm
    _ = ∑ i : Fin k, (n + (twoA c i).card) := h2
    _ = n * k + Paths c := h3

/-- **THE EXACT COUNTING IDENTITY.**  `n * (n-1) + Isolated c = n * k + Paths c`: the sharp
counting bound `Paths.mul_n_sub_one_le` (`n(n-1) ≤ nk + Paths c`) with the isolated
`(vertex, colour)` incidences added back. -/
theorem global_identity {c : Col n k} (hc : Admissible c) :
    n * (n - 1) + Isolated c = n * k + Paths c := by
  have h := sum_classIn_add_isolated hc
  rw [card_edgeFinset_univ_two n] at h
  exact h

/-! ### The surplus identity -/

/-- **THE EXACT SURPLUS IDENTITY.**  For every admissible `k`-colouring `c` of `K_n` (`n ≥ 4`)

        `6 * (n * k) = 5 * n * (n - 1) + 6 * Isolated c + 2 * Defect c`,

i.e. **the number of colours exceeds `5(n-1)/6` by exactly `Isolated c / n + Defect c / (3n)`**.
No inequality is involved: the sharp counting bound `Cherry.five_sixth_lower` is the shadow of this
equality, and the two terms on the right are the two defects a construction controls. -/
theorem surplus_identity {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n) :
    6 * (n * k) = 5 * (n * (n - 1)) + 6 * Isolated c + 2 * Defect c := by
  have hg := global_identity hc
  have h3 := three_mul_paths_le_edges hc hn
  have hD : (edgeFinset (Finset.univ : Finset (Verts n))).card = 3 * Paths c + Defect c := by
    have h := Nat.add_sub_of_le h3
    have h2 : (edgeFinset (Finset.univ : Finset (Verts n))).card - 3 * Paths c = Defect c := rfl
    omega
  have hcard := card_edgeFinset_univ_two n
  omega

/-- **THE PRICE OF THE DEFECTS.**  `6 * Isolated c + 2 * Defect c = n * (6k - 5(n-1))`: the two
defects of a colouring are *determined* by its number of colours, in the exact currency of the
catalog constant `5/6`. -/
theorem surplus_of_k {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n) :
    6 * Isolated c + 2 * Defect c = n * (6 * k - 5 * (n - 1)) := by
  have hi := surplus_identity hc hn
  have hmul : n * (6 * k) = n * (5 * (n - 1)) + (6 * Isolated c + 2 * Defect c) := by
    rw [show 6 * (n * k) = n * (6 * k) from by ring,
      show 5 * (n * (n - 1)) = n * (5 * (n - 1)) from by ring] at hi
    omega
  have hle : n * (5 * (n - 1)) ≤ n * (6 * k) := by omega
  have hsub : n * (5 * (n - 1)) + (n * (6 * k) - n * (5 * (n - 1))) = n * (6 * k) :=
    Nat.add_sub_of_le hle
  have h3 : n * (6 * k) - n * (5 * (n - 1)) = 6 * Isolated c + 2 * Defect c := by
    omega
  calc 6 * Isolated c + 2 * Defect c = n * (6 * k) - n * (5 * (n - 1)) := h3.symm
    _ = n * (6 * k - 5 * (n - 1)) := (Nat.mul_sub_left_distrib n _ _).symm

/-- The two defects are non-negative and the identity recovers the sharp counting bound
`5(n-1) ≤ 6k` (`Cherry.five_sixth_lower`) — this identity *subsumes* it. -/
theorem five_sixth_lower_of_surplus {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n) :
    5 * (n - 1) ≤ 6 * k := by
  have hi := surplus_identity hc hn
  rw [show 6 * (n * k) = n * (6 * k) from by ring,
    show 5 * (n * (n - 1)) = n * (5 * (n - 1)) from by ring] at hi
  have hpos : (0 : ℕ) < n := by omega
  have h5 : n * (5 * (n - 1)) ≤ n * (6 * k) := by omega
  exact Nat.le_of_mul_le_mul_left h5 hpos

/-! ### Extremality: the converse to the rigidity theorems -/

/-- **A CLEAN COLOURING IS EXTREMAL.**  A colouring in which no colour misses a vertex and no edge
is left unpaid is extremal, i.e. `6k = 5(n-1)`: this is the *converse* of
`Rigidity.tight_pathFinset_is_STS` and `Main.extremal_no_isolated_vertex`, and it is what a
construction must achieve in order to certify itself. -/
theorem extremal_of_clean {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n)
    (h1 : Isolated c = 0) (h2 : Defect c = 0) : 6 * k = 5 * (n - 1) := by
  have hi := surplus_identity hc hn
  rw [h1, h2] at hi
  rw [show 6 * (n * k) = n * (6 * k) from by ring,
    show 5 * (n * (n - 1)) = n * (5 * (n - 1)) from by ring] at hi
  have hpos : (0 : ℕ) < n := by omega
  exact Nat.le_antisymm (Nat.le_of_mul_le_mul_left hi.le hpos)
    (Nat.le_of_mul_le_mul_left hi.symm.le hpos)

/-- **AN EXTREMAL COLOURING IS CLEAN.**  `6k = 5(n-1)` forces `Isolated c = 0` and `Defect c = 0`:
an extremal colouring has *no* missed `(vertex, colour)` incidence and *no* unpaid edge.  (The first
is `Main.extremal_no_isolated_vertex`; the second is the covering form of
`Rigidity.tight_pathFinset_is_STS`.) -/
theorem clean_of_extremal {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n)
    (h : 6 * k = 5 * (n - 1)) : Isolated c = 0 ∧ Defect c = 0 := by
  have hi := surplus_identity hc hn
  rw [show 6 * (n * k) = n * (6 * k) from by ring,
    show 5 * (n * (n - 1)) = n * (5 * (n - 1)) from by ring, ← h] at hi
  constructor <;> omega

/-- **THE DESIGN TARGET, IN ONE STATEMENT.**  An admissible colouring in which **every** edge of
`K_n` is paid for by a two-edge path and in which **every** colour reaches **every** vertex is
extremal: `6k = 5(n-1)`.  The two conditions are exactly `Defect c = 0` and `Isolated c = 0`, the
two terms of `surplus_identity`. -/
theorem extremal_of_covered_cherries {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n)
    (hP : 3 * Paths c = (edgeFinset (Finset.univ : Finset (Verts n))).card)
    (hZ : Isolated c = 0) : 6 * k = 5 * (n - 1) := by
  refine extremal_of_clean hc hn hZ ?_
  unfold Defect
  omega

/-! ### The budget a construction has to hit -/

/-- **THE DEFECT BUDGET.**  A colouring that pays `r` colours more than `5(n-1)/6` pays at most
`r · n` in defects: `6 · Isolated c + 2 · Defect c ≤ r · n`.  With the published
`6k ≤ 5(n-1) + δn` this reads `6·Isolated + 2·Defect ≤ δn²`, i.e. the first stage of
arXiv:2208.12563 §4 / arXiv:2207.02920 §4 must leave `o(n²)` defects. -/
theorem defect_budget {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n) {r : ℕ}
    (hr : 6 * k ≤ 5 * (n - 1) + r) : 6 * Isolated c + 2 * Defect c ≤ r * n := by
  have h := surplus_of_k hc hn
  have hle : 6 * k - 5 * (n - 1) ≤ r := Nat.sub_le_iff_le_add.mpr (by omega)
  calc 6 * Isolated c + 2 * Defect c = n * (6 * k - 5 * (n - 1)) := h
    _ ≤ n * r := by
      simpa [Nat.mul_comm, Nat.mul_left_comm] using Nat.mul_le_mul_left n hle
    _ = r * n := Nat.mul_comm _ _

/-- The budget for the two defects separately: a colouring within `r` of the counting bound misses
fewer than `r·n/6` vertices and leaves fewer than `r·n/2` edges unpaid. -/
theorem isolated_le_of_budget {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n) {r : ℕ}
    (hr : 6 * k ≤ 5 * (n - 1) + r) : 6 * Isolated c ≤ r * n := by
  have h := defect_budget hc hn hr
  omega

theorem defect_le_of_budget {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n) {r : ℕ}
    (hr : 6 * k ≤ 5 * (n - 1) + r) : 2 * Defect c ≤ r * n := by
  have h := defect_budget hc hn hr
  omega

/-! ### The arithmetic restriction on the output of a construction -/

/-- **THE DEFECTS OF A COLOURING ARE A MULTIPLE OF `n`.**  `n ∣ (6·Isolated c + 2·Defect c)`: a
cheap necessary condition on the output of any construction, checkable before a single four-clique
is looked at. -/
theorem defect_divisible {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n) :
    (6 * Isolated c + 2 * Defect c) % n = 0 := by
  rw [surplus_of_k hc hn, Nat.mul_mod_right]

/-- For **odd** `n`, half of that is also a multiple of `n`:
`n ∣ (3 · Isolated c + Defect c)`. -/
theorem three_mul_isolated_defect_divisible {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n)
    (hodd : n % 2 = 1) :
    (3 * Isolated c + Defect c) % n = 0 := by
  have h := surplus_of_k hc hn
  have hodd' : Odd n := by
    refine ⟨n / 2, ?_⟩
    have h := Nat.mod_add_div n 2
    omega
  have hcop : Nat.Coprime n 2 := by
    rw [Nat.coprime_two_right]
    exact hodd'
  have hdiv : n ∣ 2 * (3 * Isolated c + Defect c) := by
    refine ⟨6 * k - 5 * (n - 1), ?_⟩
    omega
  have h' : n ∣ (3 * Isolated c + Defect c) := hcop.dvd_of_dvd_mul_left hdiv
  obtain ⟨u, hu⟩ := h'
  rw [hu]
  exact Nat.mul_mod_right _ _

/-! ### The real form, and the optimum -/

/-- The identity over `ℝ`: `k = 5(n-1)/6 + Isolated c / n + Defect c / (3n)`. -/
theorem surplus_real {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n) :
    (k : ℝ) = 5 * ((n - 1 : ℕ) : ℝ) / 6 + ((Isolated c : ℕ) : ℝ) / ((n : ℕ) : ℝ)
      + ((Defect c : ℕ) : ℝ) / (3 * (n : ℕ)) := by
  have hi := surplus_identity hc hn
  have hn0 : (0 : ℕ) < n := by omega
  have hrw : (6 * (n * k) : ℝ) = 5 * ((n * (n - 1) : ℕ) : ℝ) + 6 * ((Isolated c : ℕ) : ℝ)
      + 2 * ((Defect c : ℕ) : ℝ) := by exact_mod_cast hi
  push_cast at hrw
  have hne : ((n : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn0)
  field_simp
  nlinarith [hrw]

/-- **THE CATALOG FUNCTION IS THE COUNTING BOUND PLUS THE DEFECTS OF AN OPTIMAL COLOURING.**  There
is an admissible colouring attaining `EG n` whose two defects satisfy the identity exactly, so

    `f(n,4,5) = 5(n-1)/6 + Isolated c / n + Defect c / (3n)`

for that `c`: the excess of `f(n,4,5)` over `5n/6` is the price of the defects of a colouring
witnessing it. -/
theorem EG_surplus_real (n : ℕ) (hn : 4 ≤ n) :
    ∃ c : Col n (EG n), Admissible c
      ∧ ((EG n : ℝ) = 5 * ((n - 1 : ℕ) : ℝ) / 6 + ((Isolated c : ℕ) : ℝ) / ((n : ℕ) : ℝ)
        + ((Defect c : ℕ) : ℝ) / (3 * (n : ℕ))) := by
  obtain ⟨c, hc⟩ := EG_admissible n
  exact ⟨c, hc, surplus_real hc hn⟩

/-- **THE EXACT BUDGET AT THE OPTIMUM, IN `ℕ`.**  There is a colouring attaining `EG n` with

    `6 · n · EG n = 5n(n-1) + 6 · Isolated c + 2 · Defect c`,

so `n · (6·EG n - 5(n-1))` *is* the total defect of an optimal colouring: the catalogue constant
`5/6` and the integer `f(n,4,5)` are linked by this exact equation. -/
theorem EG_surplus_exists (n : ℕ) (hn : 4 ≤ n) :
    ∃ c : Col n (EG n), Admissible c
      ∧ 6 * (n * EG n) = 5 * (n * (n - 1)) + 6 * Isolated c + 2 * Defect c := by
  obtain ⟨c, hc⟩ := EG_admissible n
  exact ⟨c, hc, surplus_identity hc hn⟩

/-! ### The two defects of the explicit colourings of `Tables.lean` -/

/-- **THE DEFECTS OF THE 5-COLOURING OF `K_6` (`Tables.sixCol`) ARE `0` AND `15`**: every colour
reaches every vertex (`Isolated = 0`, as an extremal colouring must, `Main.extremal_no_isolated_vertex`
at `n = 6`), and exactly `15 = C(6,2)/2` edges are left unpaid.  Its surplus over the counting
bound is `6·5 - 5·5 = 5` colours, and the identity charges all of it to the unpaid edges
(`6·0 + 2·15 = 30 = 6·(6·5 - 5·5)`). -/
theorem sixCol_defects : Isolated sixCol = 0 ∧ Defect sixCol = 15 := by native_decide

/-- **THE DEFECTS OF THE 8-COLOURING OF `K_9` (`Tables.nineCol`) ARE `4` AND `24`**:
`6·4 + 2·24 = 72 = 9·(6·8 - 5·8)`, and `3·4 + 24 = 36` is a multiple of `n = 9` exactly as
`three_mul_isolated_defect_divisible` demands. -/
theorem nineCol_defects : Isolated nineCol = 4 ∧ Defect nineCol = 24 := by native_decide

/-- **THE DEFECTS OF THE 9-COLOURING OF `K_10` (`Tables.tenCol`) ARE `8` AND `21`**:
`6·8 + 2·21 = 90 = 10·(6·9 - 5·9)`.  In particular this witness misses `8` `(vertex, colour)`
incidences and leaves `21` edges unpaid, so by `clean_of_extremal` it is not extremal — and by
`defect_budget` an extremal `K_{10}` colouring (which cannot exist, `6k = 5(n-1)` being
non-integral) would have to pay in defects. -/
theorem tenCol_defects : Isolated tenCol = 8 ∧ Defect tenCol = 21 := by native_decide

/-- **THE DEFECTS OF THE 10-COLOURING OF `K_11` (`Tables.elevenCol`) ARE `10` AND `25`**:
`6·10 + 2·25 = 110 = 11·(6·10 - 5·10)`. -/
theorem elevenCol_defects : Isolated elevenCol = 10 ∧ Defect elevenCol = 25 := by native_decide

/-- **THE DEFECT BUDGET OF ROUND 44, CHECKED ON A REAL WITNESS.**  The `K_10` colouring of
`Tables.tenCol` pays `6·9 - 5·9 = 9` more than the counting bound, and `defect_budget` predicts a
total defect of `9·10 = 90`, which `tenCol_defects` confirms (`48 + 42 = 90`) — and the divisibility
`defect_divisible` predicts, `90 % 10 = 0`. -/
theorem tenCol_budget : 6 * Isolated tenCol + 2 * Defect tenCol = 10 * (6 * 9 - 5 * (10 - 1)) := by
  native_decide

/-- ... and the divisibility restriction `defect_divisible` on the same witness. -/
theorem tenCol_divisible : (6 * Isolated tenCol + 2 * Defect tenCol) % 10 = 0 := by native_decide

/-- ... and the odd-`n` half of it, `three_mul_isolated_defect_divisible`, on the `K_11` witness. -/
theorem elevenCol_divisible : (3 * Isolated elevenCol + Defect elevenCol) % 11 = 0 := by native_decide

end JSP140
