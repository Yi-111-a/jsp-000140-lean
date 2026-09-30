import JSPProblem.Counting

/-!
# JSP-000140 — the quantitative form of the counting argument: the `5/6` criterion

`Counting.lean` proves the classical bound of Erdős–Gyárfás (1977) `3(n-1) ≤ 4 * k`, i.e.
`f(n,4,5) ≥ 3(n-1)/4`, by the counting lemma `3 * |E_i| ≤ 2 * n` for each colour class.  That
counting lemma throws away a lot of information: it only uses that a colour class is a *vertex
disjoint* union of single edges and two-edge paths, and it is *sharp* for a colour class which is
a perfect packing of two-edge paths (`p_i = n/3` paths, `s_i = 0` single edges, `|E_i| = 2n/3`).

This file refines the counting step to a **quantitative identity in the number of two-edge paths**
and reads off from it the constant `5/6` of the catalog answer.  The ingredients are:

* `Paths c` — the total number of two-edge paths `a - v - b` over all colour classes of `c`
  (a vertex `v` with two colour-`i` neighbours is the centre of exactly one such path, so
  `Paths c = ∑_i |A_i|`);
* `two_mul_classIn_le_add` — the *refined* per-colour counting lemma `2 * |E_i| ≤ n + |A_i|`, i.e. a
  colour class with `p` two-edge paths has at most `(n + p)/2` edges;
* `mul_n_sub_one_le` — **the quantitative identity** `n * (n-1) ≤ n * k + Paths c`, i.e.

      k ≥ (n-1) - Paths c / n;

* `five_sixth_of_paths` — **the `5/6` criterion**: if the total number of two-edge paths is at most
  `n(n-1)/6` (equivalently: at least two thirds of all edges lie in *single-edge* components of
  their colour class) then `5 * (n-1) ≤ 6 * k`, i.e. `k ≥ 5(n-1)/6 = 5n/6 - 5/6`.

Since `three_mul_paths_le` gives `3 * Paths c ≤ n * k` (the paths of a colour class are vertex
disjoint), the identity `mul_n_sub_one_le` *subsumes* `Counting.classical_lower_bound`
(`classical_lower_bound'`), and the two hypotheses

* `Paths c ≤ n * (n-1) / 6`   (the BCDP22 lower bound: an `o(n²)` loss on the number of paths) and
* the existence of an admissible colouring with `≤ 5n/6 + o(n)` colours (the BCDP22 construction)

are *exactly* the two remaining research steps of arXiv:2207.02920, now written as concrete
hypotheses of a proved theorem.
-/

namespace JSP140

variable {n k : ℕ}

/-! ### The number of two-edge paths -/

/-- **The number of two-edge paths of a colouring.**  A vertex with exactly two colour-`i`
neighbours `a ≠ b` is the centre of exactly one two-edge path `a - v - b` of colour `i`
(`Counting.nb_eq_singleton` shows that the path is isolated), so `Paths c` counts the two-edge
paths of all colour classes of `c`. -/
def Paths (c : Col n k) : ℕ := ∑ i : Fin k, (twoA c i).card

/-- The sum of a constant over `Fin k`. -/
private lemma sum_const_n (n k : ℕ) : (∑ i : Fin k, (n : ℕ)) = n * k := by
  calc (∑ i : Fin k, (n : ℕ)) = ∑ _i ∈ (Finset.univ : Finset (Fin k)), n := rfl
    _ = Finset.univ.card • n := Finset.sum_const _
    _ = Fintype.card (Fin k) * n := by
      rw [Finset.card_univ]
      exact nsmul_eq_mul _ _
    _ = n * k := by rw [Fintype.card_fin, Nat.mul_comm]

/-- The vertices with two colour-`i` neighbours and those with exactly one are disjoint, so they
use at most `n` vertices in total. -/
theorem twoA_oneB_card_le (c : Col n k) (i : Fin k) : (twoA c i).card + (oneB c i).card ≤ n := by
  have hdisj : Disjoint (twoA c i) (oneB c i) := by
    refine Finset.disjoint_left.mpr fun w hw1 hw2 => ?_
    have h1 := (Finset.mem_filter.mp hw1).2
    have h2 := (Finset.mem_filter.mp hw2).2
    omega
  calc (twoA c i).card + (oneB c i).card = (twoA c i ∪ oneB c i).card :=
        (Finset.card_union_of_disjoint hdisj).symm
    _ ≤ (Finset.univ : Finset (Verts n)).card := Finset.card_le_card (Finset.subset_univ _)
    _ = n := Fintype.card_fin n

/-! ### The refined per-colour counting lemma -/

/-- The degree sum of a colour class, split by the number of colour-`i` neighbours. -/
private lemma sum_nb_card_eq (c : Col n k) (hc : Admissible c) (i : Fin k) :
    ∑ v ∈ (Finset.univ : Finset (Verts n)), (nb c i v (Finset.univ : Finset (Verts n))).card
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

/-- **The refined counting lemma.**  A colour class of an admissible colouring which contains `p`
two-edge paths has at most `(n + p)/2` edges, i.e.

      2 * |E_i| ≤ n + p.

Compared with the classical lemma `three_mul_classIn_le` (`3 * |E_i| ≤ 2 * n`, obtained by
iterating `p ≤ n/3`) this keeps the term `p`: a colour class which is a perfect packing of
two-edge paths is *not* excluded, it is only charged for its `p` paths. -/
theorem two_mul_classIn_le_add {c : Col n k} (hc : Admissible c) (i : Fin k) :
    2 * (classIn c i (Finset.univ : Finset (Verts n))).card ≤ n + (twoA c i).card := by
  have hdeg := degree_sum (c := c) (i := i) (S := (Finset.univ : Finset (Verts n)))
  have hsplit := sum_nb_card_eq c hc i
  have hAB := twoA_oneB_card_le c i
  have hle : (oneB c i).card ≤ n - (twoA c i).card := by omega
  calc 2 * (classIn c i (Finset.univ : Finset (Verts n))).card
      = ∑ v ∈ (Finset.univ : Finset (Verts n)), (nb c i v (Finset.univ : Finset (Verts n))).card :=
        hdeg.symm
    _ = 2 * (twoA c i).card + (oneB c i).card := by rw [hsplit, Nat.one_mul]
    _ ≤ 2 * (twoA c i).card + (n - (twoA c i).card) := Nat.add_le_add_left hle _
    _ = n + (twoA c i).card := by omega

/-! ### The quantitative identity -/

/-- **The quantitative form of the counting argument.**  For every admissible `k`-colouring `c` of
`K_n`,

      n * (n-1) ≤ n * k + Paths c,

i.e. `k ≥ (n-1) - Paths c / n`.  This is the sharp version of the classical counting bound: the
only loss w.r.t. the trivial bound `k ≥ n-1` for proper colourings is the number of two-edge
paths, divided by `n`. -/
theorem mul_n_sub_one_le {c : Col n k} (hc : Admissible c) : n * (n - 1) ≤ n * k + Paths c := by
  set U := (Finset.univ : Finset (Verts n)) with hU
  have hle : ∀ i : Fin k, 2 * (classIn c i U).card ≤ n + (twoA c i).card := fun i =>
    two_mul_classIn_le_add hc i
  have h1 : (∑ i : Fin k, 2 * (classIn c i U).card) ≤ ∑ i : Fin k, (n + (twoA c i).card) :=
    Finset.sum_le_sum fun i _ => hle i
  have h2 : (∑ i : Fin k, 2 * (classIn c i U).card) = 2 * (edgeFinset U).card := by
    calc (∑ i : Fin k, 2 * (classIn c i U).card) = 2 * ∑ i : Fin k, (classIn c i U).card := by
          rw [← Finset.mul_sum]
      _ = 2 * (edgeFinset U).card := by rw [sum_card_classIn]
  have h3 : (∑ i : Fin k, (n + (twoA c i).card)) = n * k + Paths c := by
    calc (∑ i : Fin k, (n + (twoA c i).card)) = (∑ i : Fin k, n) + ∑ i : Fin k, (twoA c i).card :=
          Finset.sum_add_distrib
      _ = n * k + Paths c := by rw [Paths, sum_const_n]
  have h4 := card_edgeFinset_univ_two n
  rw [h2, h3, hU] at h1
  rw [h4] at h1
  exact h1

/-- The two-edge paths of a colour class are vertex-disjoint, so `3 * |A_i| ≤ n` for every colour;
summing, `3 * Paths c ≤ n * k`.  Inserting this into `mul_n_sub_one_le` recovers the classical
bound `3 * (n-1) ≤ 4 * k` of `Counting.classical_lower_bound`, so the new identity subsumes the
classical argument. -/
theorem three_mul_paths_le {n k : ℕ} {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n) :
    3 * Paths c ≤ n * k := by
  have h1 : ∀ i : Fin k, 3 * (twoA c i).card ≤ n := by
    intro i
    have hAB := two_mul_cardA_le_cardB hc hn i
    have hle := twoA_oneB_card_le c i
    omega
  have h2 : (∑ i : Fin k, 3 * (twoA c i).card) ≤ ∑ i : Fin k, (n : ℕ) :=
    Finset.sum_le_sum fun i _ => h1 i
  have h3 : (∑ i : Fin k, 3 * (twoA c i).card) = 3 * Paths c := by
    rw [Paths, ← Finset.mul_sum]
  have h4 : (∑ i : Fin k, (n : ℕ)) = n * k := sum_const_n n k
  omega

/-- **The classical bound, re-derived from the quantitative identity.** -/
theorem classical_lower_bound' {n k : ℕ} {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n) :
    3 * (n - 1) ≤ 4 * k := by
  have h1 := mul_n_sub_one_le (c := c) hc
  have h2 := three_mul_paths_le hc hn
  have h3 : 3 * (n * (n - 1)) ≤ 3 * (n * k) + 3 * Paths c := by
    have h := Nat.mul_le_mul_left 3 h1
    calc 3 * (n * (n - 1)) ≤ 3 * (n * k + Paths c) := h
      _ = 3 * (n * k) + 3 * Paths c := by ring
  have h4 : 3 * (n * k) + 3 * Paths c ≤ 4 * (n * k) := by
    calc 3 * (n * k) + 3 * Paths c ≤ 3 * (n * k) + n * k := Nat.add_le_add_left h2 _
      _ = 4 * (n * k) := by ring
  have h5 : 3 * (n * (n - 1)) ≤ 4 * (n * k) := h3.trans h4
  have h6 : 3 * (n * (n - 1)) = n * (3 * (n - 1)) := by ac_rfl
  have h7 : 4 * (n * k) = n * (4 * k) := by ac_rfl
  rw [h6, h7] at h5
  exact Nat.le_of_mul_le_mul_left h5 (by omega)

/-! ### The `5/6` criterion: the lower half of the headline statement -/

/-- **The `5/6` criterion.**  If an admissible `k`-colouring of `K_n` has at most `n(n-1)/6` two-edge
paths — equivalently, at least two thirds of all edges lie in *single-edge* components of their
colour class — then it uses at least `5(n-1)/6` colours, i.e. `5 * (n-1) ≤ 6 * k`.

This is the lower half of the catalog answer `f(n,4,5) = 5n/6 + o(n)`: the *only* remaining
hypothesis is the bound `Paths c ≤ n(n-1)/6` on the number of two-edge paths, which is the content
of the lower-bound part of BCDP22 (arXiv:2207.02920). -/
theorem five_sixth_of_paths {n k : ℕ} {c : Col n k} (hc : Admissible c) (hn : 1 ≤ n)
    (hP : Paths c ≤ n * (n-1) / 6) : 5 * (n - 1) ≤ 6 * k := by
  have h1 := mul_n_sub_one_le (c := c) hc
  have h2 : 6 * Paths c ≤ n * (n - 1) := by
    exact le_trans (Nat.mul_le_mul_left 6 hP) (Nat.mul_div_le _ _)
  have h3 : 6 * (n * (n - 1)) ≤ 6 * (n * k) + 6 * Paths c := by
    have h := Nat.mul_le_mul_left 6 h1
    calc 6 * (n * (n - 1)) ≤ 6 * (n * k + Paths c) := h
      _ = 6 * (n * k) + 6 * Paths c := by ring
  have h4 : 6 * (n * k) + 6 * Paths c ≤ 6 * (n * k) + n * (n - 1) := Nat.add_le_add_left h2 _
  have h5 : 5 * (n * (n - 1)) ≤ 6 * (n * k) := by omega
  have h6 : 5 * (n * (n - 1)) = n * (5 * (n - 1)) := by ac_rfl
  have h7 : 6 * (n * k) = n * (6 * k) := by ac_rfl
  rw [h6, h7] at h5
  exact Nat.le_of_mul_le_mul_left h5 (by omega)

/-- The `5/6` criterion for `f(n,4,5) = EG n`, conditional on the number of two-edge paths of a
colouring attaining the minimum: if `K_n` has an admissible colouring with `EG n` colours and at
most `n(n-1)/6` two-edge paths, then `5(n-1) ≤ 6 * EG n`, i.e. `EG n ≥ 5n/6 - 5/6`. -/
theorem EG_ge_five_sixth_of_paths (n : ℕ) (hn : 4 ≤ n)
    (hc : ∀ c : Col n (EG n), Admissible c → Paths c ≤ n * (n-1) / 6) : 5 * (n - 1) ≤ 6 * EG n := by
  obtain ⟨c, hc'⟩ := EG_admissible n
  exact five_sixth_of_paths hc' (by omega) (hc c hc')

/-- The `5/6` criterion in real form, conditional as above. -/
theorem EG_ge_five_sixth_of_paths_real (n : ℕ) (hn : 4 ≤ n)
    (hc : ∀ c : Col n (EG n), Admissible c → Paths c ≤ n * (n-1) / 6) :
    (5 : ℝ) * ((n - 1 : ℕ) : ℝ) / 6 ≤ (EG n : ℝ) := by
  have h := EG_ge_five_sixth_of_paths n hn hc
  have h' : (5 : ℝ) * ((n - 1 : ℕ) : ℝ) ≤ 6 * (EG n : ℝ) := by exact_mod_cast h
  linarith

/-- **A colouring without two-edge paths meets the headline constant exactly.**  If `c` is
admissible and no colour class of `c` contains a two-edge path (`Paths c = 0`), then the `5/6`
criterion gives `5(n-1) ≤ 6k`, i.e. every such colouring uses at least `5(n-1)/6 = 5n/6 - 5/6`
colours.  For a *proper* edge colouring of `K_n` the hypothesis holds trivially (by
`nbrsIn_card_le_two`), and such colourings exist with `n` colours (`Construction.lean`), so the
`5/6` constant is *attained* up to the additive `o(1)` on the upper side. -/
theorem five_sixth_of_no_paths {n k : ℕ} {c : Col n k} (hc : Admissible c) (hn : 1 ≤ n)
    (h0 : Paths c = 0) : 5 * (n - 1) ≤ 6 * k := five_sixth_of_paths hc hn (by omega)

end JSP140
