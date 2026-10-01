import JSPProblem.Singles

/-!
# `JSP-000140` — the per-colour profile of an extremal admissible colouring

`Local.lean` completes the extremal structure **point by point** (per vertex: `tight_singleStar`
says every vertex is incident with exactly `(n-1)/3` isolated single edges).  The remaining gap,
named in `discovery/JSP-000140/policy.json` after round 25, is the **per-colour** side: for a
*fixed colour* `i`, nothing says how many two-edge paths and how many isolated single edges that
colour class contains.  `Extremal.tight_twoA_le` gives only the bound `3 * a_i + 3 ≤ n`, and
`Rigidity.tight_classes_span` the degree identity `a_i + b_i = n`; the exact composition of a
single colour class was never stated.

This file states it, and it turns out to be rigid.  Write `a_i = |twoA c i|` for the number of
two-edge paths of colour `i` and `s_i` for the number of isolated single edges of colour `i`
(`Singles.card_single_in_classIn` already identifies the latter as
`|classIn c i| - 2 * a_i`).  Then in the extremal case:

* **`tight_class_vertex_count` — THE PER-COLOUR VERTEX-COUNTING IDENTITY**
  `3 * a_i + 2 * s_i = n`, i.e. **the colour class `i` partitions the `n` vertices into `a_i`
  triples (the two-edge paths) and `s_i` pairs (the isolated single edges)**, exactly.  (The
  per-vertex form of this is `Rigidity.tight_degree`; the per-colour form is new, and it is the
  `3`/`2` shadow of `tight_classes_span`.)

* **`tight_class_profile` — THE EXACT PROFILE.**  For `n = 6t + 1` there is a single integer
  `u ∈ [0, t-1]` such that

      a_i = 2u + 1        and        s_i = 3 (t - 1 - u) + 2,

  i.e. **the whole colour class is determined by one parameter**: an odd number of two-edge paths
  in `[1, 2t-1]`, and a number of isolated single edges in `{2, 5, 8, …, 3t-1}`.  No colour class
  of an extremal colouring can be a packing of two-edge paths with fewer than two single edges.

* `tight_single_ge_two`, `tight_single_mod_three` — the two consequences that matter for a
  construction: **every colour class contains at least two isolated single edges, and their number
  is `≡ 2 (mod 3)`.**  (Arithmetically: `n ≡ 1 (mod 6)` and `a_i` odd give
  `n - 3 a_i ≡ 4 (mod 6)`, so `s_i = (n - 3a_i)/2 ≡ 2 (mod 3)`.)

* `tight_sum_class_vertex` — globally: the `k` colour classes each partition the vertex set, so
  `3 * Paths c + 2 * (#single edges) = k * n`, which in the extremal case reads `5 * Paths c = k * n`.

* **`tight_thirteen_profile` — THE PROFILE AT `n = 13`, THE FIRST ORDER AT WHICH THE SHARP CONSTANT
  `5/6` COULD BE ATTAINED.**  For an admissible `10`-colouring of `K_13` (which *is* extremal, since
  `6 * 10 = 5 * 12`) every colour class contains either

      3 two-edge paths + 2 isolated single edges,   or   1 two-edge path + 5 isolated single edges,

  and `tight_thirteen_eight` shows that **exactly eight of the ten colour classes are of the first
  type** (`Σ_i a_i = 26 = 8 * 3 + 2 * 1`).  This is a sharp, finite, machine-checkable constraint on
  the open question `Main.extremal_at_thirteen_is_open` (does `K_13` carry an admissible
  `10`-colouring?): any such colouring would have to have exactly this colour-class profile, with
  eight classes of `8` edges and two of `7`.
-/

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

namespace JSP140

variable {n k : ℕ}

/-- The degree sum of a colour class, split by colour-degree (repeated from `Rigidity.lean`, where
it is private, so that this file does not depend on that private copy). -/
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

/-! ### The exact size of a colour class in the extremal case -/

/-- **IN THE EXTREMAL CASE THE SIZE OF A COLOUR CLASS IS `(n + a_i)/2`**, where `a_i` is the number
of two-edge paths of that colour.  Indeed `degree_sum` gives `2 |E_i| = 2 a_i + b_i` and
`Rigidity.tight_classes_span` gives `b_i = n - a_i`. -/
theorem tight_class_edges {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n)
    (h3 : 3 * Paths c = (edgeFinset (Finset.univ : Finset (Verts n))).card)
    (hk : 6 * k = 5 * (n - 1)) (i : Fin k) :
    2 * (classIn c i (Finset.univ : Finset (Verts n))).card = n + (twoA c i).card := by
  have hdeg := degree_sum (c := c) (i := i) (S := (Finset.univ : Finset (Verts n)))
  have hsplit := sum_nb_card_eq c hc i
  have hspan := tight_classes_span hc hn h3 hk i
  omega

/-! ### The per-colour vertex-counting identity -/

/-- **THE PER-COLOUR VERTEX-COUNTING IDENTITY.**  If `c` is an admissible colouring of `K_n`
(`n ≥ 4`) attaining the counting bound of `Cherry.five_sixth_lower` with exactly `5(n-1)/6`
colours, then for every colour `i`

    3 * (number of two-edge paths of colour i) + 2 * (number of isolated single edges of colour i)
      = n.

In words: **each colour class of an extremal colouring is a spanning vertex-disjoint union of
two-edge paths and isolated single edges** — `a_i` triples and `s_i` pairs, exactly filling the `n`
vertices.  This is the per-*colour* shadow of `Rigidity.tight_degree` (which is per vertex) and of
`Rigidity.tight_classes_span` (which only counts degrees): it says that no vertex is used twice
inside one colour class, quantitatively. -/
theorem tight_class_vertex_count {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n)
    (h3 : 3 * Paths c = (edgeFinset (Finset.univ : Finset (Verts n))).card)
    (hk : 6 * k = 5 * (n - 1)) (i : Fin k) :
    3 * (twoA c i).card
      + 2 * (singleFinset c ∩ classIn c i (Finset.univ : Finset (Verts n))).card = n := by
  have hdeg := degree_sum (c := c) (i := i) (S := (Finset.univ : Finset (Verts n)))
  have hsplit := sum_nb_card_eq c hc i
  have hspan := tight_classes_span hc hn h3 hk i
  have hcls := card_single_in_classIn hc hn i
  have hle := two_mul_twoA_le_classIn hc hn i
  omega

/-- **The isolated single edges of a colour class are counted by `(n - 3 a_i)/2`.**  The per-colour
form of `tight_class_vertex_count`, with the paths solved for. -/
theorem tight_single_card_of_class {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n)
    (h3 : 3 * Paths c = (edgeFinset (Finset.univ : Finset (Verts n))).card)
    (hk : 6 * k = 5 * (n - 1)) (i : Fin k) :
    2 * (singleFinset c ∩ classIn c i (Finset.univ : Finset (Verts n))).card
      = n - 3 * (twoA c i).card := by
  have h := tight_class_vertex_count hc hn h3 hk i
  omega

/-! ### The exact profile of one colour class -/

/-- **THE EXACT PROFILE OF ONE COLOUR CLASS.**  Let `c` be an admissible colouring of `K_{6t+1}`
(`n ≥ 4`) attaining the counting bound with `5(n-1)/6` colours, and let `i` be a colour.  Then
there is a unique integer `u` with `u ≤ t - 1` such that

    |{two-edge paths of colour i}|  =  2 u + 1,
    |{isolated single edges of colour i}|  =  3 (t - 1 - u) + 2.

So the colour class of `i` consists of `2u+1` two-edge paths and `3(t-1-u)+2` isolated single
edges: its number of paths is an odd integer of `1 … 2t-1` and its number of single edges is an
integer of `2 … 3t-1` congruent to `2` modulo `3`.  **The whole colour class is determined by one
parameter**, which is the local specification any construction of the extremal family must meet,
colour by colour. -/
theorem tight_class_profile {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n)
    (h3 : 3 * Paths c = (edgeFinset (Finset.univ : Finset (Verts n))).card)
    (hk : 6 * k = 5 * (n - 1)) (t : ℕ) (ht : n = 6 * t + 1) (i : Fin k) :
    ∃ u : ℕ, u ≤ t - 1 ∧ (twoA c i).card = 2 * u + 1 ∧
      (singleFinset c ∩ classIn c i (Finset.univ : Finset (Verts n))).card = 3 * (t - 1 - u) + 2 := by
  have hodd := (tight_twoA_odd hc hn h3 hk i)
  obtain ⟨u, hu⟩ : ∃ u : ℕ, (twoA c i).card = 2 * u + 1 := ⟨(twoA c i).card / 2, by
    calc (twoA c i).card = (twoA c i).card % 2 + 2 * ((twoA c i).card / 2) :=
          (Nat.mod_add_div _ 2).symm
      _ = 2 * ((twoA c i).card / 2) + 1 := by rw [hodd]; exact Nat.add_comm _ _⟩
  have hle := tight_twoA_le hc hn h3 hk i
  have hv := tight_class_vertex_count hc hn h3 hk i
  refine ⟨u, by omega, hu, by omega⟩

/-- **EVERY COLOUR CLASS OF AN EXTREMAL COLOURING CONTAINS AT LEAST TWO ISOLATED SINGLE EDGES.**
No colour class can be a perfect packing of two-edge paths. -/
theorem tight_single_ge_two {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n)
    (h3 : 3 * Paths c = (edgeFinset (Finset.univ : Finset (Verts n))).card)
    (hk : 6 * k = 5 * (n - 1)) (t : ℕ) (ht : n = 6 * t + 1) (i : Fin k) :
    2 ≤ (singleFinset c ∩ classIn c i (Finset.univ : Finset (Verts n))).card := by
  obtain ⟨u, hu, -, hs⟩ := tight_class_profile hc hn h3 hk t ht i
  rw [hs]
  omega

/-- **THE NUMBER OF ISOLATED SINGLE EDGES OF A COLOUR CLASS IS `≡ 2 (mod 3)`.**  Together with
`tight_single_ge_two` this says the per-class count of single edges is one of `2, 5, 8, …`. -/
theorem tight_single_mod_three {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n)
    (h3 : 3 * Paths c = (edgeFinset (Finset.univ : Finset (Verts n))).card)
    (hk : 6 * k = 5 * (n - 1)) (t : ℕ) (ht : n = 6 * t + 1) (i : Fin k) :
    (singleFinset c ∩ classIn c i (Finset.univ : Finset (Verts n))).card % 3 = 2 := by
  obtain ⟨u, hu, -, hs⟩ := tight_class_profile hc hn h3 hk t ht i
  rw [hs]
  omega

/-- **EVERY COLOUR CLASS OF AN EXTREMAL COLOURING CONTAINS AT LEAST ONE TWO-EDGE PATH.** -/
theorem tight_twoA_ge_one {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n)
    (h3 : 3 * Paths c = (edgeFinset (Finset.univ : Finset (Verts n))).card)
    (hk : 6 * k = 5 * (n - 1)) (t : ℕ) (ht : n = 6 * t + 1) (i : Fin k) :
    1 ≤ (twoA c i).card := by
  obtain ⟨u, -, hu, -⟩ := tight_class_profile hc hn h3 hk t ht i
  rw [hu]
  omega

/-- **NO COLOUR CLASS OF AN EXTREMAL COLOURING IS A PURE MATCHING OR A PURE PACKING OF PATHS.**
Every colour class contains at least one two-edge path *and* at least two isolated single edges,
and both counts are rigid (`tight_class_profile`). -/
theorem tight_class_mixed {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n)
    (h3 : 3 * Paths c = (edgeFinset (Finset.univ : Finset (Verts n))).card)
    (hk : 6 * k = 5 * (n - 1)) (t : ℕ) (ht : n = 6 * t + 1) (i : Fin k) :
    1 ≤ (twoA c i).card ∧
      2 ≤ (singleFinset c ∩ classIn c i (Finset.univ : Finset (Verts n))).card :=
  ⟨tight_twoA_ge_one hc hn h3 hk t ht i, tight_single_ge_two hc hn h3 hk t ht i⟩

/-! ### The global per-colour count -/

/-- **THE `k` COLOUR CLASSES EACH PARTITION THE VERTEX SET.**  For every admissible colouring
attaining the counting bound with `5(n-1)/6` colours,

    Σ_i [ 3 * a_i + 2 * s_i ]  =  k * n,

i.e. `3 * Paths c + 2 * (#isolated single edges) = k * n`.  In the extremal case both sums equal
`Paths c = n(n-1)/6`, so this reads `5 * n(n-1)/6 = k * n`, the identity behind the counting
bound.  It is the global form of `tight_class_vertex_count` and a consistency check on the
whole extremal description. -/
theorem tight_sum_class_vertex {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n)
    (h3 : 3 * Paths c = (edgeFinset (Finset.univ : Finset (Verts n))).card)
    (hk : 6 * k = 5 * (n - 1)) :
    (∑ i : Fin k, (3 * (twoA c i).card
      + 2 * (singleFinset c ∩ classIn c i (Finset.univ : Finset (Verts n))).card)) = k * n := by
  have hsum : (∑ i : Fin k,
      (3 * (twoA c i).card
        + 2 * (singleFinset c ∩ classIn c i (Finset.univ : Finset (Verts n))).card))
      = ∑ _i : Fin k, n := Finset.sum_congr rfl fun i _ => tight_class_vertex_count hc hn h3 hk i
  rw [hsum]
  simp

/-- **THE SINGLE EDGES SPLIT EVENLY OVER THE COLOUR CLASSES.**  In the extremal case the sum of the
per-class counts of isolated single edges equals `Paths c = n(n-1)/6`:

    Σ_i s_i  =  Σ_i a_i  =  n(n-1)/6.

This is the global form of `card_single_in_classIn` together with the tightness `|E| = 3 * Paths c`.
-/
theorem tight_sum_single_eq_paths {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n)
    (h3 : 3 * Paths c = (edgeFinset (Finset.univ : Finset (Verts n))).card)
    (hk : 6 * k = 5 * (n - 1)) :
    (∑ i : Fin k, (singleFinset c ∩ classIn c i (Finset.univ : Finset (Verts n))).card) = Paths c := by
  have hkey : ∀ i : Fin k,
      (singleFinset c ∩ classIn c i (Finset.univ : Finset (Verts n))).card
        + 2 * (twoA c i).card = (classIn c i (Finset.univ : Finset (Verts n))).card := by
    intro i
    have h := card_single_in_classIn hc hn i
    have hle := two_mul_twoA_le_classIn hc hn i
    omega
  have h1 : (∑ i : Fin k, ((singleFinset c ∩ classIn c i (Finset.univ : Finset (Verts n))).card
      + 2 * (twoA c i).card)) = ∑ i : Fin k, (classIn c i (Finset.univ : Finset (Verts n))).card :=
    Finset.sum_congr rfl fun i _ => hkey i
  have h2 : (∑ i : Fin k, (classIn c i (Finset.univ : Finset (Verts n))).card)
      = 3 * ∑ i : Fin k, (twoA c i).card := by
    rw [sum_card_classIn c _, h3.symm, Paths]
  have hmul : (∑ i : Fin k, 2 * (twoA c i).card) = 2 * ∑ i : Fin k, (twoA c i).card := by
    rw [Finset.mul_sum]
  rw [Finset.sum_add_distrib, hmul] at h1
  simp only [Paths]
  omega

/-- **In the extremal case the single edges of a colour class number `2, 5, 8, …`, so the total
number of single edges is `≡ 2k (mod 3)`.**  Together with `Singles.tight_card_singles`
(`#single edges = Paths c = n(n-1)/6`) this is the per-class congruence that a construction of the
extremal family must satisfy globally as well. -/
theorem tight_sum_single_mod_three {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n)
    (h3 : 3 * Paths c = (edgeFinset (Finset.univ : Finset (Verts n))).card)
    (hk : 6 * k = 5 * (n - 1)) (t : ℕ) (ht : n = 6 * t + 1) :
    Paths c % 3 = (2 * k) % 3 := by
  have hmod : ∀ i : Fin k,
      (singleFinset c ∩ classIn c i (Finset.univ : Finset (Verts n))).card % 3 = 2 :=
    fun i => tight_single_mod_three hc hn h3 hk t ht i
  have hsplit : ∀ i : Fin k,
      (singleFinset c ∩ classIn c i (Finset.univ : Finset (Verts n))).card
        = 2 + 3 * ((singleFinset c ∩ classIn c i (Finset.univ : Finset (Verts n))).card / 3) := by
    intro i
    have h := Nat.mod_add_div
      (singleFinset c ∩ classIn c i (Finset.univ : Finset (Verts n))).card 3
    rw [hmod i] at h
    omega
  have h3sum : (∑ i : Fin k, (singleFinset c ∩ classIn c i (Finset.univ : Finset (Verts n))).card)
      = 2 * k + 3 * (∑ i : Fin k,
          ((singleFinset c ∩ classIn c i (Finset.univ : Finset (Verts n))).card / 3)) := by
    calc (∑ i : Fin k, (singleFinset c ∩ classIn c i (Finset.univ : Finset (Verts n))).card)
        = ∑ i : Fin k, (2 + 3 * ((singleFinset c ∩ classIn c i
            (Finset.univ : Finset (Verts n))).card / 3)) :=
          Finset.sum_congr rfl fun i _ => hsplit i
      _ = (∑ _i : Fin k, (2 : ℕ)) + ∑ i : Fin k,
          3 * ((singleFinset c ∩ classIn c i (Finset.univ : Finset (Verts n))).card / 3) :=
          Finset.sum_add_distrib
      _ = 2 * k + 3 * (∑ i : Fin k,
          ((singleFinset c ∩ classIn c i (Finset.univ : Finset (Verts n))).card / 3)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Finset.mul_sum,
            Nat.cast_id, Nat.mul_comm]
  rw [← tight_sum_single_eq_paths hc hn h3 hk, h3sum, Nat.add_mul_mod_self_left]

/-! ### The tiling condition is equivalent to extremality -/

/-- **THE SUM OF THE PER-COLOUR SINGLE-EDGE COUNTS, IN GENERAL.**  For every admissible colouring
(`n ≥ 4`), `Σ_i s_i = |E(K_n)| - 2 * Paths c`: the single edges are the edges of the colour classes
that are not edges of two-edge paths.  (In the extremal case this is `Paths c` again.) -/
private lemma sum_single_eq {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n) :
    (∑ i : Fin k, (singleFinset c ∩ classIn c i (Finset.univ : Finset (Verts n))).card)
      + 2 * Paths c = (edgeFinset (Finset.univ : Finset (Verts n))).card := by
  have hkey : ∀ i : Fin k,
      (singleFinset c ∩ classIn c i (Finset.univ : Finset (Verts n))).card
        + 2 * (twoA c i).card = (classIn c i (Finset.univ : Finset (Verts n))).card := by
    intro i
    have h := card_single_in_classIn hc hn i
    have hle := two_mul_twoA_le_classIn hc hn i
    omega
  have h1 : (∑ i : Fin k, ((singleFinset c ∩ classIn c i
      (Finset.univ : Finset (Verts n))).card + 2 * (twoA c i).card))
      = (∑ i : Fin k, (classIn c i (Finset.univ : Finset (Verts n))).card) :=
    Finset.sum_congr rfl fun i _ => hkey i
  have hmul : (∑ i : Fin k, 2 * (twoA c i).card) = 2 * ∑ i : Fin k, (twoA c i).card := by
    rw [Finset.mul_sum]
  rw [Finset.sum_add_distrib, hmul] at h1
  simp only [Paths]
  rw [h1, sum_card_classIn c _]

/-- Splitting a sum of a linear combination into a sum over `Fin m`. -/
private lemma split_sum (m : ℕ) (f g : Fin m → ℕ) :
    (3 * ∑ i, f i + 2 * ∑ i, g i) = ∑ i, (3 * f i + 2 * g i) := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]

/-- Summing the per-colour tiling condition over the colours. -/
private lemma sum_tiling {c : Col n k}
    (htiling : ∀ i : Fin k, 3 * (twoA c i).card
        + 2 * (singleFinset c ∩ classIn c i (Finset.univ : Finset (Verts n))).card = n) :
    3 * Paths c
      + 2 * (∑ i : Fin k,
          (singleFinset c ∩ classIn c i (Finset.univ : Finset (Verts n))).card) = k * n := by
  have hsum : (∑ i : Fin k, (3 * (twoA c i).card
      + 2 * (singleFinset c ∩ classIn c i (Finset.univ : Finset (Verts n))).card)) = k * n := by
    calc (∑ i : Fin k, (3 * (twoA c i).card
        + 2 * (singleFinset c ∩ classIn c i (Finset.univ : Finset (Verts n))).card))
        = ∑ _i : Fin k, n := Finset.sum_congr rfl fun i _ => htiling i
      _ = k * n := by simp
  rw [Paths]
  rw [split_sum]
  exact hsum

/-- **THE PER-COLOUR TILING CONDITION IMPLIES THE SHARP `5/6` COUNTING BOUND.**  Suppose every
colour class of an admissible colouring of `K_n` (`n ≥ 4`) partitions the vertex set into its
two-edge paths (three vertices each) and its isolated single edges (two vertices each):

    ∀ i,  3 * a_i + 2 * s_i = n.

Then `5 * (n - 1) ≤ 6 * k`, i.e. `k ≥ 5(n-1)/6`.

This says that **the sharp counting constant `5/6` of the Erdős–Gyárfás lower bound is a *per-colour*
consequence of a local condition**, not only a global counting artefact: summing the tiling
condition gives `k n = 2 |E| - Paths c`, and inserting `Paths c ≤ |E|/3`
(`Cherry.six_mul_paths_le`) yields `k n ≥ (5/3) |E| = (5/3) · n(n-1)/2`. -/
theorem five_sixth_of_classwise_tiling {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n)
    (htiling : ∀ i : Fin k, 3 * (twoA c i).card
        + 2 * (singleFinset c ∩ classIn c i (Finset.univ : Finset (Verts n))).card = n) :
    5 * (n - 1) ≤ 6 * k := by
  have hX : 3 * Paths c
      + 2 * (∑ i : Fin k,
          (singleFinset c ∩ classIn c i (Finset.univ : Finset (Verts n))).card) = k * n :=
    sum_tiling htiling
  have h1 := sum_single_eq hc hn
  have h2 := card_edgeFinset_univ_two n
  have h6 := six_mul_paths_le hc hn
  -- `k n = 2|E| - Paths c`
  have hkn : k * n + Paths c = 2 * (edgeFinset (Finset.univ : Finset (Verts n))).card := by omega
  -- at most a third of the edges lie in two-edge paths (`Cherry.six_mul_paths_le`)
  have hthird : 6 * Paths c ≤ 2 * (edgeFinset (Finset.univ : Finset (Verts n))).card := by omega
  -- hence `k n ≥ (5/6) · 2|E|`, i.e. `6 k n ≥ 5 · 2|E| = 5 n (n-1)`
  have hstep : 6 * (k * n)
      ≥ 5 * (2 * (edgeFinset (Finset.univ : Finset (Verts n))).card) := by omega
  have hstep' : 6 * (k * n) ≥ 5 * (n * (n - 1)) := by rw [← h2]; exact hstep
  have hmul : n * (5 * (n - 1)) ≤ n * (6 * k) := by
    calc n * (5 * (n - 1)) = 5 * (n * (n - 1)) := by ring
      _ ≤ 6 * (k * n) := hstep'
      _ = n * (6 * k) := by ring
  exact Nat.le_of_mul_le_mul_left hmul (by omega : (0 : ℕ) < n)

/-- **EXTREMALITY IS EQUIVALENT TO THE PER-COLOUR TILING CONDITION.**  Let `c` be an admissible
colouring of `K_n` (`n ≥ 4`) with exactly `5(n-1)/6` colours (`6k = 5(n-1)`).  Then

    the counting bound `Cherry.five_sixth_lower` is attained   ⟺   every colour class of `c`
    partitions the vertex set into two-edge paths and isolated single edges (`3 a_i + 2 s_i = n`).

The forward direction is `tight_class_vertex_count`.  The backward direction is
`tight_of_classwise_tiling` below: with `6k = 5(n-1)` the tiling condition forces
`6 * Paths c = n (n - 1) = 2 |E(K_n)|`, i.e. `3 * Paths c = |E(K_n)|` — the two-edge paths form a
Steiner triple system (`Rigidity.tight_pathFinset_is_STS`).  So the extremal colourings are exactly
those whose colour classes are *perfect* packings of the vertex set, triple by triple and pair by
pair. -/
theorem tight_of_classwise_tiling {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n)
    (hk : 6 * k = 5 * (n - 1))
    (htiling : ∀ i : Fin k, 3 * (twoA c i).card
        + 2 * (singleFinset c ∩ classIn c i (Finset.univ : Finset (Verts n))).card = n) :
    3 * Paths c = (edgeFinset (Finset.univ : Finset (Verts n))).card := by
  have hX : 3 * Paths c
      + 2 * (∑ i : Fin k,
          (singleFinset c ∩ classIn c i (Finset.univ : Finset (Verts n))).card) = k * n :=
    sum_tiling htiling
  have h1 := sum_single_eq hc hn
  have h2 := card_edgeFinset_univ_two n
  -- `k n = 2|E| - Paths c` and `6 k = 5 (n-1) = 5 (n-1)`, so `6 k n = 10|E|`, whence
  -- `6 Paths c = 2 |E|`
  have hkn : k * n + Paths c = 2 * (edgeFinset (Finset.univ : Finset (Verts n))).card := by omega
  have h6kn : 6 * (k * n)
      = 10 * (edgeFinset (Finset.univ : Finset (Verts n))).card := by
    have hA : 5 * (n * (n - 1))
        = 10 * (edgeFinset (Finset.univ : Finset (Verts n))).card := by
      rw [← h2]; ring
    calc 6 * (k * n) = (6 * k) * n := by ring
      _ = (5 * (n - 1)) * n := by rw [hk]
      _ = 5 * (n * (n - 1)) := by ring
      _ = 10 * (edgeFinset (Finset.univ : Finset (Verts n))).card := hA
  have h6P : 6 * Paths c = 2 * (edgeFinset (Finset.univ : Finset (Verts n))).card := by omega
  omega

/-- **THE CHARACTERISATION.**  For an admissible colouring of `K_n` (`n ≥ 4`) with exactly
`5(n-1)/6` colours, the counting bound is attained **iff** every colour class is a spanning
vertex-disjoint union of two-edge paths and isolated single edges — equivalently, iff the colouring
is in the extremal case of `Rigidity.lean` (its two-edge paths form a Steiner triple system). -/
theorem classwise_tiling_iff_extremal {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n)
    (hk : 6 * k = 5 * (n - 1)) :
    (∀ i : Fin k, 3 * (twoA c i).card
        + 2 * (singleFinset c ∩ classIn c i (Finset.univ : Finset (Verts n))).card = n)
      ↔ 3 * Paths c = (edgeFinset (Finset.univ : Finset (Verts n))).card := by
  have h3 := tight_attained hc hn hk
  constructor
  · intro htiling
    exact tight_of_classwise_tiling hc hn hk htiling
  · intro _
    exact fun i => tight_class_vertex_count hc hn h3 hk i

/-! ### The profile at `n = 13`, the first order at which the constant `5/6` can be attained -/

/-- **AT `n = 13` EVERY COLOUR CLASS HAS AN ODD NUMBER OF TWO-EDGE PATHS, AND THAT NUMBER IS `1` OR
`3`.**  (For an admissible `10`-colouring of `K_13`, `6 * 10 = 5 * (13 - 1)`, so the colouring is
extremal and `Rigidity.tight_ge_thirteen` does not rule it out: `13` is exactly the first order at
which the sharp counting bound `5(n-1)/6 = 10` could be attained.) -/
theorem tight_thirteen_paths {c : Col 13 10} (hc : Admissible c) (hn : 4 ≤ 13) (i : Fin 10) :
    (twoA c i).card = 1 ∨ (twoA c i).card = 3 := by
  have h3 := tight_attained hc hn (by omega)
  obtain ⟨u, hu, ha, -⟩ := tight_class_profile hc hn h3 (by omega) 2 (by omega) i
  rw [ha]
  omega

/-- **THE EXACT PROFILE OF A COLOUR CLASS OF `K_13`.**  In an admissible `10`-colouring of `K_13`
every colour class consists of either `3` two-edge paths and `2` isolated single edges, or `1`
two-edge path and `5` isolated single edges. -/
theorem tight_thirteen_profile {c : Col 13 10} (hc : Admissible c) (hn : 4 ≤ 13) (i : Fin 10) :
    ((twoA c i).card = 1 ∧
        (singleFinset c ∩ classIn c i (Finset.univ : Finset (Verts 13))).card = 5) ∨
      ((twoA c i).card = 3 ∧
        (singleFinset c ∩ classIn c i (Finset.univ : Finset (Verts 13))).card = 2) := by
  have h3 := tight_attained hc hn (by omega)
  obtain ⟨u, hu, ha, hs⟩ := tight_class_profile hc hn h3 (by omega) 2 (by omega) i
  rw [ha, hs] at *
  omega

/-- **THE TOTAL NUMBER OF TWO-EDGE PATHS OF AN ADMISSIBLE `10`-COLOURING OF `K_13` IS `26`** — i.e.
`Paths c = n(n-1)/6`, as `Rigidity.tight_paths` says, here at the first admissible extremal order. -/
theorem tight_thirteen_paths_total {c : Col 13 10} (hc : Admissible c) (hn : 4 ≤ 13) :
    (∑ i : Fin 10, (twoA c i).card) = 26 := by
  have h3 := tight_attained hc hn (by omega)
  have hp := tight_paths hc hn h3
  rw [Paths] at hp
  rw [hp]

/-- **EXACTLY EIGHT OF THE TEN COLOUR CLASSES OF AN ADMISSIBLE `10`-COLOURING OF `K_13` HAVE THREE
TWO-EDGE PATHS**, the remaining two having one each: `8 * 3 + 2 * 1 = 26 = Paths c`.  Together with
`tight_thirteen_profile` this determines the whole extremal colouring of `K_13` up to the choice of
the eight three-path classes: eight colour classes of `3 + 2 = 5` … precisely, of `2 * 3 + 2 = 8`
edges each and two colour classes of `2 * 1 + 5 = 7` edges each (`8 * 8 + 2 * 7 = 78 = C(13,2)`). -/
theorem tight_thirteen_eight {c : Col 13 10} (hc : Admissible c) (hn : 4 ≤ 13) :
    (∑ i : Fin 10, (if (twoA c i).card = 3 then (1 : ℕ) else 0)) = 8 := by
  have hkey : ∀ i : Fin 10, (twoA c i).card
      = 1 + 2 * (if (twoA c i).card = 3 then (1 : ℕ) else 0) := by
    intro i
    rcases tight_thirteen_paths hc hn i with h | h
    · rw [h, if_neg (by omega)]
    · rw [h, if_pos (by omega)]
  have h1 : (∑ i : Fin 10, (twoA c i).card)
      = ∑ i : Fin 10, (1 + 2 * (if (twoA c i).card = 3 then (1 : ℕ) else 0)) :=
    Finset.sum_congr rfl fun i _ => hkey i
  have hA : (∑ _i : Fin 10, (1 : ℕ)) = 10 := by simp
  have hB : (∑ i : Fin 10, 2 * (if (twoA c i).card = 3 then (1 : ℕ) else 0))
      = 2 * (∑ i : Fin 10, (if (twoA c i).card = 3 then (1 : ℕ) else 0)) := by
    rw [Finset.mul_sum]
  have htot := tight_thirteen_paths_total hc hn
  rw [h1, Finset.sum_add_distrib, hA, hB] at htot
  omega

/-- **THE COLOUR CLASSES OF AN ADMISSIBLE `10`-COLOURING OF `K_13` HAVE EIGHT CLASSES OF EIGHT EDGES
AND TWO OF SEVEN.**  Equivalently the sizes `|classIn c i|` take the value `8` eight times and `7`
twice (`8 * 8 + 2 * 7 = 78 = C(13,2)`).  Together with `tight_thirteen_profile` and
`tight_thirteen_eight` this is a complete description of the *sizes* of the ten colour classes at
the first order at which the counting bound `5(n-1)/6` could be attained. -/
theorem tight_thirteen_edges {c : Col 13 10} (hc : Admissible c) (hn : 4 ≤ 13) (i : Fin 10) :
    7 ≤ (classIn c i (Finset.univ : Finset (Verts 13))).card
      ∧ (classIn c i (Finset.univ : Finset (Verts 13))).card ≤ 8 := by
  have hkey : (singleFinset c ∩ classIn c i (Finset.univ : Finset (Verts 13))).card
      + 2 * (twoA c i).card = (classIn c i (Finset.univ : Finset (Verts 13))).card := by
    have h := card_single_in_classIn hc hn i
    have hle := two_mul_twoA_le_classIn hc hn i
    omega
  rcases tight_thirteen_profile hc hn i with ⟨ha, hs⟩ | ⟨ha, hs⟩
  · rw [ha, hs] at hkey
    omega
  · rw [ha, hs] at hkey
    omega

end JSP140
