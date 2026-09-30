import JSPProblem.Rigidity

/-!
# JSP-000140 — arithmetic obstructions to extremality: the extremal order is at least `13`

Round 13 proved that an admissible colouring of `K_n` attains the extremal value `5(n-1)/6` of the
lower bound `Cherry.five_sixth_lower` **iff** its two-edge paths form a Steiner triple system of
order `n` (`Rigidity.tight_pathFinset_is_STS`, `Rigidity.tight_attained`), and round 14 added that
in the extremal case every colour class *spans* the vertex set
(`Rigidity.tight_classes_span`, `Rigidity.tight_covers`): each of the `5(n-1)/6` colour classes is a
spanning vertex-disjoint union of two-edge paths and isolated single edges.

This file extracts the **arithmetic** content of that description, and in particular the
**parity obstruction** which was invisible to the counting arguments of `Cherry.lean` and
`Paths.lean`:

* `oneB_even` — **the handshaking lemma for a colour class.**  In a colour class every vertex has
  colour-degree `0`, `1` or `2` (`Counting.nb_card_le_two`), and the degree sum is
  `2 * |E_i|` (even, `Counting.degree_sum`).  Hence the number of degree-`1` vertices is **even**:
  the degree-`1` vertices come in pairs, the two ends of a single edge.
* `two_mul_twoA_le_classIn`, `tight_three_mul_twoA_le` — the counting refinement
  `3 * |A_i| ≤ n` for every colour class of an extremal colouring, where `A_i` is the set of
  two-edge-path centres in colour `i`.
* `tight_twoA_odd` — **in the extremal case every colour class contains an ODD number of two-edge
  paths.**  Indeed `|A_i| + |B_i| = n` with `n ≡ 1 (mod 6)` (odd) and `|B_i|` even.
* `tight_twoA_le` — consequently `|A_i| ≤ (n-4)/3` in the extremal case.
* **`tight_ge_thirteen` — the extremal order is at least `13`.**  The `n(n-1)/6` two-edge paths are
  distributed over the `5(n-1)/6` colour classes, each of which contains at most `(n-4)/3` of them;
  for `n = 6t+1` this reads `(6t+1)t ≤ 5t(2t-1)`, i.e. `t ≥ 2`.
* `no_five_colouring_of_K7` and **`EG_seven_ge_six` — the sharp `5/6` lower bound is *strict* at
  `n = 7`**: `f(7,4,5) ≥ 6 > 5 = 5(7-1)/6`.  So the extremal value of `Cherry.five_sixth_lower` is
  *not* attained at `n = 7`, the only order below `13` with `n ≡ 1 (mod 6)`.

This is the first place where the local structure of the extremal colourings yields an *improved*
lower bound rather than a characterisation: the counting arguments of `Cherry.lean` are blind to
the parity of the degree-`1` vertices, but the extremal description is not.
-/

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

namespace JSP140

variable {n k : ℕ}

/-- The sum of a constant over `Fin k`. -/
private lemma sum_const_fin (m k : ℕ) : (∑ i : Fin k, (m : ℕ)) = m * k := by
  calc (∑ i : Fin k, (m : ℕ)) = ∑ _i ∈ (Finset.univ : Finset (Fin k)), m := rfl
    _ = (Finset.univ : Finset (Fin k)).card • m := Finset.sum_const _
    _ = Fintype.card (Fin k) * m := by
      rw [Finset.card_univ]
      exact nsmul_eq_mul _ _
    _ = m * k := by rw [Fintype.card_fin, Nat.mul_comm]

/-! ### The handshaking lemma for a single colour class -/

/-- The degree sum of a colour class, split by the number of colour-`i` neighbours (the copy of
`Paths.sum_nb_card_eq` which is private to that file and to `Rigidity.lean`). -/
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

/-- **THE HANDSHAKING LEMMA FOR A COLOUR CLASS.**  In a colour class of an admissible colouring
every vertex has colour-degree `0`, `1` or `2`, and the sum of the colour-degrees is
`2 * |E_i|` — an even number.  Hence

    |B_i| = |{v : v has exactly one colour-`i` neighbour}|

is **even**: the degree-`1` vertices of a colour class come in pairs, the two ends of a single edge
of that class (a two-edge path contributes its two leaves, which is an even number of
contributions per path as well).

This is the parity input which the counting lemmas of `Cherry.lean` (`3 * Paths c ≤ |E(K_n)|`) and
`Paths.lean` (`2 * |E_i| ≤ n + |A_i|`) discard: they only ever compare *cardinalities* linearly, and
lose the parity of `B_i`. -/
theorem oneB_even {c : Col n k} (hc : Admissible c) (i : Fin k) :
    ∃ r : ℕ, (oneB c i).card = 2 * r := by
  have hdeg := degree_sum (c := c) (i := i) (S := (Finset.univ : Finset (Verts n)))
  have hsplit := sum_nb_card_eq c hc i
  refine ⟨(classIn c i (Finset.univ : Finset (Verts n))).card - (twoA c i).card, ?_⟩
  omega

/-! ### The two edges of a two-edge path -/

/-- **The two edges of the two-edge path centred at `v` in colour `i`** (the third edge of
`cherryEdges c i v`, the one joining the two leaves, is *not* included here). -/
def pathEdges (c : Col n k) (i : Fin k) (v : Verts n) : Finset (Sym2 (Verts n)) :=
  (Nbrs c i v).image (fun a => s(v, a))

theorem mem_pathEdges {c : Col n k} (i : Fin k) {v : Verts n} {e : Sym2 (Verts n)} :
    e ∈ pathEdges c i v ↔ ∃ a ∈ Nbrs c i v, e = s(v, a) := by
  rw [pathEdges, Finset.mem_image]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, ha, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, ha, rfl⟩

/-- **A two-edge path contributes two edges of its colour class.** -/
theorem card_pathEdges {c : Col n k} (i : Fin k) {v : Verts n} (hv : v ∈ twoA c i) :
    (pathEdges c i v).card = 2 := by
  have hinj : Function.Injective (fun a : Verts n => s(v, a)) := by
    intro a b h
    exact sym2_inj_right h
  rw [pathEdges, Finset.card_image_of_injective _ hinj]
  exact card_twoA i hv

/-- The edges of a two-edge path belong to its colour class. -/
theorem pathEdges_subset_classIn {c : Col n k} (i : Fin k) {v : Verts n} {e : Sym2 (Verts n)}
    (he : e ∈ pathEdges c i v) : e ∈ classIn c i (Finset.univ : Finset (Verts n)) := by
  obtain ⟨a, ha, he⟩ := (mem_pathEdges i).mp he
  refine mem_classIn.mpr ⟨?_, ?_⟩
  · rw [he]
    exact mem_edgeFinset_mk (Finset.mem_univ v) (Finset.mem_univ a) (mem_Nbrs.mp ha).1.symm
  · rw [he]
    exact (mem_Nbrs.mp ha).2

/-- **The two edges of two different two-edge paths of the same colour are disjoint.**  An edge of
`K_n` joins at most one pair of two-edge-path centres of a given colour (`Cherry.not_two_centres`),
so the pairs contributed by the paths of a colour class are disjoint: the paths of a colour class
use `2 * |A_i|` distinct edges. -/
theorem pathEdges_disjoint {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n) (i : Fin k) {v w : Verts n}
    (hv : v ∈ twoA c i) (hw : w ∈ twoA c i) (hne : v ≠ w) :
    Disjoint (pathEdges c i v) (pathEdges c i w) := by
  refine Finset.disjoint_left.mpr fun e he1 he2 => ?_
  obtain ⟨a, ha, he1⟩ := (mem_pathEdges i).mp he1
  obtain ⟨b, hb, he2⟩ := (mem_pathEdges i).mp he2
  have hcol : c s(v, a) = i := (mem_Nbrs.mp ha).2
  have hcol' : c s(w, b) = i := (mem_Nbrs.mp hb).2
  have hvw : c s(v, w) = i := by
    have heq : s(v, a) = s(w, b) := he1.symm.trans he2
    rcases sym2_inj heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact absurd h1 hne
    · rw [← h1] at hcol'
      rw [Sym2.eq_swap] at hcol'
      exact hcol'
  exact not_two_centres (a := v) (b := w) hc hn i hne (card_twoA i hv) (card_twoA i hw) hvw

/-- **THE PATH EDGES OF A COLOUR CLASS ARE DISJOINT AND USE `2 * |A_i|` EDGES.**  Every two-edge
path of colour `i` contributes its two edges, and no edge is contributed twice — this is the
per-class form of the packing lemma `Cherry.cherryEdges_disjoint`. -/
theorem two_mul_twoA_le_classIn {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n) (i : Fin k) :
    2 * (twoA c i).card ≤ (classIn c i (Finset.univ : Finset (Verts n))).card := by
  have hcard : ∀ v ∈ twoA c i, (pathEdges c i v).card = 2 :=
    fun v hv => card_pathEdges i hv
  have hsub (v : Verts n) (hv : v ∈ twoA c i) (e : Sym2 (Verts n)) (he : e ∈ pathEdges c i v) :
      e ∈ classIn c i (Finset.univ : Finset (Verts n)) := pathEdges_subset_classIn i he
  have hdisc : (↑(twoA c i) : Set (Verts n)).PairwiseDisjoint (fun v => pathEdges c i v) := by
    intro v hv w hw hvw
    exact pathEdges_disjoint hc hn i (Finset.mem_coe.mp hv) (Finset.mem_coe.mp hw) hvw
  have h1 : ((twoA c i).biUnion (fun v => pathEdges c i v)).card
      = ∑ v ∈ twoA c i, (pathEdges c i v).card := Finset.card_biUnion hdisc
  have h2 : (∑ v ∈ twoA c i, (pathEdges c i v).card) = 2 * (twoA c i).card := by
    calc (∑ v ∈ twoA c i, (pathEdges c i v).card) = ∑ v ∈ twoA c i, (2 : ℕ) := by
          refine Finset.sum_congr rfl fun v hv => hcard v (Finset.mem_coe.mp hv)
      _ = (twoA c i).card • (2 : ℕ) := Finset.sum_const _
      _ = 2 * (twoA c i).card := by rw [nsmul_eq_mul]; exact Nat.mul_comm _ _
  have h3 : ((twoA c i).biUnion (fun v => pathEdges c i v)).card
      ≤ (classIn c i (Finset.univ : Finset (Verts n))).card := by
    refine Finset.card_le_card (Finset.biUnion_subset.mpr fun v hv => ?_)
    exact fun e he => hsub v (Finset.mem_coe.mp hv) e he
  omega

/-! ### The arithmetic of an extremal colouring -/

/-- **Every colour class of an extremal colouring contains at most `n/3` two-edge paths.**  In the
extremal case the class spans the vertex set (`Rigidity.tight_classes_span`:
`|A_i| + |B_i| = n`), the degree-`1` vertices come in pairs (`oneB_even`), and the two edges of each
path are distinct edges of the class (`two_mul_twoA_le_classIn`); hence `3 * |A_i| ≤ n`. -/
theorem tight_three_mul_twoA_le {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n)
    (h3 : 3 * Paths c = (edgeFinset (Finset.univ : Finset (Verts n))).card)
    (hk : 6 * k = 5 * (n - 1)) (i : Fin k) : 3 * (twoA c i).card ≤ n := by
  have hspan := tight_classes_span hc hn h3 hk i
  obtain ⟨r, hr⟩ := oneB_even hc i
  have hdeg := degree_sum (c := c) (i := i) (S := (Finset.univ : Finset (Verts n)))
  have hsplit := sum_nb_card_eq c hc i
  have hcls := two_mul_twoA_le_classIn hc hn i
  omega

/-- **IN THE EXTREMAL CASE EVERY COLOUR CLASS CONTAINS AN ODD NUMBER OF TWO-EDGE PATHS.**  Indeed the
class spans the vertex set, so `|A_i| = n - |B_i|`, and `|B_i|` is even (`oneB_even`) while
`n ≡ 1 (mod 6)` is odd (`Rigidity.tight_mod6`).

Equivalently: in an extremal colouring the number of isolated single edges of a colour class,
`(|B_i| - 2|A_i|)/2`, is such that `3 * |A_i| ≤ n` is *not* attained — the class can never be a
perfect packing of two-edge paths, which would need `n ≡ 0 (mod 3)`. -/
theorem tight_twoA_odd {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n)
    (h3 : 3 * Paths c = (edgeFinset (Finset.univ : Finset (Verts n))).card)
    (hk : 6 * k = 5 * (n - 1)) (i : Fin k) : (twoA c i).card % 2 = 1 := by
  have hspan := tight_classes_span hc hn h3 hk i
  obtain ⟨r, hr⟩ := oneB_even hc i
  obtain ⟨hmod, -⟩ := tight_mod6 hc hn h3 hk
  have hodd : n % 2 = 1 := by omega
  omega

/-- **In the extremal case no colour class wastes more than two vertices' worth of paths:**
`3 * |A_i| + 3 ≤ n`, i.e. `|A_i| ≤ (n-4)/3`.  This is `tight_three_mul_twoA_le` sharpened by the
parity: `3 * |A_i|` is odd and `n` is odd and not divisible by `3`, so `3 * |A_i| ≠ n`. -/
theorem tight_twoA_le {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n)
    (h3 : 3 * Paths c = (edgeFinset (Finset.univ : Finset (Verts n))).card)
    (hk : 6 * k = 5 * (n - 1)) (i : Fin k) : 3 * (twoA c i).card + 3 ≤ n := by
  have h1 := tight_three_mul_twoA_le hc hn h3 hk i
  have hmod6 := (tight_mod6 hc hn h3 hk).1
  have hodd := tight_twoA_odd hc hn h3 hk i
  obtain ⟨t, ht⟩ : ∃ t : ℕ, n = 6 * t + 1 := ⟨n / 6, by
    calc n = n % 6 + 6 * (n / 6) := (Nat.mod_add_div n 6).symm
      _ = 6 * (n / 6) + 1 := by rw [hmod6]; exact Nat.add_comm _ _⟩
  obtain ⟨u, hu⟩ : ∃ u : ℕ, (twoA c i).card = 2 * u + 1 := ⟨(twoA c i).card / 2, by
    calc (twoA c i).card = (twoA c i).card % 2 + 2 * ((twoA c i).card / 2) :=
          (Nat.mod_add_div _ 2).symm
      _ = 2 * ((twoA c i).card / 2) + 1 := by rw [hodd]; exact Nat.add_comm _ _⟩
  omega

/-- **THE TOTAL NUMBER OF TWO-EDGE PATHS IS BOUNDED BY THE PER-CLASS BOUND.**  In the extremal case
the `n(n-1)/6` two-edge paths are distributed over the `5(n-1)/6` colour classes, each of which
contains at most `(n-4)/3` of them (`tight_twoA_le`). -/
theorem tight_paths_le {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n)
    (h3 : 3 * Paths c = (edgeFinset (Finset.univ : Finset (Verts n))).card)
    (hk : 6 * k = 5 * (n - 1)) (t : ℕ) (ht : n = 6 * t + 1) :
    Paths c ≤ k * (2 * t - 1) := by
  have hle : ∀ i : Fin k, (twoA c i).card ≤ 2 * t - 1 := by
    intro i
    have h := tight_twoA_le hc hn h3 hk i
    omega
  calc Paths c = ∑ i : Fin k, (twoA c i).card := rfl
    _ ≤ ∑ i : Fin k, (2 * t - 1) := Finset.sum_le_sum fun i _ => hle i
    _ = k * (2 * t - 1) := by
      rw [sum_const_fin]
      exact Nat.mul_comm _ _

/-- **AN EXTREMAL ADMISSIBLE COLOURING OF `K_n` REQUIRES `n ≥ 13`.**  This is the first *numerical*
obstruction to extremality obtained in this development.  By `Rigidity.tight_mod6` extremality
forces `n = 6t + 1`; the `n(n-1)/6 = (6t+1)t` two-edge paths are spread over the `k = 5t` colour
classes, each of which contains at most `2t-1` of them (`tight_twoA_le`), whence

    (6t+1) t ≤ 5t (2t-1)   ⟺   6t + 1 ≤ 10t - 5   ⟺   t ≥ 2   ⟺   n ≥ 13.

In particular the extremal value `5(n-1)/6` of `Cherry.five_sixth_lower` — and hence the Steiner
triple system of `Rigidity.tight_pathFinset_is_STS` — **cannot occur for `n = 7`**, the only
admissible order below `13` with `n ≡ 1 (mod 6)`. -/
theorem tight_ge_thirteen {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n)
    (hk : 6 * k = 5 * (n - 1)) : 13 ≤ n := by
  have h3 := tight_attained hc hn hk
  obtain ⟨hmod, -⟩ := tight_mod6 hc hn h3 hk
  obtain ⟨t, ht⟩ : ∃ t : ℕ, n = 6 * t + 1 := ⟨n / 6, by
    calc n = n % 6 + 6 * (n / 6) := (Nat.mod_add_div n 6).symm
      _ = 6 * (n / 6) + 1 := by rw [hmod]; exact Nat.add_comm _ _⟩
  have hk5 : k = 5 * t := by
    have h6 : 6 * k = 30 * t := by rw [hk, ht]; omega
    omega
  have hP : 6 * Paths c = n * (n - 1) := by
    have h7 := card_edgeFinset_univ_two n
    omega
  have hbound : Paths c ≤ k * (2 * t - 1) := tight_paths_le hc hn h3 hk t ht
  have hstep : 6 * (Paths c) ≤ 6 * (5 * t * (2 * t - 1)) := by
    have h6 := Nat.mul_le_mul_left 6 hbound
    have h2 : 6 * (k * (2 * t - 1)) = 6 * (5 * t * (2 * t - 1)) := by rw [hk5]
    exact h6.trans_eq h2
  have hA : (6 * t) * (6 * t + 1) ≤ (30 * t) * (2 * t - 1) := by
    have h' : (6 * t) * (6 * t + 1) = n * (n - 1) := by
      rw [ht]
      have hsub : (6 * t + 1) - 1 = 6 * t := by omega
      rw [hsub]
      ring
    calc (6 * t) * (6 * t + 1) = 6 * (Paths c) := by rw [hP, h']
      _ ≤ 6 * (5 * t * (2 * t - 1)) := hstep
      _ = (30 * t) * (2 * t - 1) := by ring
  have hA2 : (6 * t) * (6 * t + 1) ≤ (6 * t) * (5 * (2 * t - 1)) := by
    calc (6 * t) * (6 * t + 1) ≤ (30 * t) * (2 * t - 1) := hA
      _ = (6 * t) * (5 * (2 * t - 1)) := by ring
  have hB : 6 * t + 1 ≤ 5 * (2 * t - 1) :=
    Nat.le_of_mul_le_mul_left hA2 (by omega : (0 : ℕ) < 6 * t)
  omega

/-- **No admissible colouring of `K_7` uses at most five colours.**  The lower bound
`Cherry.five_sixth_lower` forces `k ≥ 5` for `n = 7`, and `tight_ge_thirteen` rules out `k = 5`. -/
theorem no_five_or_fewer_of_K7 {k : ℕ} (c : Col 7 k) (hc : Admissible c) (hk : k ≤ 5) : False := by
  have h := five_sixth_lower hc (by omega)
  have hcontra : 6 * k = 5 * (7 - 1) := by omega
  have h13 := tight_ge_thirteen hc (by omega) hcontra
  omega

/-- **There is no admissible `5`-colouring of `K_7`.** -/
theorem no_five_colouring_of_K7 : ¬ (∃ c : Col 7 5, Admissible c) := by
  rintro ⟨c, hc⟩
  exact no_five_or_fewer_of_K7 c hc (by omega)

/-- **THE SHARP LOWER BOUND IS STRICT AT `n = 7`.**  `f(7,4,5) ≥ 6`, one more than the value
`5(7-1)/6 = 5` of the general lower bound `Cherry.five_sixth_lower`: the extremal case is
impossible at `n = 7` (`tight_ge_thirteen`), so the lower bound is not attained there. -/
theorem EG_seven_ge_six : 6 * 6 ≤ 6 * EG 7 := by
  by_contra hcon
  have hle : EG 7 ≤ 5 := by omega
  obtain ⟨c, hc⟩ := EG_admissible 7
  exact no_five_or_fewer_of_K7 c hc hle

/-- **The lower bound for `f(7,4,5)` is `6`, not `5`.** -/
theorem EG_seven_ge_six_nat : 6 ≤ EG 7 := by
  have h := EG_seven_ge_six
  omega

/-- The same statement in real form: `f(7,4,5) ≥ 6`. -/
theorem EG_seven_ge_six_real : (6 : ℝ) ≤ (EG 7 : ℝ) := by
  have h : 6 ≤ EG 7 := EG_seven_ge_six_nat
  exact_mod_cast h

end JSP140
