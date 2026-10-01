import JSPProblem.Singles

/-!
# `JSP-000140` — the *local* profile of an extremal colouring: `lean/JSPProblem/Star.lean`

Rounds 13–15 gave the *global* description of the extremal case
(`Rigidity.tight_attained`, `Rigidity.tight_covers`, `Rigidity.tight_pathFinset_is_STS`):
an admissible colouring of `K_n` with `6k = 5(n-1)` colours has its two-edge paths forming a
**Steiner triple system** on `V`, and **every colour class spans `V`**.

This file adds the **per-vertex** half, which is the half a *construction* of such a colouring has
to satisfy, and which no previous file records.  The centre of a block of the Steiner triple
system turns out to be forced to be a **balanced** choice:

* **`sum_nb_star`** — the star of a vertex is counted exactly once:

      ∑_i |nb c i v| = n - 1                       (for every colouring, `v` any vertex)

  the per-vertex form of the handshaking lemma `Extremal.oneB_even`; the `k` colour classes,
  restricted to the star of `v`, *partition* the `n - 1` edges at `v`;
* **`star_centred_colours`** — combined with `Rigidity.tight_covers` (in the extremal case every
  class spans `V`, so every colour has colour-degree `≥ 1` at `v`) this gives an identity for the
  number of colours in which `v` is the **centre** of a two-edge path:

      ∑_i [ v ∈ twoA c i ] = n - 1 - k             (in the extremal case);

* **`tight_star_centre`** — with `6k = 5 (n - 1)`:

      every vertex is the centre of exactly `(n - 1) / 6` two-edge paths,

  i.e. of exactly **one third** of the two-edge paths through it (there are `(n - 1)/2` of them,
  one for each pair `{v, w}` — `Rigidity.tight_pathFinset_is_STS`).  So the centre function of an
  extremal colouring is a `1/3`-balanced choice of a centre in each block of the Steiner triple
  system, and `Rigidity.tight_mod6`, `Extremal.tight_ge_thirteen` restrict the admissible orders to
  `n ≡ 1 (mod 6)`, `n ≥ 13` — so `n = 13` is the first order at which the sharp constant `5/6`
  could be attained at all;
* **`tight_star_oneB`** — consequently `v` has colour-degree `1` in exactly `2 (n - 1) / 3` colours:
  the local profile of an extremal colouring is uniform at every vertex.
-/

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

namespace JSP140

variable {n k : ℕ}

/-- The distributivity of a `Fintype` sum (the Mathlib lemma is stated for a `Finset` sum, and the
two are definitionally equal but not syntactically). -/
private lemma sum_add_fin {α : Type} [Fintype α] (f g : α → ℕ) :
    ∑ i : α, (f i + g i) = (∑ i : α, f i) + ∑ i : α, g i := by
  rw [← Finset.sum_add_distrib (M := ℕ)]

/-! ### The star of a vertex is counted once -/

/-- **THE STAR IDENTITY.**  For every vertex `v` and every colouring (admissibility is *not*
needed), the colour-degrees of `v` add up to the number of edges at `v`:

    ∑_i |nb c i v| = n - 1.

Equivalently: the `k` colour classes, restricted to the star of `v`, partition the `n - 1` edges
at `v`.  This is the per-vertex form of the handshaking lemma `Extremal.oneB_even`, and it is the
only place where the two sides of the problem (one fixed vertex, all colours) meet. -/
theorem sum_nb_star (c : Col n k) (v : Verts n) :
    (∑ i : Fin k, (nb c i v (Finset.univ : Finset (Verts n))).card) = n - 1 := by
  classical
  set U : Finset (Verts n) := Finset.univ with hU
  have hdisj : ((Finset.univ : Finset (Fin k)) : Set (Fin k)).PairwiseDisjoint
      (fun i => nb c i v U) := by
    intro i _ j _ hij
    exact Finset.disjoint_left.2 fun w hw1 hw2 => by
      have h1 := mem_nb.mp hw1
      have h2 := mem_nb.mp hw2
      exact hij (h1.2.2.symm.trans h2.2.2)
  calc (∑ i : Fin k, (nb c i v U).card)
      = ((Finset.univ : Finset (Fin k))).sum fun i => (nb c i v U).card := by rfl
    _ = ((Finset.univ : Finset (Fin k)).biUnion fun i => nb c i v U).card :=
        (Finset.card_biUnion hdisj).symm
    _ = (U.erase v).card := by
      congr 1
      ext w
      constructor
      · intro hw
        rcases Finset.mem_biUnion.mp hw with ⟨i, -, hi⟩
        exact Finset.mem_erase.mpr ⟨(mem_nb.mp hi).1, Finset.mem_univ w⟩
      · intro hw
        have hw' := Finset.mem_erase.mp hw
        exact Finset.mem_biUnion.mpr
          ⟨c s(v, w), Finset.mem_univ _, mem_nb.mpr ⟨hw'.1, hw'.2, rfl⟩⟩
    _ = n - 1 := by rw [Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_fin]

/-! ### How many colours make `v` the centre of a two-edge path -/

/-- **THE CENTRE COUNT.**  Assume every colour class spans the vertex set, i.e. `v` has
colour-degree `≥ 1` in every colour (`Rigidity.tight_covers` is the hypothesis in the extremal
case).  Then the number of colours in which `v` is the centre of a two-edge path is

    ∑_i [ v ∈ twoA c i ] = n - 1 - k.

Indeed the `n - 1` edges at `v` are split into `k` non-empty colour classes, and a class in which
`v` is a centre uses one edge more than a class in which `v` is a leaf or a single-edge endpoint. -/
theorem star_centred_colours {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n)
    (hcover : ∀ i : Fin k, ∀ v : Verts n, v ∈ twoA c i ∨ v ∈ oneB c i) (v : Verts n) :
    (∑ i : Fin k, if v ∈ twoA c i then (1 : ℕ) else 0) = n - 1 - k := by
  have hdeg : ∀ i : Fin k,
      (nb c i v (Finset.univ : Finset (Verts n))).card
        = if v ∈ twoA c i then (2 : ℕ) else 1 := by
    intro i
    by_cases h2 : (nb c i v (Finset.univ : Finset (Verts n))).card = 2
    · have : v ∈ twoA c i := Finset.mem_filter.mpr ⟨Finset.mem_univ v, h2⟩
      rw [if_pos this]; omega
    · have hne : v ∉ twoA c i := by
        intro hh; have := (Finset.mem_filter.mp hh).2; omega
      rw [if_neg hne]
      rcases hcover i v with h | h
      · exfalso; have := (Finset.mem_filter.mp h).2; omega
      · have := (Finset.mem_filter.mp h).2; omega
  have hsplit : ∀ i : Fin k,
      (if v ∈ twoA c i then (1 : ℕ) else 0) + 1 = if v ∈ twoA c i then (2 : ℕ) else 1 := by
    intro i; split <;> simp
  have hmain : n - 1 = ∑ i : Fin k, (if v ∈ twoA c i then (2 : ℕ) else 1) := by
    rw [← sum_nb_star c v]
    exact Finset.sum_congr rfl fun i _ => hdeg i
  have hone : (∑ i : Fin k, (1 : ℕ)) = k := by simp
  have h1 : (∑ i : Fin k, (if v ∈ twoA c i then (1 : ℕ) else 0))
      + (∑ i : Fin k, (1 : ℕ)) = n - 1 := by
    rw [← sum_add_fin, hmain]
    exact Finset.sum_congr rfl fun i _ => hsplit i
  omega

/-- **THE LOCAL PROFILE OF AN EXTREMAL COLOURING.**  If an admissible colouring of `K_n` attains
the counting bound `6k = 5 (n - 1)`, then **every vertex is the centre of exactly `(n - 1) / 6`
two-edge paths** — one third of the two-edge paths through it.

Together with `Rigidity.tight_pathFinset_is_STS` (the two-edge paths form a Steiner triple system,
so exactly `(n - 1)/2` of them pass through `v`) and `Rigidity.tight_mod6` (`n ≡ 1 (mod 6)`), this
says: *an extremal colouring of `K_n` is a Steiner triple system with a centre in each block such
that every vertex is the centre of exactly one third of its blocks.*  `Extremal.tight_ge_thirteen`
rules out `n < 13`, so `n = 13` is the first order at which the sharp constant `5/6` can be
attained at all. -/
theorem tight_star_centre {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n)
    (h3 : 3 * Paths c = (edgeFinset (Finset.univ : Finset (Verts n))).card)
    (hk : 6 * k = 5 * (n - 1)) (v : Verts n) :
    6 * (∑ i : Fin k, if v ∈ twoA c i then (1 : ℕ) else 0) = n - 1 := by
  have h := star_centred_colours hc hn (fun i w => tight_covers hc hn h3 hk i w) v
  omega

/-- **In an extremal colouring `v` has colour-degree `1` in exactly `2 (n - 1) / 3` colours.**  So
the local profile of an extremal colouring is *uniform*: every vertex is a two-edge-path centre in
`(n - 1)/6` colours and has colour-degree `1` in `2 (n - 1)/3` colours. -/
theorem tight_star_oneB {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n)
    (h3 : 3 * Paths c = (edgeFinset (Finset.univ : Finset (Verts n))).card)
    (hk : 6 * k = 5 * (n - 1)) (v : Verts n) :
    3 * (∑ i : Fin k, if v ∈ oneB c i then (1 : ℕ) else 0) = 2 * (n - 1) := by
  have hA := tight_star_centre hc hn h3 hk v
  have hd : ∀ i : Fin k,
      (if v ∈ twoA c i then (1 : ℕ) else 0) + (if v ∈ oneB c i then (1 : ℕ) else 0) = 1 := by
    intro i
    rcases tight_covers hc hn h3 hk i v with h | h
    · have hn2 : v ∉ oneB c i := by
        intro hc'
        have := (Finset.mem_filter.mp hc').2
        have := (Finset.mem_filter.mp h).2
        omega
      rw [if_pos h, if_neg hn2, add_zero]
    · have hn2 : v ∉ twoA c i := by
        intro hc'
        have := (Finset.mem_filter.mp hc').2
        have := (Finset.mem_filter.mp h).2
        omega
      rw [if_neg hn2, if_pos h, zero_add]
  have hone : (∑ i : Fin k, (1 : ℕ)) = k := by simp
  have hsum : (∑ i : Fin k, if v ∈ twoA c i then (1 : ℕ) else 0)
      + (∑ i : Fin k, if v ∈ oneB c i then (1 : ℕ) else 0) = k := by
    have h1 : ∑ i : Fin k, ((if v ∈ twoA c i then (1 : ℕ) else 0)
        + (if v ∈ oneB c i then (1 : ℕ) else 0)) = ∑ i : Fin k, (1 : ℕ) :=
      Finset.sum_congr rfl fun i _ => hd i
    rw [← sum_add_fin, h1, hone]
  have hB : (∑ i : Fin k, if v ∈ oneB c i then (1 : ℕ) else 0)
      = k - (∑ i : Fin k, if v ∈ twoA c i then (1 : ℕ) else 0) := by omega
  omega

/-- **The whole local profile in one statement.**  In an extremal admissible colouring of `K_n`,
every vertex `v` is the centre of exactly `(n - 1)/6` two-edge paths and has colour-degree `1` in
exactly `2 (n - 1)/3` colours — the third possibility, colour-degree `0`, never occurs
(`Rigidity.tight_covers`). -/
theorem tight_star_profile {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n)
    (h3 : 3 * Paths c = (edgeFinset (Finset.univ : Finset (Verts n))).card)
    (hk : 6 * k = 5 * (n - 1)) (v : Verts n) :
    6 * (∑ i : Fin k, if v ∈ twoA c i then (1 : ℕ) else 0) = n - 1 ∧
      3 * (∑ i : Fin k, if v ∈ oneB c i then (1 : ℕ) else 0) = 2 * (n - 1) :=
  ⟨tight_star_centre hc hn h3 hk v, tight_star_oneB hc hn h3 hk v⟩

/-! ### How many blocks of the extremal Steiner triple system pass through a vertex -/

/-- **EVERY VERTEX LIES IN EXACTLY `(n-1)/2` BLOCKS OF THE EXTREMAL STEINER TRIPLE SYSTEM.**  This
is the per-vertex form of `Rigidity.sum_card_filter_pairIn`: for each of the `n - 1` pairs `{v, w}`
at `v` there is exactly one block containing it (`Rigidity.tight_pathFinset_is_STS`), and each block
through `v` accounts for exactly two of those pairs.  Since `tight_star_centre` says that `v` is the
*centre* of `(n-1)/6` of them, the centre function of the extremal structure is a `1/3`-balanced
choice **at every point**: of the `(n-1)/2` blocks through `v`, one third are centred at `v` and two
thirds have `v` as a leaf.  This is the specification a construction of the extremal family has to
meet. -/
theorem tight_blocks_through {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n)
    (h3 : 3 * Paths c = (edgeFinset (Finset.univ : Finset (Verts n))).card)
    (v : Verts n) :
    ((pathFinset c).filter (fun b => v ∈ b)).card * 2 = n - 1 := by
  classical
  set B : Finset (Finset (Verts n)) := pathFinset c with hBc
  set U : Finset (Verts n) := Finset.univ with hUc
  have hB : IsSTS B := tight_pathFinset_is_STS hc hn h3
  -- for each partner `w` of `v` there is exactly one block through both
  have hone : ∀ w ∈ U.erase v, ((B.filter (fun b => v ∈ b ∧ w ∈ b)).card) = 1 := by
    intro w hw
    have hwv : w ≠ v := (Finset.mem_erase.mp hw).1
    have hmem : s(v, w) ∈ edgeFinset U :=
      mem_edgeFinset_mk (Finset.mem_univ v) (Finset.mem_univ w) hwv.symm
    obtain ⟨b₀, hb₀, huniq⟩ := hB.2 (s(v, w)) hmem
    have hb₀mem : v ∈ b₀ ∧ w ∈ b₀ := mem_pairIn.mp hb₀.2
    have hset : B.filter (fun b => v ∈ b ∧ w ∈ b) = {b₀} := by
      ext b
      constructor
      · intro hb
        have hbm : b ∈ B ∧ (v ∈ b ∧ w ∈ b) := Finset.mem_filter.mp hb
        rw [Finset.mem_singleton]
        exact huniq b ⟨hbm.1, mem_pairIn.mpr hbm.2⟩
      · intro hb
        rw [Finset.mem_singleton] at hb
        subst hb
        exact Finset.mem_filter.mpr ⟨hb₀.1, hb₀mem⟩
    rw [hset]
    simp
  -- the double count: pairs at `v` against blocks through `v`
  have hstep : ∀ b : Finset (Verts n),
      (∑ w ∈ (U.erase v).filter (fun w => w ∈ b), (1 : ℕ))
        = ∑ w ∈ U.erase v, (if w ∈ b then (1 : ℕ) else 0) := by
    intro b
    exact (Finset.sum_filter (s := U.erase v) (p := fun w => w ∈ b)
      (f := fun _ => (1 : ℕ)))
  have hset : ∀ b : Finset (Verts n), (b ⊆ U) → v ∈ b →
      (U.erase v).filter (fun w => w ∈ b) = b.erase v := by
    intro b hsub hvb
    ext w
    simp only [Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro ⟨⟨hne, hU⟩, hbin⟩
      exact ⟨hne, hbin⟩
    · rintro ⟨hne, hbin⟩
      exact ⟨⟨hne, hsub hbin⟩, hbin⟩
  have hinter : ∀ b : Finset (Verts n), (b ⊆ U) → v ∈ b →
      (∑ w ∈ U.erase v, (if w ∈ b then (1 : ℕ) else 0)) = (b.erase v).card := by
    intro b hsub hvb
    rw [← hstep b, (Finset.card_eq_sum_ones _).symm, hset b hsub hvb]
  have hinner : ∀ b ∈ B, (∑ w ∈ U.erase v, (if v ∈ b ∧ w ∈ b then (1 : ℕ) else 0))
      = if v ∈ b then (2 : ℕ) else 0 := by
    intro b hb
    have hb3 : b.card = 3 := card_pathFinset_mem hb
    by_cases hvb : v ∈ b
    · have hconv : (∑ w ∈ U.erase v, (if v ∈ b ∧ w ∈ b then (1 : ℕ) else 0))
          = ∑ w ∈ U.erase v, (if w ∈ b then (1 : ℕ) else 0) :=
        Finset.sum_congr rfl fun w hw => by
          by_cases hwb : w ∈ b <;> simp [hwb, hvb]
      rw [if_pos hvb, hconv, hinter b (Finset.subset_univ b) hvb,
        Finset.card_erase_of_mem hvb, hb3]
    · rw [if_neg hvb]
      refine Finset.sum_eq_zero fun w _ => ?_
      simp [hvb]
  have hleft : (∑ w ∈ U.erase v, ((B.filter (fun b => v ∈ b ∧ w ∈ b)).card)) = n - 1 := by
    calc (∑ w ∈ U.erase v, ((B.filter (fun b => v ∈ b ∧ w ∈ b)).card))
        = ∑ w ∈ U.erase v, (1 : ℕ) := Finset.sum_congr rfl fun w hw => hone w hw
      _ = (U.erase v).card := (Finset.card_eq_sum_ones _).symm
      _ = n - 1 := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_fin]
  have hmid : (∑ w ∈ U.erase v, ((B.filter (fun b => v ∈ b ∧ w ∈ b)).card))
      = ∑ b ∈ B, (if v ∈ b then (2 : ℕ) else 0) := by
    calc (∑ w ∈ U.erase v, ((B.filter (fun b => v ∈ b ∧ w ∈ b)).card))
        = ∑ w ∈ U.erase v, ∑ b ∈ B, if v ∈ b ∧ w ∈ b then (1 : ℕ) else 0 := by
          refine Finset.sum_congr rfl fun w hw => ?_
          rw [Finset.card_eq_sum_ones, Finset.sum_filter]
      _ = ∑ b ∈ B, ∑ w ∈ U.erase v, (if v ∈ b ∧ w ∈ b then (1 : ℕ) else 0) := Finset.sum_comm
      _ = ∑ b ∈ B, (if v ∈ b then (2 : ℕ) else 0) :=
          Finset.sum_congr rfl fun b hb => hinner b hb
  have hlast : ∑ b ∈ B, (if v ∈ b then (2 : ℕ) else 0)
      = (B.filter (fun b => v ∈ b)).card * 2 := by
    calc (∑ b ∈ B, (if v ∈ b then (2 : ℕ) else 0))
        = ∑ b ∈ B.filter (fun b => v ∈ b), (2 : ℕ) :=
          (Finset.sum_filter (s := B) (p := fun b => v ∈ b) (f := fun _ => (2 : ℕ))).symm
      _ = (B.filter (fun b => v ∈ b)).card • (2 : ℕ) := Finset.sum_const _
      _ = (B.filter (fun b => v ∈ b)).card * 2 := by rw [nsmul_eq_mul]; rfl
  exact (hmid.trans hlast).symm.trans hleft

end JSP140
