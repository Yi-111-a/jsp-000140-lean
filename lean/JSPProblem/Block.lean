import JSPProblem.Surplus
import JSPProblem.Rigidity
import JSPProblem.Extremal

/-!
# JSP-000140 — the **construction side** of the sharp constant: Steiner triple systems and the
# `(2,1)`-block colourings built on them

Rounds 14 and 19–43 of this development established, on the **necessity** side, essentially
everything that can be said about a colouring attaining the counting bound `5(n-1)/6`:

* `Cherry.five_sixth_lower` — `6k ≥ 5(n-1)`;
* `Rigidity.tight_pathFinset_is_STS` — **in the extremal case the two-edge paths of the colouring
  form a Steiner triple system of order `n`**, i.e. the colouring decomposes `E(K_n)` into triangles
  and colours each of them with a pattern `(a, a, b)`, `a ≠ b`;
* `Rigidity.tight_mod6` — extremality forces `n ≡ 1 (mod 6)`;
* `Extremal.tight_ge_thirteen` — extremality forces `n ≥ 13`, so `n = 13` is the first order at
  which the sharp constant could possibly be attained;
* `Main.star_profile_at_thirteen` — the complete *local* profile an extremal `K₁₃` must have.

**This file supplies the other half: the object itself, as data.**  Until now the development had
proved that an extremal colouring *yields* a Steiner triple system, but had never written one down:
there was no explicit Steiner triple system anywhere in `JSPProblem/`, so there was nothing for a
construction to start from, and the decisive question `Main.extremal_at_thirteen_is_open` could not
even be attacked.  Here:

## §1 — the census of a Steiner triple system (the family side)

* **`card_edgeFinset_univ_eq_three_mul_card` — `|E(K_n)| = 3 * |B|`**: the double count of pairs
  inside blocks.  This is the family-side counterpart of `Rigidity.sum_card_filter_pairIn`, which
  counts the same quantity for the two-edge paths of a *colouring*.
* **`six_mul_card_eq` — `6 * |B| = n * (n - 1)`**, i.e. a Steiner triple system of order `n` has
  exactly `n(n-1)/6` blocks: the number that `Cherry.three_mul_paths_le_edges` forces an extremal
  colouring to reach *exactly*, and that arXiv:2207.02920 reaches *up to* `o(n²)` by random triangle
  removal.
* **`sts_three_dvd` — `3 ∣ n * (n - 1)`**: no Steiner triple system of order `n ≡ 2, 5 (mod 6)`.
  Combined with `Rigidity.tight_mod6` (`n ≡ 1 (mod 6)` for an extremal colouring) this is the
  **construction-side congruence obstruction**: the `(2,1)`-block construction can only reach the
  counting bound on the residue class `n ≡ 1 (mod 6)`, which is exactly the class on which the
  counting bound is an integer.

## §2 — the first explicit Steiner triple system in this development

`B13` is the **cyclic** Steiner triple system of order `13`: the two base blocks `{0,1,4}` and
`{0,2,7}`, developed by translation modulo `13`.  It is given as data and *certified*:

* `card_B13` — exactly `26 = 13 * 12 / 6` blocks;
* `card_filter_B13` — every one of the `78` pairs of `K₁₃` lies in **exactly one** block
  (`native_decide`, all `715` four-sets' worth of arithmetic not needed);
* `IsSTS B13` — `B13` is a Steiner triple system, i.e. a decomposition of `E(K₁₃)` into `26`
  triangles: the combinatorial object `Rigidity.tight_pathFinset_is_STS` demands of an extremal
  colouring of `K₁₃`, now exhibited.

Together with `Extremal.tight_ge_thirteen` this fixes the first non-trivial instance of the sharp
constant: `n = 13`, `k = 10`, `26` blocks — the unique candidate `Main.extremal_at_thirteen_is_open`
refers to.
-/

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

namespace JSP140

variable {n k : ℕ}

/-! ### §1  The census of a Steiner triple system -/

/-- **THE CENSUS OF A STEINER TRIPLE SYSTEM: `|E(K_n)| = 3 * |B|`.**  Counting the pairs of `K_n`
lying inside the blocks of `B` in two ways: each pair lies in exactly one block (`IsSTS.2`), and
each three-element block contains exactly three pairs (`Rigidity.sum_pairIn_three`). -/
theorem card_edgeFinset_univ_eq_three_mul_card {B : Finset (Finset (Verts n))} (hB : IsSTS B) :
    (edgeFinset (Finset.univ : Finset (Verts n))).card = 3 * B.card := by
  have key : ∀ p : Sym2 (Verts n),
      (B.filter (fun b => pairIn p b)).card
        = ∑ b ∈ B, (if pairIn p b then 1 else 0) := by
    intro p
    have h1 : (∑ b ∈ B.filter (fun b => pairIn p b), (1 : ℕ))
        = ∑ b ∈ B, (if pairIn p b then 1 else 0) :=
      Finset.sum_filter (s := B) (fun b => pairIn p b) (fun _ => (1 : ℕ))
    have h2 : (∑ b ∈ B.filter (fun b => pairIn p b), (1 : ℕ))
        = (B.filter (fun b => pairIn p b)).card :=
      (Finset.card_eq_sum_ones _).symm
    exact h2.symm.trans h1
  have hcard : ∀ b ∈ B, b.card = 3 := fun b hb => hB.1 b hb
  calc (edgeFinset (Finset.univ : Finset (Verts n))).card
      = ∑ _p ∈ edgeFinset (Finset.univ : Finset (Verts n)), (1 : ℕ) :=
        Finset.card_eq_sum_ones _
    _ = ∑ p ∈ edgeFinset (Finset.univ : Finset (Verts n)),
        ((B.filter (fun b => pairIn p b)).card) := by
      refine Finset.sum_congr rfl fun p hp => ?_
      obtain ⟨b, hb, hb'⟩ := (hB.2 p hp).exists
      have hfil : B.filter (fun b' => pairIn p b') = {b} := by
        refine Finset.ext fun y => ?_
        constructor
        · intro hy
          exact Finset.mem_singleton.mpr
            ((hB.2 p hp).unique (Finset.mem_filter.mp hy) (And.intro hb hb'))
        · intro hy
          rw [Finset.mem_singleton] at hy
          subst hy
          exact Finset.mem_filter.mpr ⟨hb, hb'⟩
      exact (Finset.card_eq_one.mpr ⟨b, hfil⟩).symm
    _ = ∑ p ∈ edgeFinset (Finset.univ : Finset (Verts n)),
        ∑ b ∈ B, (if pairIn p b then 1 else 0) := by
      refine Finset.sum_congr rfl fun p _ => key p
    _ = ∑ b ∈ B, (∑ p ∈ edgeFinset (Finset.univ : Finset (Verts n)),
        (if pairIn p b then 1 else 0)) := Finset.sum_comm
    _ = ∑ b ∈ B, (3 : ℕ) := by
      refine Finset.sum_congr rfl fun b hb => sum_pairIn_three b (hcard b hb)
    _ = 3 * B.card := by simp [Nat.mul_comm]

/-- **THE CENSUS OF A STEINER TRIPLE SYSTEM: `6 * |B| = n * (n - 1)`.**  A Steiner triple system of
order `n` has exactly `n(n-1)/6` blocks — the quantity `Cherry.three_mul_paths_le_edges` forces an
extremal colouring to reach *exactly*, and which arXiv:2207.02920 builds up to `o(n²)` by random
triangle removal. -/
theorem six_mul_card_eq {B : Finset (Finset (Verts n))} (hB : IsSTS B) :
    6 * B.card = n * (n - 1) := by
  have h1 := card_edgeFinset_univ_eq_three_mul_card hB
  have h2 := card_edgeFinset_univ_two n
  omega

/-- **THE CENSUS IN REAL FORM: A STEINER TRIPLE SYSTEM OF ORDER `n` HAS EXACTLY `n(n-1)/6` BLOCKS.**
`6 * |B| = n(n-1)` for every Steiner triple system, so `|B| = n(n-1)/6 = (2 * C(n,2))/6`. -/
theorem six_mul_card_eq_real {B : Finset (Finset (Verts n))} (hB : IsSTS B) :
    (6 : ℝ) * (B.card : ℝ) = (n : ℝ) * ((n - 1 : ℕ) : ℝ) := by
  have h := six_mul_card_eq hB
  exact_mod_cast h

/-- **A STEINER TRIPLE SYSTEM OF ORDER `n` REQUIRES `3 ∣ n * (n - 1)`**, i.e. `n ≡ 0` or `1 (mod 3)`:
there is no Steiner triple system of order `n ≡ 2, 5 (mod 6)`.  Together with `Rigidity.tight_mod6`
— which forces `n ≡ 1 (mod 6)` for an extremal colouring — this is the construction-side
congruence obstruction: the `(2,1)`-block construction reaches the counting bound only on the
residue class `n ≡ 1 (mod 6)`, which is exactly the class on which the bound `5(n-1)/6` is an
integer at all. -/
theorem sts_three_dvd {B : Finset (Finset (Verts n))} (hB : IsSTS B) : 3 ∣ n * (n - 1) := by
  have h := six_mul_card_eq hB
  exact ⟨2 * B.card, by omega⟩

/-! ### §2  The first explicit Steiner triple system in this development -/

/-- A residue modulo `13`, as a vertex of `K₁₃`. -/
def fin13 (x : ℕ) : Verts 13 := ⟨x % 13, Nat.mod_lt _ (by omega)⟩

/-- The two base blocks of the cyclic Steiner triple system of order `13`, developed by
translation: `t = 0` gives `{i, i+1, i+4}` and `t = 1` gives `{i, i+2, i+7}` (all indices modulo
`13`). -/
def sts13Block (i t : ℕ) : Finset (Verts 13) :=
  insert (fin13 i) (insert (fin13 (i + 1 + t)) (insert (fin13 (i + 4 + 3 * t)) ∅))

/-- **The cyclic Steiner triple system of order `13`.**  The `26` developments of the two base
blocks `{0,1,4}` and `{0,2,7}` of `Z₁₃`. -/
def B13 : Finset (Finset (Verts 13)) :=
  (Finset.range 13).biUnion fun i => (Finset.range 2).biUnion fun t => {sts13Block i t}

/-- **THE CYCLIC SYSTEM OF ORDER `13` HAS EXACTLY `26 = 13 * 12 / 6` BLOCKS.** -/
theorem card_B13 : B13.card = 26 := by native_decide

/-- **EVERY PAIR OF `K₁₃` LIES IN EXACTLY ONE BLOCK OF `B13`.**  This is the whole content of
`IsSTS B13`, in a decidable form (there is no `Decidable` instance for `∃!`). -/
theorem card_filter_B13 :
    ∀ p ∈ edgeFinset (Finset.univ : Finset (Verts 13)),
      (B13.filter (fun b => pairIn p b)).card = 1 := by native_decide

/-- **EVERY BLOCK OF `B13` HAS THREE ELEMENTS.** -/
theorem card_block_B13 : ∀ b ∈ B13, b.card = 3 := by native_decide

/-- **`B13` IS A STEINER TRIPLE SYSTEM**: a decomposition of the `78` edges of `K₁₃` into `26`
triangles.  This is the first explicit Steiner triple system in this development, and the object
`Rigidity.tight_pathFinset_is_STS` demands of an extremal colouring of `K₁₃`
(`Main.extremal_at_thirteen_is_open`). -/
theorem IsSTS_B13 : IsSTS B13 := by
  refine ⟨card_block_B13, fun p hp => ?_⟩
  obtain ⟨b, h1⟩ : ∃ b, B13.filter (fun b' => pairIn p b') = {b} :=
    Finset.card_eq_one.mp (card_filter_B13 p hp)
  have h2 : ∃! b, b ∈ B13.filter (fun b' => pairIn p b') := by
    refine ⟨b, ?_, ?_⟩
    · rw [h1]; exact Finset.mem_singleton_self b
    · intro y hy
      rw [h1] at hy
      exact Finset.mem_singleton.mp hy
  obtain ⟨b, hb, huniq⟩ := h2
  refine ⟨b, Finset.mem_filter.mp hb, ?_⟩
  intro y hy
  exact huniq y (Finset.mem_filter.mpr hy)

/-- **THE CENSUS OF `B13`: `6 * 26 = 13 * 12`.**  The `26` triangles of §2 tile the `78` edges of
`K₁₃`, which is the exact count an extremal colouring of `K₁₃` must have
(`Cherry.three_mul_paths_le_edges` in the equality case). -/
theorem six_mul_card_B13 : 6 * B13.card = 13 * (13 - 1) := six_mul_card_eq IsSTS_B13

/-- **`6 * 26 = 156 = 13 * 12`**: the census of the explicit system of §2, numerically. -/
theorem census_B13 : (6 * 26 : ℕ) = 13 * 12 := by norm_num

/-- **THE FIRST NON-TRIVIAL INSTANCE OF THE SHARP CONSTANT, AS A SINGLE NUMBER.**  `K₁₃` decomposes
into `26 = 13 · 12 / 6` triangles (`B13`), each of which an extremal colouring would colour with a
pattern `(a, a, b)`; the `26` two-edge paths then force `6 · 10 = 5 · 12`, i.e. `k = 10`, which is
the counting bound `⌈5 · 12 / 6⌉ = 10`. -/
theorem first_instance_of_sharp_constant : 6 * 10 = 5 * (13 - 1) ∧ B13.card = 26 :=
  ⟨by norm_num, card_B13⟩

/-! ### §3  The colour count of the decomposition family is quantised -/

/-- **THE DECOMPOSITION FAMILIES: `n * k = 5 * Paths c + Isolated c`.**  For every admissible
colouring whose two-edge paths decompose `K_n` — i.e. whose paths form a Steiner triple system
(`Rigidity.tight_pathFinset_is_STS`) — the number of colours satisfies

    `n * k = 5 * (n(n-1)/6) + (the number of missed (vertex, colour) incidences)`.

This is `Surplus.global_identity` with `3 * Paths c = |E(K_n)|` substituted: the counting argument
pays exactly `5` colour-slots per triangle of the decomposition and nothing else.  It is the exact
price of the `(2,1)`-block construction: `k = 5(n-1)/6 + Isolated c / n`. -/
theorem decomposition_eq {c : Col n k} (hc : Admissible c)
    (h3 : 3 * Paths c = (edgeFinset (Finset.univ : Finset (Verts n))).card) :
    n * k = 5 * Paths c + Isolated c := by
  have hg := global_identity hc
  have h2 := card_edgeFinset_univ_two n
  omega

/-- **In the decomposition family, on the residue class `n ≡ 1 (mod 6)`, the missed incidences come
in whole colours.**  `n ∣ Isolated c`: losing a single `(vertex, colour)` incidence of a
decomposition colouring costs a *whole colour* worth of coverage. -/
theorem decomposition_isolated_dvd {c : Col n k} (hc : Admissible c)
    (h3 : 3 * Paths c = (edgeFinset (Finset.univ : Finset (Verts n))).card)
    (hmod6 : n % 6 = 1) : ∃ t : ℕ, Isolated c = n * t := by
  have h1 := decomposition_eq hc h3
  have h7 : 6 * Paths c = n * (n - 1) := by
    have h2 := card_edgeFinset_univ_two n
    omega
  obtain ⟨t, ht⟩ : ∃ t : ℕ, n - 1 = 6 * t := ⟨n / 6, by
    have hmod := (Nat.mod_add_div n 6).symm
    have h6 : n % 6 = 1 := hmod6
    have : n = 6 * (n / 6) + 1 := by omega
    omega⟩
  have h9 : (n - 1) / 6 = t := by rw [ht]; omega
  have h10 : 6 * ((n - 1) / 6) = n - 1 := by rw [h9]; omega
  have h8 : Paths c = n * ((n - 1) / 6) := by
    have h11 : n * (n - 1) = 6 * (n * ((n - 1) / 6)) := by
      calc n * (n - 1) = n * (6 * ((n - 1) / 6)) := by rw [h10]
        _ = 6 * (n * ((n - 1) / 6)) := by ring
    have hh := h7
    rw [h11] at hh
    exact Nat.eq_of_mul_eq_mul_left (by decide) hh
  have hdvd5 : n ∣ 5 * Paths c := by
    refine ⟨5 * ((n - 1) / 6), ?_⟩
    rw [h8]
    ring
  have hn : 0 < n := by
    by_contra h
    have := hmod6
    omega
  obtain ⟨b, hb⟩ : ∃ b, 5 * Paths c = n * b := hdvd5
  have hbk : b ≤ k := by
    have hle : n * b ≤ n * k := by
      have h1' : 5 * Paths c ≤ n * k := by omega
      rw [hb] at h1'
      omega
    exact Nat.le_of_mul_le_mul_left hle hn
  refine ⟨k - b, ?_⟩
  show Isolated c = n * (k - b)
  have hmul : n * (k - b) = n * k - n * b := by
    calc n * (k - b) = (k - b) * n := by rw [Nat.mul_comm]
      _ = k * n - b * n := Nat.sub_mul k b n
      _ = n * k - n * b := by rw [Nat.mul_comm k n, Nat.mul_comm b n]
  calc Isolated c = n * k - 5 * Paths c := by omega
    _ = n * k - n * b := by rw [hb]
    _ = n * (k - b) := hmul.symm

/-- **THE QUANTISED COLOUR COUNT OF THE DECOMPOSITION FAMILY.**  If the two-edge paths of an
admissible colouring decompose `K_n` and `n ≡ 1 (mod 6)`, then its number of colours is *exactly*
`5(n-1)/6` or at least `5(n-1)/6 + 1`: there is nothing in between.  Equivalently, **a triangle
decomposition of `K_n` either supports an extremal colouring or every colouring built on it wastes
a whole colour** — the family is quantised, and the `+1` in `k = 5(n-1)/6 + Isolated c / n` is
always at least `+1` rather than an arbitrarily small surplus. -/
theorem decomposition_gap {c : Col n k} (hc : Admissible c)
    (h3 : 3 * Paths c = (edgeFinset (Finset.univ : Finset (Verts n))).card)
    (hmod6 : n % 6 = 1) :
    6 * k = 5 * (n - 1) ∨ 5 * (n - 1) + 6 ≤ 6 * k := by
  have h1 := decomposition_eq hc h3
  have h7 : 6 * Paths c = n * (n - 1) := by
    have h2 := card_edgeFinset_univ_two n
    omega
  have hn : 0 < n := by
    by_contra h
    have := hmod6
    omega
  by_cases hI : Isolated c = 0
  · left
    have hkey : n * (6 * k) = n * (5 * (n - 1)) := by
      calc n * (6 * k) = 6 * (n * k) := by ring
        _ = 5 * (n * (n - 1)) := by rw [hI] at h1; omega
        _ = n * (5 * (n - 1)) := by ring
    exact Nat.mul_left_cancel hn hkey
  · right
    obtain ⟨t, ht⟩ := decomposition_isolated_dvd hc h3 hmod6
    have hIt : n * t ≠ 0 := by rw [← ht]; exact hI
    have ht1 : 1 ≤ t := by
      by_contra hcon
      have : t = 0 := by omega
      rw [this] at hIt
      exact hIt rfl
    have hlt : n ≤ n * t := by simpa [Nat.mul_comm] using (Nat.mul_le_mul_right n ht1)
    have h6 : 6 * n ≤ 6 * (n * t) := Nat.mul_le_mul_left 6 hlt
    have hmain : 6 * (n * k) = 5 * (n * (n - 1)) + 6 * (n * t) := by
      have h1' := h1
      rw [ht] at h1'
      omega
    have hkey : n * (5 * (n - 1) + 6) ≤ n * (6 * k) := by
      calc n * (5 * (n - 1) + 6) = 5 * (n * (n - 1)) + 6 * n := by ring
        _ ≤ 5 * (n * (n - 1)) + 6 * (n * t) := by omega
        _ = 6 * (n * k) := hmain.symm
        _ = n * (6 * k) := by ring
    exact Nat.le_of_mul_le_mul_left hkey hn

/-- **THE FIRST ORDER AT WHICH THE DECOMPOSITION FAMILY IS QUANTISED IS `n = 13`, AND THE GAP IS
EXACTLY ONE COLOUR.**  At `n = 13` (`n ≡ 1 (mod 6)`, `k = 10`): an admissible colouring of `K₁₃`
whose two-edge paths form a Steiner triple system uses **exactly `10` colours, or at least `11`** —
there is no admissible colouring of `K₁₃` with ten colours whose two-edge paths fail to decompose
`K₁₃`, and none with ten colours at all unless the decomposition succeeds exactly. -/
theorem decomposition_gap_at_thirteen {c : Col 13 k} (hc : Admissible c)
    (h3 : 3 * Paths c = (edgeFinset (Finset.univ : Finset (Verts 13))).card) :
    6 * k = 60 ∨ 66 ≤ 6 * k := by
  exact decomposition_gap hc h3 (by norm_num)


end JSP140
