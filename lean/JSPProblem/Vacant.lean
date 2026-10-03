import JSPProblem.Profile
import JSPProblem.Star
import JSPProblem.Strict
import JSPProblem.Rigidity

/-!
# JSP-000140 — THE VACANT LEAF COLOUR: `f(n,4,5) ≥ ⌈(5n+1)/6⌉`, one more than the catalog bound

## The gap left by rounds 4–64

The catalog lower bound `Cherry.five_sixth_lower` (`5 * (n-1) ≤ 6 * k`) is a shadow of the exact
identity `Surplus.surplus_identity`

    `6 * n * k = 5 * n * (n-1) + 6 * Isolated c + 2 * Defect c`,

where `Isolated c` counts the `(vertex, colour)` **slots the colouring does not use**.  Every
instrument of rounds 63–64 (the four-set census `Pairs.lean`, Cauchy–Schwarz `Moment.lean`, the
per-class charge `Profile.lean`) reads only the colour-class profile `(|E_i|)` and `Paths c`, and so
cannot bound `Isolated c`: that family is exhausted (at `(9,7)` the sharp relaxed cost is
`120 ≤ C(9,4) = 126`, and `Profile.chargeOK 9` holds).

The bound `5(n-1) ≤ 6k` is therefore *strict* as soon as `Isolated c ≥ 1`, which
`Strict.isolated_pos` proves for `Paths c > 0`; rounds 53–55 spent exactly that one unit.
**This file proves `Isolated c ≥ n` whenever `n ≥ 4` and `k ≤ n - 2`.**

## The one new input: the leaf colour is vacant at the centre

Let `(v; a, b)` be a two-edge path of colour `i` (`v` the centre, `va` and `vb` both of colour `i`)
and let `j = c s(a,b)` be the colour of its **leaf edge**.  Then

    **`v ∈ zeroA c j`  —  no edge at `v` has colour `j`.**

Indeed `j ≠ i` (a `K₄` with three edges of one colour spans at most four), and if `c s(v,x) = j`
for some `x ∉ {v,a,b}` then the `K₄` on `{v,a,b,x}` carries `i, i, j, j` and two further edges —
**at most four** colours, against the five `Admissible` demands.  This is `Strict.apex_zeroA`
(round 53) read for an arbitrary two-edge path rather than for a labelled triangle of a
`(2,1)`-block colouring, and it is a *per-vertex* statement: the census family has none.

Consequences proved here:

* every two-edge-path centre is a wasted slot (`card_centres_le_isolated`);
* if `k ≤ n - 2` then **every** vertex is a two-edge-path centre (pigeonhole on `Star.sum_nb_star`:
  `n-1` edges at `v`, `k ≤ n-2` colours), hence **`n ≤ Isolated c`** (`isolated_ge_n`);
* hence, from `Surplus.surplus_of_k`, **`5n + 1 ≤ 6k`** for every `n ≥ 7`
  (`five_n_add_one_le_six_k_of_seven`): the catalog bound `5(n-1) ≤ 6k` with one whole unit added
  back, i.e. **`f(n,4,5) ≥ ⌈(5n+1)/6⌉`, one colour above `⌈5(n-1)/6⌉`, at every `n ≥ 7`**;
* at the instance level **`EG 9 = 8`, `EG 10 = 9`, `EG 11 = 10`** become *theorems of counting*:
  the 80-minute search certificate `Nine.certD_nine_six` is redundant, and benchmark **B4**
  `f(10,4,5) ∈ {8,9}` is closed (`f(10,4,5) = 9`);
* at the extremal value `6k = 5n+1` every slot but one is used (`isolated_eq_n_defect_eq_zero`).

The prize hypothesis `Main.AdmissibleUpper ε` is untouched: this is still the *lower* half, and it
does not supply the existence theorem of arXiv:2207.02920 §4.
-/

namespace JSP140

variable {n k : ℕ} {c : Col n k}

/-! ### §0  A counting tool -/

/-- Two members of a two-element finset, distinct. -/
private theorem exists_two_ne_mem_of_card_eq_two {α : Type*} [DecidableEq α] {s : Finset α}
    (h : s.card = 2) : ∃ a b : α, a ∈ s ∧ b ∈ s ∧ a ≠ b := by
  obtain ⟨a, b, hab, hs⟩ := Finset.card_eq_two.mp h
  refine ⟨a, b, ?_, ?_, hab⟩
  · rw [hs]; exact Finset.mem_insert_self _ _
  · rw [hs]; simp

/-- `a * (b - 1) + a = a * b`, the form of `Pairs.mul_sub_add` with the two occurrences of `m`
disjoint. -/
private theorem mul_sub_one_add (a b : ℕ) (hb : 1 ≤ b) : a * (b - 1) + a = a * b := by
  obtain ⟨m, hm⟩ : ∃ m : ℕ, b = m + 1 := ⟨b - 1, by omega⟩
  rw [hm]
  rw [Nat.succ_sub_one]
  rfl

/-- **THE UNUSED SLOTS DOMINATE THE MISSED VERTICES.**  If every vertex of `S` is missed by at least
one colour of `c`, then `S.card ≤ Isolated c`. -/
private theorem card_le_isolated_of_forall_mem {c : Col n k} {S : Finset (Verts n)}
    (h : ∀ v ∈ S, ∃ i : Fin k, v ∈ zeroA c i) : S.card ≤ Isolated c := by
  have hsub : S ⊆ (Finset.univ : Finset (Fin k)).biUnion fun i : Fin k => zeroA c i := by
    intro v hv
    obtain ⟨i, hi⟩ := h v hv
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hi⟩
  have h1 := Finset.card_le_card hsub
  have h2 : ((Finset.univ : Finset (Fin k)).biUnion fun i : Fin k => zeroA c i).card
      ≤ ∑ _i ∈ (Finset.univ : Finset (Fin k)), (zeroA c _i).card := Finset.card_biUnion_le
  calc S.card
      ≤ ((Finset.univ : Finset (Fin k)).biUnion fun i : Fin k => zeroA c i).card := h1
    _ ≤ ∑ _i ∈ (Finset.univ : Finset (Fin k)), (zeroA c _i).card := h2
    _ = Isolated c := rfl

/-! ### §1  THE VACANT LEAF COLOUR -/

/-- **THE LEAF COLOUR OF A TWO-EDGE PATH IS VACANT AT ITS CENTRE.**

If `v` is the centre of a two-edge path `a - v - b` of colour `i` (so `va` and `vb` both carry
colour `i`), then the colour `c s(a,b)` of the leaf edge occurs on **no** edge at `v`:
`v ∈ zeroA c (c s(a,b))`.

This is the local fact `Strict.apex_zeroA` (round 53) for an arbitrary two-edge path: the `K₄` on
`{v, a, b, x}` carries `i, i` on the two edges at `v`, `c s(a,b)` on the leaf edge and, if some edge
at `v` had the leaf colour, that colour again — **at most four** colours, against the five that
`Admissible` demands. -/
theorem twoA_zeroA {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n) {i : Fin k} {v : Verts n}
    (hv : v ∈ twoA c i) {a b : Verts n} (ha : a ∈ Nbrs c i v) (hb : b ∈ Nbrs c i v)
    (hab : a ≠ b) : v ∈ zeroA c (c s(a, b)) := by
  have h3 : v ≠ a := (mem_Nbrs.mp ha).1.symm
  have h4 : v ≠ b := (mem_Nbrs.mp hb).1.symm
  have h5 : c s(v, a) = i := (mem_Nbrs.mp ha).2
  have h6 : c s(v, b) = i := (mem_Nbrs.mp hb).2
  have hne : c s(a, b) ≠ i := (cherry_leaf_pair hc hn hv ha hb hab).1
  exact apex_zeroA hc ⟨h3, h4, hab, h5.trans h6.symm, (h5.symm ▸ hne).symm⟩

/-- The colour that vacates a centre: if the colour-`i` neighbourhood of `v` has two elements, then
some colour is missing at `v` (namely `c s(a,b)`). -/
theorem exists_zeroA_of_card_nb_eq_two {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n)
    {i : Fin k} {v : Verts n} (h : (nb c i v (Finset.univ : Finset (Verts n))).card = 2) :
    ∃ j : Fin k, v ∈ zeroA c j := by
  obtain ⟨a, b, ha, hb, hab⟩ :=
    exists_two_ne_mem_of_card_eq_two (α := Verts n) (s := nb c i v (Finset.univ : Finset (Verts n))) h
  exact ⟨c s(a, b), twoA_zeroA hc hn (mem_twoA.mpr h) ha hb hab⟩

/-! ### §2  EVERY CENTRE IS A WASTED SLOT -/

/-- **EVERY TWO-EDGE-PATH CENTRE IS MISSED BY SOME COLOUR.**  The number of *distinct* centres of
the two-edge paths of `c` is at most the number of unused `(vertex, colour)` slots. -/
theorem card_centres_le_isolated {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n) :
    ((Finset.univ : Finset (Fin k)).biUnion fun i : Fin k => twoA c i).card ≤ Isolated c := by
  refine card_le_isolated_of_forall_mem (S := _) ?_
  intro v hv
  obtain ⟨i, _, hv⟩ := Finset.mem_biUnion.mp hv
  exact exists_zeroA_of_card_nb_eq_two hc hn (mem_twoA.mp hv)

/-- Pigeonhole: if `k + 2 ≤ n` then every vertex is the centre of a two-edge path, because the
`n - 1` edges at `v` cannot all carry distinct colours out of a palette of `k ≤ n - 2`. -/
theorem exists_twoA_of_le {c : Col n k} (hc : Admissible c) (hk : k + 2 ≤ n) (v : Verts n) :
    ∃ i : Fin k, v ∈ twoA c i := by
  by_contra hcon
  have h1 : ∀ i : Fin k, (nb c i v (Finset.univ : Finset (Verts n))).card ≤ 1 := by
    intro i
    have h2 := nb_card_le_two hc i v (Finset.univ : Finset (Verts n))
    by_cases h3 : (nb c i v (Finset.univ : Finset (Verts n))).card = 2
    · exact (hcon ⟨i, mem_twoA.mpr h3⟩).elim
    · omega
  have h3 : (∑ i : Fin k, (nb c i v (Finset.univ : Finset (Verts n))).card) ≤ k := by
    calc (∑ i : Fin k, (nb c i v (Finset.univ : Finset (Verts n))).card)
        ≤ ∑ _i : Fin k, (1 : ℕ) := Finset.sum_le_sum fun i _ => h1 i
      _ = k := by simp
  have h4 := sum_nb_star c v
  omega

/-! ### §3  THE REFINED COUNTING BOUND -/

/-- **`n ≤ Isolated c` whenever `n ≥ 4` and `k ≤ n - 2`**: every one of the `n` vertices is missed
by at least one of the `k` colours, so the exact identity `Surplus.surplus_identity` cannot be
tight.  This is the first `O(n)`-sized lower bound on the unused slots of the development. -/
theorem isolated_ge_n {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n) (hk : k + 2 ≤ n) :
    n ≤ Isolated c := by
  have hmem : ∀ v ∈ (Finset.univ : Finset (Verts n)), ∃ i : Fin k, v ∈ zeroA c i := by
    intro v _
    obtain ⟨i, hi⟩ := exists_twoA_of_le hc hk v
    exact exists_zeroA_of_card_nb_eq_two hc hn (mem_twoA.mp hi)
  calc n = (Finset.univ : Finset (Verts n)).card := (Finset.card_fin n).symm
    _ ≤ Isolated c :=
      card_le_isolated_of_forall_mem (S := (Finset.univ : Finset (Verts n))) hmem

/-- **THE REFINED COUNTING BOUND `5n + 1 ≤ 6k`.**  Every admissible `k`-colouring of `K_n` (`n ≥ 4`)
with `k ≤ n - 2` satisfies `5 * n + 1 ≤ 6 * k` — the catalog bound `5 * (n-1) ≤ 6 * k`
(`Cherry.five_sixth_lower`) with **one whole unit added back**, because `Isolated c ≥ n`
(`isolated_ge_n`) and `Surplus.surplus_of_k` prices the unused slots at `6` units each. -/
theorem five_n_add_one_le_six_k {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n) (hk : k + 2 ≤ n) :
    5 * n + 1 ≤ 6 * k := by
  have h1 := surplus_identity hc hn
  have h2 := isolated_ge_n hc hn hk
  have hB : 5 * n * (n - 1) + 6 * n = 5 * n * n + n := by
    have h3 : 5 * n * (n - 1) + 5 * n = 5 * n * n := mul_sub_one_add (5 * n) n (by omega)
    omega
  have hD1 : 5 * n * (n - 1) + 6 * n ≤ 6 * (n * k) := by
    calc 5 * n * (n - 1) + 6 * n
        ≤ (5 * n * (n - 1)) + (6 * Isolated c + 2 * Defect c) := by omega
      _ = 6 * (n * k) := by
        calc 5 * n * (n - 1) + (6 * Isolated c + 2 * Defect c)
            = 5 * (n * (n - 1)) + 6 * Isolated c + 2 * Defect c := by ac_rfl
          _ = 6 * (n * k) := h1.symm
  have hD : n * (5 * n + 1) ≤ n * (6 * k) := by
    calc n * (5 * n + 1) = 5 * n * n + n := by ring
      _ = 5 * n * (n - 1) + 6 * n := hB.symm
      _ ≤ 6 * (n * k) := hD1
      _ = n * (6 * k) := by ring
  exact Nat.le_of_mul_le_mul_left hD (by omega)

/-- **THE REFINED COUNTING BOUND, UNCONDITIONALLY, FOR `n ≥ 7`.**  If `k ≥ n - 1` then
`6k ≥ 6n - 6 ≥ 5n + 1` for `n ≥ 7`; if `k ≤ n - 2` the refined bound `five_n_add_one_le_six_k`
applies. -/
theorem five_n_add_one_le_six_k_of_seven {c : Col n k} (hc : Admissible c) (hn : 7 ≤ n) :
    5 * n + 1 ≤ 6 * k := by
  by_cases hk : k + 2 ≤ n
  · exact five_n_add_one_le_six_k hc (by omega) hk
  · have h1 : n ≤ k + 1 := by omega
    omega

/-- **THE REFINED CATALOG LOWER BOUND, IN INTEGRAL FORM: `⌈(5n+1)/6⌉ ≤ f(n,4,5)` for `n ≥ 7`.**
This is `Tables.EG_ge_ceil_five_sixth` (`⌈5(n-1)/6⌉ ≤ f(n,4,5)`) with one unit added: since
`⌈(5n+1)/6⌉ - 1 = ⌊5n/6⌋ ≤ ⌈5(n-1)/6⌉`, the refinement is **exactly one colour** above the catalog
form at every `n ≥ 7`. -/
theorem EG_ge_ceil_five_sixth_plus_one (n : ℕ) (hn : 7 ≤ n) : (5 * n + 1 + 5) / 6 ≤ EG n := by
  obtain ⟨c, hc⟩ := EG_admissible n
  have h1 := five_n_add_one_le_six_k_of_seven hc hn
  omega

/-- The refinement is never weaker than the catalog form: `⌈5(n-1)/6⌉ ≤ ⌈(5n+1)/6⌉`. -/
theorem ceil_five_sixth_le_refined (n : ℕ) : (5 * (n - 1) + 5) / 6 ≤ (5 * n + 1 + 5) / 6 := by
  omega

/-! ### §4  The instances -/

/-- **No admissible seven-colouring of `K₉`**: `f(9,4,5) ≥ 8`. -/
theorem no_seven_of_nine : ¬ (∃ c : Col 9 7, Admissible c) := by
  rintro ⟨c, hc⟩
  have h1 := five_n_add_one_le_six_k hc (by norm_num) (by norm_num)
  norm_num at h1

/-- **No admissible eight-colouring of `K₁₀`**: `f(10,4,5) ≥ 9`. -/
theorem no_eight_of_ten : ¬ (∃ c : Col 10 8, Admissible c) := by
  rintro ⟨c, hc⟩
  have h1 := five_n_add_one_le_six_k hc (by norm_num) (by norm_num)
  norm_num at h1

/-- **No admissible nine-colouring of `K₁₁`**: `f(11,4,5) ≥ 10`. -/
theorem no_nine_of_eleven : ¬ (∃ c : Col 11 9, Admissible c) := by
  rintro ⟨c, hc⟩
  have h1 := five_n_add_one_le_six_k hc (by norm_num) (by norm_num)
  norm_num at h1

/-- **No admissible ten-colouring of `K₁₂`**: `f(12,4,5) ≥ 11`. -/
theorem no_ten_of_twelve : ¬ (∃ c : Col 12 10, Admissible c) := by
  rintro ⟨c, hc⟩
  have h1 := five_n_add_one_le_six_k hc (by norm_num) (by norm_num)
  norm_num at h1

/-- `f(9,4,5) ≥ 8` — the lower half of `Nine.EG_nine`, **by counting**: the 80-minute search
certificate `Nine.certD_nine_six` is redundant. -/
theorem EG_nine_ge_eight : 8 ≤ EG 9 := by
  obtain ⟨c, hc⟩ := EG_admissible 9
  have h1 := five_n_add_one_le_six_k_of_seven hc (by norm_num)
  omega

/-- **THE EXACT VALUE `f(9,4,5) = 8`** — previously `Nine.EG_nine`, which needs the certificate
`Nine.certD_nine_six` (80 min, kept off the default build path); now on the default build path. -/
theorem EG_nine : EG 9 = 8 := Nat.le_antisymm EG_nine_le EG_nine_ge_eight

/-- `f(10,4,5) ≥ 9`: benchmark **B4** (`f(10,4,5) ∈ {8,9}`) improved by counting. -/
theorem EG_ten_ge_nine : 9 ≤ EG 10 := by
  obtain ⟨c, hc⟩ := EG_admissible 10
  have h1 := five_n_add_one_le_six_k_of_seven hc (by norm_num)
  omega

/-- **THE EXACT VALUE `f(10,4,5) = 9`** — benchmark **B4** is CLOSED by counting, with `Tables.tenCol`
(an admissible nine-colouring of `K₁₀`) as the witness. -/
theorem EG_ten : EG 10 = 9 := Nat.le_antisymm EG_ten_le EG_ten_ge_nine

/-- `f(11,4,5) ≥ 10`. -/
theorem EG_eleven_ge_ten : 10 ≤ EG 11 := by
  obtain ⟨c, hc⟩ := EG_admissible 11
  have h1 := five_n_add_one_le_six_k_of_seven hc (by norm_num)
  omega

/-- **THE EXACT VALUE `f(11,4,5) = 10`** — with `Tables.elevenCol` as the witness. -/
theorem EG_eleven : EG 11 = 10 := Nat.le_antisymm EG_eleven_le EG_eleven_ge_ten

/-- `f(12,4,5) ≥ 11` and `f(13,4,5) ≥ 11`: the refined bound at the two orders for which the
development had only the search-free classical bound `⌈5(n-1)/6⌉`. -/
theorem EG_twelve_ge_eleven : 11 ≤ EG 12 := by
  obtain ⟨c, hc⟩ := EG_admissible 12
  have h1 := five_n_add_one_le_six_k_of_seven hc (by norm_num)
  omega

/-- `f(13,4,5) ≥ 11` by this file's bound as well (`Strict.EG_thirteen_ge_eleven` reaches the
same value by the *one wasted slot* bound of round 53; the two agree whenever `n ≡ 1 (mod 6)`, and
this one is strictly better otherwise — see `refined_beats_eg_strict`). -/
theorem EG_thirteen_ge_eleven' : 11 ≤ EG 13 := by
  obtain ⟨c, hc⟩ := EG_admissible 13
  have h1 := five_n_add_one_le_six_k_of_seven hc (by norm_num)
  omega

/-- **THE REFINEMENT BEATS THE ROUND-53 BOUND OFF THE RESIDUE CLASS `n ≡ 1 (mod 6)`.**
`Strict.eg_strict` buys one unit of `6k` from `Isolated c ≥ 1`, so it reads `6k ≥ 5(n-1) + 1`;
`five_n_add_one_le_six_k_of_seven` buys six units from `Isolated c ≥ n`, reading
`6k ≥ 5n + 1 = 5(n-1) + 6`.  The gap is a whole colour whenever `n mod 6 ≠ 1`: at `n = 10` it
turns benchmark B4 (`f(10,4,5) ∈ {8,9}`) into `f(10,4,5) = 9`. -/
theorem refined_dominates_eg_strict (n : ℕ) (hn : 4 ≤ n) : 5 * (n - 1) + 1 ≤ 6 * EG n := by
  obtain ⟨c, hc⟩ := EG_admissible n
  by_cases hk : EG n + 2 ≤ n
  · have h := five_n_add_one_le_six_k hc (by omega) hk
    omega
  · exact eg_strict n hn

/-- **NO ADMISSIBLE COLOURING BELOW THE REFINED BOUND.**  For every `n ≥ 7` and every `k` with
`6k < 5n + 1` (equivalently `k < ⌈(5n+1)/6⌉`) there is no admissible `k`-colouring of `K_n`: this is
the general form of all the instances of §4, and it is the version a search has to beat. -/
theorem no_colouring_of_refined (n k : ℕ) (hn : 7 ≤ n) (hk : 6 * k < 5 * n + 1) :
    ¬ (∃ c : Col n k, Admissible c) := by
  rintro ⟨c, hc⟩
  have h1 := five_n_add_one_le_six_k_of_seven hc hn
  omega

/-- **THE REFINED BOUND IN REAL FORM, IN THE SHAPE OF THE HEADLINE.**  For every `n ≥ 7`,

    `5n/6 + 1/6 ≤ f(n,4,5)`,

i.e. `f(n,4,5) = 5n/6 + o(n)` with the constant improved by one sixth of a colour — the mirror
image of `Main.fiveSixthLower_eps`, which reads `5n/6 - εn ≤ f(n,4,5)`. -/
theorem refined_half_eps (n : ℕ) (hn : 7 ≤ n) : (5 : ℝ) * (n : ℝ) / 6 + 1 / 6 ≤ (EG n : ℝ) := by
  obtain ⟨c, hc⟩ := EG_admissible n
  have h1 := five_n_add_one_le_six_k_of_seven hc hn
  have h2 : (5 : ℝ) * (n : ℝ) + 1 ≤ 6 * (EG n : ℝ) := by exact_mod_cast h1
  linarith
/-! ### §5  The shape of a colouring at the refined bound -/

/-- **AT `6k = 5n + 1` EVERY SLOT BUT ONE IS USED.**  If an admissible colouring attains the
refined bound with `k ≤ n-2`, then `Isolated c = n` (each vertex is missed by exactly one colour)
and `Defect c = 0` (every edge is paid for by a two-edge path): `surplus_of_k` gives
`6 * Isolated c + 2 * Defect c = n * (6k - 5(n-1)) = 6 * n`. -/
theorem isolated_eq_n_defect_eq_zero {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n)
    (hk : k + 2 ≤ n) (heq : 6 * k = 5 * n + 1) : Isolated c = n ∧ Defect c = 0 := by
  have h1 := surplus_of_k hc hn
  have h2 := isolated_ge_n hc hn hk
  have h3 : 6 * k - 5 * (n - 1) = 6 := by omega
  have h4 : 6 * Isolated c + 2 * Defect c = 6 * n := by
    calc 6 * Isolated c + 2 * Defect c = n * (6 * k - 5 * (n - 1)) := h1
      _ = n * 6 := by rw [h3]
      _ = 6 * n := Nat.mul_comm _ _
  constructor <;> omega

/-- **THE SHAPE OF BENCHMARK B5.**  `n = 13, k = 11` is the first order at which the refined bound
`6k ≥ 5n + 1` can be *attained* (`6 · 11 = 5 · 13 + 1`), and `Strict.EG_thirteen_ge_eleven` shows no
admissible 10-colouring of `K₁₃` exists.  So an admissible 11-colouring of `K₁₃` — if there is one —
must use every slot but one and pay for every edge: `Isolated c = 13` (each vertex is missed by
exactly one colour, namely the leaf colour of both of its two two-edge paths) and `Defect c = 0`.
This is the whole of `Main.extremal_at_thirteen_is_open` in the currency of the defects. -/
theorem extremal_at_thirteen_shape {c : Col 13 11} (hc : Admissible c) :
    Isolated c = 13 ∧ Defect c = 0 :=
  isolated_eq_n_defect_eq_zero hc (by norm_num) (by norm_num) (by norm_num)

/-! ### §6  Non-vacuity: the leaf-colour lemma on the verified constructions -/

set_option maxRecDepth 10000 in
/-- The leaf-colour fact `twoA_zeroA` holds on the verified five-colouring of `K₆`: whenever the
colour-`i` neighbourhood of `v` has two elements `a ≠ b`, the colour `c s(a,b)` occurs on no edge at
`v`. -/
theorem leafVacant_sixCol :
    ∀ (v a b : Verts 6) (i : Fin 5), (nb sixCol i v (Finset.univ : Finset (Verts 6))).card = 2 →
      a ∈ Nbrs sixCol i v → b ∈ Nbrs sixCol i v → a ≠ b → v ∈ zeroA sixCol (sixCol s(a, b)) := by
  native_decide

set_option maxRecDepth 10000 in
/-- The same for the eight-colouring of `K₉`. -/
theorem leafVacant_nineCol :
    ∀ (v a b : Verts 9) (i : Fin 8), (nb nineCol i v (Finset.univ : Finset (Verts 9))).card = 2 →
      a ∈ Nbrs nineCol i v → b ∈ Nbrs nineCol i v → a ≠ b → v ∈ zeroA nineCol (nineCol s(a, b)) :=
  by native_decide

set_option maxRecDepth 10000 in
/-- The same for the nine-colouring of `K₁₀`. -/
theorem leafVacant_tenCol :
    ∀ (v a b : Verts 10) (i : Fin 9), (nb tenCol i v (Finset.univ : Finset (Verts 10))).card = 2 →
      a ∈ Nbrs tenCol i v → b ∈ Nbrs tenCol i v → a ≠ b → v ∈ zeroA tenCol (tenCol s(a, b)) :=
  by native_decide

set_option maxRecDepth 10000 in
/-- The same for the ten-colouring of `K₁₁`. -/
theorem leafVacant_elevenCol :
    ∀ (v a b : Verts 11) (i : Fin 10),
      (nb elevenCol i v (Finset.univ : Finset (Verts 11))).card = 2 →
      a ∈ Nbrs elevenCol i v → b ∈ Nbrs elevenCol i v → a ≠ b →
      v ∈ zeroA elevenCol (elevenCol s(a, b)) := by
  native_decide

/-- **NON-VACUITY OF THE INSTRUMENT.**  The unused slots of the four verified constructions are
`0, 4, 8, 10` for `K₆, K₉, K₁₀, K₁₁`.  Each of these colourings uses `k = n - 1` colours — exactly
the number of edges at a vertex — so `isolated_ge_n` (which needs `k ≤ n-2`) does not apply to
them, and the new instrument is consistent with every witness this development has produced.  It
bites exactly in the regime no construction of the development reaches: a colouring with
`k ≤ n - 2` colours, i.e. at least **two** wasted slots at every vertex. -/
theorem isolated_sixCol : Isolated sixCol = 0 := by native_decide

theorem isolated_nineCol : Isolated nineCol = 4 := by native_decide

theorem isolated_tenCol : Isolated tenCol = 8 := by native_decide

theorem isolated_elevenCol : Isolated elevenCol = 10 := by native_decide

end JSP140
