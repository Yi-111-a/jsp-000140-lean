import JSPProblem.ApexPrice
import JSPProblem.Rigidity
import JSPProblem.Cell
import JSPProblem.Disj
import JSPProblem.Grid
import JSPProblem.Nibble
import JSPProblem.Tables

/-!
# JSP-000140 — round 90: **THE FIRST STAGE AS A DECOMPOSITION INTO PATH FACTORS** — the
# Oberwolfach form of the catalogue rate, the obstruction modulo `5`, and the first order at
# which the rate can be attained

Rounds 53–56, 71–72 and 88–89 attacked the *extremal* case from the counting side: what the
identity `5 · |T| ≤ n · k` forces on a complete labelled-triangle covering (`Grid.cellCount`,
`Cell.cells`, `Cell.cells_tight`), and what the two-edge paths must look like
(`tight_pathFinset_is_STS`, `tight_mod6`, `Extremal.tight_ge_thirteen`).  Every one of those
statements is *asymmetric*: it constrains the total `Σ_i`, or the aggregate `Σ_i a_i`, and the
per-colour equations `3 a_i + 2 b_i = n` are read off one colour at a time without ever forcing
the `a_i` themselves.

**This round adds the missing hypothesis and reads off the missing consequences: BALANCE.**  A
*balanced* colouring is one whose colour classes all have the same number of edges — the shape
every symmetric construction has, and the shape a random matching produces.  Under balance the
per-colour equations collapse and the catalogue rate becomes a **decomposition problem for `K_n`**,
of exactly the classical kind:

> **the extremal balanced colouring of `K_n` decomposes `E(K_n)` into `5(n-1)/6` spanning path
> factors, each of them `n/5` cherries and `n/5` single edges** — an instance of the Oberwolfach
> problem for the spanning factor `3^{n/5} 2^{n/5}`.

and the *number* `n/5` forces **`5 ∣ n`**, which together with `tight_mod6` (`n ≡ 1 mod 6`) pins
the orders down to the residue class `25 (mod 30)`.  Since `Extremal.tight_ge_thirteen` allows
`n = 13` and `n = 19`, this is a **genuine new obstruction**: **the two orders which the tightness
theory still admits cannot carry a balanced colouring at all, and `n = 25` (`k = 20`) is the first
order at which the catalogue rate is even arithmetically possible.**  That is a concrete finite
target, and `TwentyFive.sound` turns it into the exact value `f(25,4,5) = 20` the moment one such
colouring is certified.

## §0 — the factor picture

`PathFac.Factor c i` = "the colour class `i` spans `V`": every vertex carries one or two colour-`i`
edges, which — admissibility (`Cell.class_eq_twoA_add_leaf`) — says exactly that `E_i` is a
vertex-disjoint union of `a_i = |twoA c i|` cherries and `b_i = Cell.leaf c i` single edges.

* `Factor.of_cover`, `Factor.card`, `Factor.span`, `Factor.miss_eq_zero`;
* **`Factor.cells — THE CELL EQUATION OF A FACTOR, `3 a_i + 2 b_i = n`**, the counting form of "the
  factor spans the vertex set";
* **`Factor.two_mul_card — `2 |E_i| = n + a_i`**, the edge count of a spanning factor;
* **`Factor.parity_one — a spanning factor of an odd `K_n` has an ODD number of cherries.**

## §1 — at the catalogue rate every colour class is a factor

`extremal_Factor`, `extremal_cells`, `extremal_two_mul_card`, `extremal_odd`,
`extremal_parity_one`: `6k = 5(n-1)` ⟹ all `k` colour classes are spanning path factors with
`3 a_i + 2 b_i = n`.  (`Grid.decomposes_of_tight` is the grid version of the same statement.)

## §2 — BALANCE, and the Oberwolfach form

* `Balanced`, `Balanced.card_mul_k` (**the common size**: `k · |E_i| = |E(K_n)|`);
* **`Balanced.tight_five_mul — `5 |E_i| = 3 n` for every colour**;
* **`Balanced.tight_twoA`, `Balanced.tight_leaf — `5 a_i = 5 b_i = n`: every colour class has
  exactly `n/5` cherries AND exactly `n/5` single edges** — the factor type `3^{n/5} 2^{n/5}`;
* **`Balanced.five_dvd_n — `5 ∣ n`**, `Balanced.mod30 — **`n ≡ 25 (mod 30)`**,
  `Balanced.ge_twentyfive — **`25 ≤ n`**;
* `Balanced.ne_seven`, `Balanced.ne_thirteen`, `Balanced.ne_nineteen`: **the orders `7`, `13`, `19`
  carry no balanced extremal colouring** (`13` and `19` are exactly the orders
  `Extremal.tight_ge_thirteen` still admits);
* `Balanced.twentyfive`: at `n = 25`, `k = 20`, every colour class is `3⁵ 2⁵`;
* `TwentyFive` (the target), `TwentyFive.sound` (**`f(25,4,5) = 20`**),
  `TwentyFive.nineteen_impossible`, `twentyfive_ge` (`f(25,4,5) ≥ 20`).

## §3 — the arithmetic of the rate itself

* **`gcd_dvd_five — at `6k = 5(n-1)` one has `gcd n k ∣ 5`**: the palette and the order share no
  large common divisor, a purely arithmetic reason why no *cyclic* scheme can be extremal (rounds
  81 and 85 killed the difference- and sum-type families by hand).
-/

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

namespace JSP140
namespace PathFac

variable {n k : ℕ}

/-! ### §0 — the factor picture -/

/-- **THE PATH-FACTOR PICTURE OF A COLOUR CLASS.**  `Factor c i` says that the colour class `E_i`
*spans* the vertex set: every vertex carries one or two colour-`i` edges
(`∀ v, v ∈ twoA c i ∨ v ∈ oneB c i`), and the edge count is the one of a disjoint union of
`|twoA c i|` cherries (two-edge paths) and `Cell.leaf c i` single edges.  The second half is
automatic for every admissible colouring (`Cell.class_eq_twoA_add_leaf`), so `Factor` is exactly
the spanning condition. -/
def Factor (c : Col n k) (i : Fin k) : Prop :=
  (∀ v : Verts n, v ∈ twoA c i ∨ v ∈ oneB c i) ∧
    2 * (twoA c i).card + Cell.leaf c i = (classIn c i (Finset.univ : Finset (Verts n))).card

/-- The edge count of a factor. -/
theorem Factor.card {c : Col n k} {i : Fin k} (hF : Factor c i) :
    2 * (twoA c i).card + Cell.leaf c i = (classIn c i (Finset.univ : Finset (Verts n))).card :=
  hF.2

/-- The spanning condition of a factor. -/
theorem Factor.span {c : Col n k} {i : Fin k} (hF : Factor c i) (v : Verts n) :
    v ∈ twoA c i ∨ v ∈ oneB c i := hF.1 v

/-- **ONLY THE SPANNING IS NEW**: for an admissible colouring the edge count of a disjoint union of
cherries and single edges holds for every colour (`Cell.class_eq_twoA_add_leaf`). -/
theorem Factor.of_cover {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n) {i : Fin k}
    (hcov : ∀ v : Verts n, v ∈ twoA c i ∨ v ∈ oneB c i) : Factor c i :=
  ⟨hcov, Cell.class_eq_twoA_add_leaf hc hn i⟩

/-- **A SPANNING COLOUR CLASS MISSES NO VERTEX.** -/
theorem Factor.miss_eq_zero {c : Col n k} {i : Fin k} (hF : Factor c i) : Miss.miss c i = 0 := by
  have hsub : Miss.active c i = (Finset.univ : Finset (Verts n)) := by
    refine Finset.eq_univ_of_forall fun v => ?_
    rw [Miss.mem_active]
    exact hF.1 v
  have h := Miss.miss_add_active (c := c) i
  rw [hsub, Finset.card_univ, Fintype.card_fin] at h
  omega

/-- **THE CELL EQUATION OF A FACTOR: `3 · (cherries) + 2 · (single edges) = n`.**  This is the
counting form of "the factor spans `V`": its components use `3 a + 2 b` distinct vertices. -/
theorem Factor.cells {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n) {i : Fin k} (hF : Factor c i) :
    3 * (twoA c i).card + 2 * Cell.leaf c i = n := by
  have h1 := Cell.cells hc hn i
  have h2 := Factor.miss_eq_zero hF
  omega

/-- **THE EDGE COUNT OF A SPANNING FACTOR: `2 |E_i| = n + a_i`.**  A factor with `a` cherries and
`b` single edges has `2a + b` edges and `3a + 2b` vertices, so `2(2a+b) = (3a+2b) + a`. -/
theorem Factor.two_mul_card {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n) {i : Fin k}
    (hF : Factor c i) : 2 * (classIn c i (Finset.univ : Finset (Verts n))).card
      = n + (twoA c i).card := by
  have h1 := Factor.card hF
  have h2 := Factor.cells hc hn hF
  omega

/-- **A SPANNING FACTOR OF AN ODD COMPLETE GRAPH HAS AN ODD NUMBER OF CHERRIES.** -/
theorem Factor.parity_one {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n) {i : Fin k}
    (hF : Factor c i) (hnodd : n % 2 = 1) : (twoA c i).card % 2 = 1 := by
  have h1 := Cell.parity hc hn i
  have h2 := Factor.miss_eq_zero hF
  rw [h2, Nat.sub_zero, hnodd] at h1
  exact h1

/-! ### §1 — at the catalogue rate every colour class is a factor -/

/-- **THE EXTREMAL CASE IS A FACTORISATION, COLOUR BY COLOUR.**  If an admissible colouring of `K_n`
attains the catalogue rate `6k = 5(n-1)`, then every one of its `k` colour classes spans `V` and
is a disjoint union of cherries and single edges. -/
theorem extremal_Factor {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n) (hk : 6 * k = 5 * (n - 1))
    (i : Fin k) : Factor c i := by
  refine Factor.of_cover hc hn ?_
  exact tight_covers hc hn (tight_attained hc hn hk) hk i

/-- The cell equation at the catalogue rate (`Cell.cells_tight`, in the `Factor` language). -/
theorem extremal_cells {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n) (hk : 6 * k = 5 * (n - 1))
    (i : Fin k) : 3 * (twoA c i).card + 2 * Cell.leaf c i = n :=
  Cell.cells_tight hc hn hk i

/-- `2 |E_i| = n + a_i` at the catalogue rate. -/
theorem extremal_two_mul_card {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n)
    (hk : 6 * k = 5 * (n - 1)) (i : Fin k) :
    2 * (classIn c i (Finset.univ : Finset (Verts n))).card = n + (twoA c i).card :=
  Factor.two_mul_card hc hn (extremal_Factor hc hn hk i)

/-- `n ≡ 1 (mod 6)` in the extremal case (`tight_mod6`), hence `n` is odd. -/
theorem extremal_odd {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n) (hk : 6 * k = 5 * (n - 1)) :
    n % 2 = 1 := by
  have h := (tight_mod6 hc hn (tight_attained hc hn hk) hk).1
  have h2 : n % 2 = (n % 6) % 2 := by
    have h3 := Nat.mod_mod_of_dvd n (show (2 : ℕ) ∣ 6 by decide)
    omega
  rw [h2, h]

/-- **AT THE CATALOGUE RATE EVERY COLOUR CLASS HAS AN ODD NUMBER OF CHERRIES** (the `Factor`
reading of `Extremal.tight_twoA_odd`). -/
theorem extremal_parity_one {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n)
    (hk : 6 * k = 5 * (n - 1)) (i : Fin k) : (twoA c i).card % 2 = 1 :=
  Factor.parity_one hc hn (extremal_Factor hc hn hk i) (extremal_odd hc hn hk)

/-! ### §2 — BALANCE: the Oberwolfach form of the catalogue rate -/

/-- **BALANCE**: all colour classes have the same number of edges — the shape of every symmetric
construction, and the shape a random matching produces.  The extremal theory of rounds 53–56 and
71–72 never needed it, and never used it; with it the per-colour equations of `Cell.cells_tight`
become *absolute* numbers. -/
def Balanced (c : Col n k) : Prop :=
  ∀ i j : Fin k, (classIn c i (Finset.univ : Finset (Verts n))).card
              = (classIn c j (Finset.univ : Finset (Verts n))).card

instance decidableBalanced {n k : ℕ} (c : Col n k) : Decidable (Balanced c) := by
  unfold Balanced
  infer_instance

/-- **THE COMMON SIZE OF A BALANCED COLOURING**: `k · |E_i| = |E(K_n)|`. -/
theorem Balanced.card_mul_k {c : Col n k} (hB : Balanced c) (i : Fin k) :
    (classIn c i (Finset.univ : Finset (Verts n))).card * k
      = (edgeFinset (Finset.univ : Finset (Verts n))).card := by
  have hsum := sum_card_classIn c (Finset.univ : Finset (Verts n))
  have h1 : (∑ j : Fin k, (classIn c j (Finset.univ : Finset (Verts n))).card)
      = (classIn c i (Finset.univ : Finset (Verts n))).card * k := by
    calc (∑ j : Fin k, (classIn c j (Finset.univ : Finset (Verts n))).card)
        = ∑ _j : Fin k, (classIn c i (Finset.univ : Finset (Verts n))).card :=
          Finset.sum_congr rfl fun j _ => (hB i j).symm
      _ = (classIn c i (Finset.univ : Finset (Verts n))).card * Fintype.card (Fin k) := by
          rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
          ring
      _ = (classIn c i (Finset.univ : Finset (Verts n))).card * k := by rw [Fintype.card_fin]
  rw [h1] at hsum
  exact hsum

/-- **THE COMMON SIZE AT THE CATALOGUE RATE IS `3n/5`: `5 · |E_i| = 3 n` for every colour.** -/
theorem Balanced.tight_five_mul {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n)
    (hk : 6 * k = 5 * (n - 1)) (hB : Balanced c) (i : Fin k) :
    5 * (classIn c i (Finset.univ : Finset (Verts n))).card = 3 * n := by
  have h1 := Balanced.card_mul_k hB i
  have h2 := card_edgeFinset_univ_two n
  have hA : 6 * ((classIn c i (Finset.univ : Finset (Verts n))).card * k)
      = 3 * (n * (n - 1)) := by rw [h1]; omega
  have hB' : 6 * ((classIn c i (Finset.univ : Finset (Verts n))).card * k)
      = 5 * (classIn c i (Finset.univ : Finset (Verts n))).card * (n - 1) := by
    calc 6 * ((classIn c i (Finset.univ : Finset (Verts n))).card * k)
        = (classIn c i (Finset.univ : Finset (Verts n))).card * (6 * k) := by ring
      _ = (classIn c i (Finset.univ : Finset (Verts n))).card * (5 * (n - 1)) := by rw [hk]
      _ = 5 * (classIn c i (Finset.univ : Finset (Verts n))).card * (n - 1) := by ring
  have hE : 0 < (edgeFinset (Finset.univ : Finset (Verts n))).card := by
    have hpos : 0 < n * (n - 1) := Nat.mul_pos (by omega) (by omega)
    have h2' : 0 < 2 * (edgeFinset (Finset.univ : Finset (Verts n))).card := by omega
    omega
  have hCk : 0 < (classIn c i (Finset.univ : Finset (Verts n))).card * k := by rw [h1]; exact hE
  have hcard : 0 < (classIn c i (Finset.univ : Finset (Verts n))).card := by
    rcases Nat.eq_zero_or_pos (classIn c i (Finset.univ : Finset (Verts n))).card with hz | hp
    · rw [hz] at hCk
      omega
    · exact hp
  have hC : (n - 1) * (5 * (classIn c i (Finset.univ : Finset (Verts n))).card)
      = (n - 1) * (3 * n) := by
    calc (n - 1) * (5 * (classIn c i (Finset.univ : Finset (Verts n))).card)
        = (5 * (classIn c i (Finset.univ : Finset (Verts n))).card) * (n - 1) := by ring
      _ = 6 * ((classIn c i (Finset.univ : Finset (Verts n))).card * k) := hB'.symm
      _ = 3 * (n * (n - 1)) := hA
      _ = (n - 1) * (3 * n) := by ring
  exact Nat.mul_left_cancel (by omega) hC

/-- **THE FACTOR TYPE OF A BALANCED EXTREMAL COLOURING: `5 · a_i = n`, i.e. every colour class is
`n/5` cherries.**  Together with `Balanced.tight_leaf` this says that *each* colour class is the
spanning factor `3^{n/5} 2^{n/5}` — an instance of the Oberwolfach problem. -/
theorem Balanced.tight_twoA {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n)
    (hk : 6 * k = 5 * (n - 1)) (hB : Balanced c) (i : Fin k) : 5 * (twoA c i).card = n := by
  have h1 := Balanced.tight_five_mul hc hn hk hB i
  have h2 := extremal_two_mul_card hc hn hk i
  omega

/-- **AND `5 · b_i = n`: every colour class has `n/5` single edges as well.** -/
theorem Balanced.tight_leaf {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n)
    (hk : 6 * k = 5 * (n - 1)) (hB : Balanced c) (i : Fin k) : 5 * Cell.leaf c i = n := by
  have h1 := Balanced.tight_five_mul hc hn hk hB i
  have h2 := Factor.card (extremal_Factor hc hn hk i)
  have h3 := Balanced.tight_twoA hc hn hk hB i
  omega

/-- **THE OBSTRUCTION MODULO `5`: A BALANCED EXTREMAL COLOURING NEEDS `5 ∣ n`.**  This is the first
`mod 5` obstruction of the development; every previous congruence statement (`tight_mod6`,
`Extend.n_mod_six_of_refined`, `Rate.dvd`) is a statement modulo `6`. -/
theorem Balanced.five_dvd_n {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n)
    (hk : 6 * k = 5 * (n - 1)) (hB : Balanced c) : 5 ∣ n := by
  have hk0 : 0 < k := by omega
  obtain ⟨i⟩ : Nonempty (Fin k) := ⟨⟨0, hk0⟩⟩
  have h := Balanced.tight_twoA hc hn hk hB i
  exact ⟨(twoA c i).card, h.symm⟩

/-- **THE ORDERS WHICH CARRY A BALANCED EXTREMAL COLOURING ARE EXACTLY `n ≡ 25 (mod 30)`.** -/
theorem Balanced.mod30 {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n)
    (hk : 6 * k = 5 * (n - 1)) (hB : Balanced c) : n % 30 = 25 := by
  have h5 := Balanced.five_dvd_n hc hn hk hB
  have h6 := (tight_mod6 hc hn (tight_attained hc hn hk) hk).1
  obtain ⟨m, hm⟩ := h5
  have hm6 : m % 6 = 5 := by omega
  have hmn : m = 6 * (m / 6) + m % 6 := (Nat.div_add_mod m 6).symm
  have hnm : n = 30 * (m / 6) + 25 := by omega
  omega

/-- **THE FIRST ORDER.** -/
theorem Balanced.ge_twentyfive {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n)
    (hk : 6 * k = 5 * (n - 1)) (hB : Balanced c) : 25 ≤ n := by
  have h := Balanced.mod30 hc hn hk hB
  omega

/-- **THE CATALOGUE RATE IS ARITHMETICALLY IMPOSSIBLE IN A BALANCED COLOURING OF `K₇`.**  This
strengthens `Extremal.no_five_colouring_of_K7`: not only does no admissible 5-colouring of `K₇`
exist, but the cell equation of `Grid.cellCount` (`3 a_j + 2 b_j = 7`, which forces `a_j = 1`)
already refuses to be balanced, since `5 ∤ 7`. -/
theorem Balanced.ne_seven : ¬ (∃ c : Col 7 5, Admissible c ∧ Balanced c) := by
  rintro ⟨c, hc, hB⟩
  have h := Balanced.five_dvd_n hc (by norm_num) (by norm_num) hB
  obtain ⟨m, hm⟩ := h
  omega

/-- **`n = 13` — the first order `Extremal.tight_ge_thirteen` allows — carries NO balanced colouring
at the catalogue rate** (`6 · 10 = 5 · 12`, but `5 ∤ 13`). -/
theorem Balanced.ne_thirteen : ¬ (∃ c : Col 13 10, Admissible c ∧ Balanced c) := by
  rintro ⟨c, hc, hB⟩
  have h := Balanced.five_dvd_n hc (by norm_num) (by norm_num) hB
  obtain ⟨m, hm⟩ := h
  omega

/-- **`n = 19` — the second order `tight_mod6` and `tight_ge_thirteen` still allow — carries NO
balanced colouring at the catalogue rate** (`6 · 15 = 5 · 18`, but `5 ∤ 19`). -/
theorem Balanced.ne_nineteen : ¬ (∃ c : Col 19 15, Admissible c ∧ Balanced c) := by
  rintro ⟨c, hc, hB⟩
  have h := Balanced.five_dvd_n hc (by norm_num) (by norm_num) hB
  obtain ⟨m, hm⟩ := h
  omega

/-- **THE FIRST INSTANCE: AT `n = 25` AND `k = 20` EVERY COLOUR CLASS IS `3⁵ 2⁵`.**  Five cherries
and five single edges spanning `25` vertices, fifteen edges; twenty such factors partition
`E(K₂₅) = 300` edges. -/
theorem Balanced.twentyfive {c : Col 25 20} (hc : Admissible c) (hB : Balanced c) (i : Fin 20) :
    (twoA c i).card = 5 ∧ Cell.leaf c i = 5 ∧
      (classIn c i (Finset.univ : Finset (Verts 25))).card = 15 := by
  have h1 := Balanced.tight_twoA hc (by norm_num) (by norm_num) hB i
  have h2 := Balanced.tight_leaf hc (by norm_num) (by norm_num) hB i
  have h3 := Balanced.tight_five_mul hc (by norm_num) (by norm_num) hB i
  constructor
  · omega
  constructor
  · omega
  · omega

/-- **THE SHAPE OF THE FIRST INSTANCE.**  In a balanced extremal colouring of `K_n` the `k` colour
classes are `n/5` cherries and `n/5` single edges each: the two numbers coincide, which is the
defining feature of the factor `3^{n/5} 2^{n/5}`. -/
theorem Balanced.tight_cherries {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n)
    (hk : 6 * k = 5 * (n - 1)) (hB : Balanced c) (i : Fin k) :
    (twoA c i).card = n / 5 ∧ Cell.leaf c i = n / 5 := by
  have h1 := Balanced.tight_twoA hc hn hk hB i
  have h2 := Balanced.tight_leaf hc hn hk hB i
  have h3 : 5 ∣ n := Balanced.five_dvd_n hc hn hk hB
  obtain ⟨m, hm⟩ := h3
  constructor <;> omega

/-- **THE COUNTING LOWER BOUND AT `n = 25`: `f(25,4,5) ≥ 20`.**  The sharp catalog bound
`5(n-1)/6 = 20` is *attained* only if a 20-colouring exists, and no colouring with fewer colours
is possible at all. -/
theorem twentyfive_ge : 20 ≤ EG 25 := by
  have h := EG_ge_five_sixth 25 (by norm_num)
  omega

/-- **THE TARGET OF THE NEXT ATTACK: A BALANCED ADMISSIBLE 20-COLOURING OF `K₂₅`.**  By
`Balanced.twentyfive` it is exactly a decomposition of `E(K₂₅)` into twenty spanning factors
`3⁵ 2⁵` obeying the four-set conditions of admissibility — a finite, purely combinatorial object,
in the classical style of the Oberwolfach problem. -/
def TwentyFive : Prop := ∃ c : Col 25 20, Admissible c ∧ Balanced c

/-- **A CERTIFIED INSTANCE GIVES THE EXACT VALUE `f(25,4,5) = 20`** — the first order at which the
catalogue rate is even arithmetically possible. -/
theorem TwentyFive.sound (h : TwentyFive) : EG 25 = 20 := by
  obtain ⟨c, hc, hB⟩ := h
  have h1 : EG 25 ≤ 20 := EG_le 25 20 c hc
  exact le_antisymm h1 twentyfive_ge

/-- **AND NO SMALLER PALETTE IS ADMISSIBLE AT `n = 25`** — so a certified instance is not merely
optimal but *exactly* optimal. -/
theorem TwentyFive.nineteen_impossible : ¬ (∃ c : Col 25 19, Admissible c) := by
  rintro ⟨c, hc⟩
  have h : EG 25 ≤ 19 := EG_le 25 19 c hc
  have h20 : 20 ≤ EG 25 := twentyfive_ge
  omega

/-- **THE WHOLE FIRST STAGE, COLOUR BY COLOUR: `k · (n/5)` labelled triangles.**  In a balanced
extremal colouring every colour class carries `n/5` cherries, so the first stage of
arXiv:2207.02920 §4 has `k · n/5 = n(n-1)/6` members and the two-edge paths form a Steiner triple
system — the aggregate statement `tight_pathFinset_is_STS`, here obtained colour by colour. -/
theorem Balanced.tight_total_cherries {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n)
    (hk : 6 * k = 5 * (n - 1)) (hB : Balanced c) :
    (∑ i : Fin k, (twoA c i).card) = k * (n / 5) := by
  have hk0 : 0 < k := by omega
  obtain ⟨i⟩ : Nonempty (Fin k) := ⟨⟨0, hk0⟩⟩
  have h1 := Balanced.tight_twoA hc hn hk hB i
  have h2 := Balanced.tight_cherries hc hn hk hB i
  calc (∑ i : Fin k, (twoA c i).card)
      = ∑ _i : Fin k, n / 5 := Finset.sum_congr rfl fun j _ => (Balanced.tight_cherries hc hn hk hB j).1
    _ = k * (n / 5) := by
        rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, Fintype.card_fin]

/-- **AND THAT SUM IS `Paths c`, WHICH IS `n(n-1)/6` BY `tight_attained`**: the first stage of the
published construction at the catalogue rate is a Steiner triple system of `K_n`. -/
theorem Balanced.tight_cherries_eq_paths {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n)
    (hk : 6 * k = 5 * (n - 1)) (hB : Balanced c) :
    k * (n / 5) = Paths c := by
  have h1 := Balanced.tight_total_cherries hc hn hk hB
  change k * (n / 5) = (∑ i : Fin k, (twoA c i).card)
  rw [h1]

/-- **THE FIRST THREE ORDERS OF THE BALANCED PROGRAMME, WITH THEIR PALETTES: `(25, 20)`, `(55, 45)`,
`(85, 70)`.**  The orders are `n ≡ 25 (mod 30)` and the palettes `k = 5(n-1)/6`; a colouring
certified at any of them is, by `TwentyFive.sound`-style arguments, exactly optimal. -/
theorem Balanced.first_instances :
    6 * 20 = 5 * (25 - 1) ∧ 6 * 45 = 5 * (55 - 1) ∧ 6 * 70 = 5 * (85 - 1) ∧ 25 % 30 = 25 := by
  norm_num

/-! ### §3 — the arithmetic of the rate itself -/

/-- **AT THE CATALOGUE RATE THE PALETTE AND THE ORDER SHARE NO LARGE DIVISOR: `gcd n k ∣ 5`.**
Indeed `6k = 5n - 5`, so every common divisor of `n` and `k` divides `5`.  This is a purely
arithmetic second reason why an extremal colouring cannot be cyclic: rounds 81 and 85 killed the
difference- and sum-type families by hand, and this kills *every* colouring invariant under a
cyclic group whose order shares a divisor `> 5` with the palette. -/
theorem gcd_dvd_five {n k : ℕ} (hn : 1 ≤ n) (hk : 6 * k = 5 * (n - 1)) : Nat.gcd n k ∣ 5 := by
  have hdn : Nat.gcd n k ∣ n := Nat.gcd_dvd_left n k
  have hdk : Nat.gcd n k ∣ k := Nat.gcd_dvd_right n k
  have h1 : Nat.gcd n k ∣ 5 * n := by
    have heq : 5 * n = n + n + n + n + n := by omega
    rw [heq]
    exact dvd_add (dvd_add (dvd_add (dvd_add hdn hdn) hdn) hdn) hdn
  have h2 : Nat.gcd n k ∣ 6 * k := by
    have heq : 6 * k = k + k + k + k + k + k := by omega
    rw [heq]
    exact dvd_add (dvd_add (dvd_add (dvd_add (dvd_add hdk hdk) hdk) hdk) hdk) hdk
  have hsp : n - 1 + 1 = n := Nat.succ_pred_eq_of_pos (n := n) hn
  have hkey : 6 * k + 5 = 5 * n := by
    calc 6 * k + 5 = 5 * (n - 1) + 5 := by rw [hk]
      _ = 5 * (n - 1 + 1) := by rw [← Nat.mul_one 5, ← Nat.mul_add]
      _ = 5 * n := by rw [hsp]
  have h3 : 5 * n - 6 * k = 5 := by omega
  have h4 : Nat.gcd n k ∣ (5 * n - 6 * k) := Nat.dvd_sub h1 h2
  rw [h3] at h4
  exact h4

end PathFac
end JSP140
