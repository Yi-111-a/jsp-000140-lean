import JSPProblem.Definitions
import JSPProblem.ColorClass

/-!
# JSP-000140 — the headline statement

**Catalog statement** (`awards/problems/catalog-0101-0200.md`, record `JSP-000140`):

> **JSP-000140 · How many edge colors are necessary if every four-vertex clique must contain
> at least five colors?**
>
> Graph theory; no later than 1997; current status **Solved**; Lean proof in the catalog: No.
> `[BCDP22]` S. Banerjee, P. Bradshaw, S. Letzter, A. Pokrovskiy, *The Erdős–Gyárfás function
> `f(n,4,5) = 5n/6 + o(n)` — so Gyárfás was right*, arXiv:2207.02920 (2022).

The quantity asked for is the **Erdős–Gyárfás function** `f(n, p, q)` — the least number of
colours in an edge-colouring of `K_n` in which every `K_p` spans at least `q` colours —
specialised to `f(n, 4, 5)`, i.e. `JSP140.EG n` of `Definitions.lean`.

## What this file contains

* `jsp_000140_target` — the *exact* statement of the required theorem `jsp_000140_main`, as a
  `def` (not yet a proved theorem; see `blockers` in `discovery/JSP-000140/policy.json`):
  `FiveSixth EG`, i.e. `f(n,4,5) = 5n/6 + o(n)` in ε-form.
* `fiveSixth_colouring_iff` / `fiveSixth_number_iff` — a *reduction* of the headline
  statement to two purely combinatorial statements, one for each direction.  These are proved
  and identify exactly what still has to be proved for the prize.
* Proved partial results: the **local structure theorem** (`Definitions.lean`,
  `ColorClass.lean`) and the upper bound `f(n,4,5) ≤ n²`.
-/

namespace JSP140

variable {n k : ℕ}

/-- **The target of the required theorem** `jsp_000140_main`:
`f(n,4,5) = 5n/6 + o(n)`, i.e. `|f(n,4,5) - 5n/6| ≤ ε n` for all large `n`, for every
`ε > 0`.  (BCDP22, arXiv:2207.02920.) -/
def jsp_000140_target : Prop := FiveSixth EG

/-- The lower half of the headline statement, phrased for *colourings*: for every `ε > 0` and
all large `n`, **every** admissible `k`-colouring of `K_n` satisfies `k ≥ 5n/6 - ε n`.  This
is the difficult content of the lower bound of BCDP22. -/
def AdmissibleLower (ε : ℝ) : Prop :=
  ∀ ε' : ℝ, 0 < ε' → ∃ N : ℕ, ∀ m : ℕ, N ≤ m → ∀ (j : ℕ) (c : Col m j), Admissible c →
    5 * (m : ℝ) / 6 - ε' * m ≤ j

/-- The upper half of the headline statement, phrased for *colourings*: for every `ε > 0` and
all large `n` there is an admissible `k`-colouring of `K_n` with `k ≤ 5n/6 + ε n`.  This is
the content of the construction in BCDP22. -/
def AdmissibleUpper (ε : ℝ) : Prop :=
  ∀ ε' : ℝ, 0 < ε' → ∃ N : ℕ, ∀ m : ℕ, N ≤ m → ∃ (j : ℕ) (c : Col m j), Admissible c ∧
    (j : ℝ) ≤ 5 * (m : ℝ) / 6 + ε' * m

/-- **The lower bound of the headline theorem, reformulated.**  `EG` is the minimum number of
colours, so the numerical lower bound `f(n,4,5) ≥ 5n/6 - ε n` is exactly the statement that
*every* admissible colouring uses that many colours. -/
theorem fiveSixthLower_iff (ε : ℝ) : FiveSixthLower EG ↔ AdmissibleLower ε := by
  constructor
  · intro h
    intro ε' hε'
    obtain ⟨N, hN⟩ := h ε' hε'
    refine ⟨N, fun m hm j c hc => ?_⟩
    exact le_trans (by simpa using hN m hm) (by simpa using EG_le m j c hc)
  · intro h
    intro ε' hε'
    obtain ⟨N, hN⟩ := h ε' hε'
    refine ⟨N, fun m hm => ?_⟩
    obtain ⟨c, hc⟩ := EG_admissible m
    exact hN m hm (EG m) c hc

/-- **The upper bound of the headline theorem, reformulated.** -/
theorem fiveSixthUpper_iff (ε : ℝ) : FiveSixthUpper EG ↔ AdmissibleUpper ε := by
  constructor
  · intro h
    intro ε' hε'
    obtain ⟨N, hN⟩ := h ε' hε'
    refine ⟨N, fun m hm => ?_⟩
    obtain ⟨c, hc⟩ := EG_admissible m
    exact ⟨EG m, c, hc, by simpa using hN m hm⟩
  · intro h
    intro ε' hε'
    obtain ⟨N, hN⟩ := h ε' hε'
    refine ⟨N, fun m hm => ?_⟩
    obtain ⟨j, c, hc, hj⟩ := hN m hm
    exact le_trans (by simpa using EG_le m j c hc) hj

/-- The headline theorem is exactly the conjunction of the two combinatorial bounds. -/
theorem jsp_000140_target_iff : jsp_000140_target ↔ AdmissibleLower 1 ∧ AdmissibleUpper 1 := by
  rw [jsp_000140_target, fiveSixth_iff, fiveSixthLower_iff, fiveSixthUpper_iff]

/-! ### Proved partial results -/

/-- Two edges with the same endpoints: the two endpoints of one are each an endpoint of the
other. -/
private lemma sym2_mem {α : Type*} {x y x' y' : α} (h : s(x, y) = s(x', y')) :
    (x = x' ∨ x = y') ∧ (y = x' ∨ y = y') := by
  rcases sym2_inj h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨Or.inl h1, Or.inr h2⟩
  · exact ⟨Or.inr h1, Or.inl h2⟩

/-- The three edges of a triangle on three distinct vertices are pairwise distinct. -/
theorem three_edges_ne {α : Type*} {a b d : α} (hab : a ≠ b) (had : a ≠ d) (hbd : b ≠ d) :
    s(a, b) ≠ s(a, d) ∧ s(a, b) ≠ s(b, d) ∧ s(a, d) ≠ s(b, d) := by
  refine ⟨fun hh => ?_, fun hh => ?_, fun hh => ?_⟩
  · obtain ⟨h1, h2⟩ := sym2_mem hh
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> aesop
  · obtain ⟨h1, h2⟩ := sym2_mem hh
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> aesop
  · obtain ⟨h1, h2⟩ := sym2_mem hh
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> aesop

/-- **No monochromatic triangle.**  In an admissible colouring of `K_n` (with `n ≥ 4`) no
three vertices span three edges of the same colour: a fourth vertex would give a `K₄` with
three equally coloured edges, contradicting `classIn_card_le_two`. -/
theorem no_mono_triangle {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n) (i : Fin k)
    {a b d : Verts n} (hab : a ≠ b) (had : a ≠ d) (hbd : b ≠ d)
    (h : c s(a, b) = i ∧ c s(a, d) = i ∧ c s(b, d) = i) : False := by
  obtain ⟨z, hz⟩ := exists_vertex_outside hn (threeSet a b d)
    (by rw [card_threeSet hab had hbd]; omega)
  have hza : a ≠ z := fun hh => hz (hh ▸ Finset.mem_insert_self a _)
  have hzb : b ≠ z := fun hh => hz (hh ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self b _))
  have hzd : d ≠ z := fun hh => hz (hh ▸ Finset.mem_insert_of_mem
    (Finset.mem_insert_of_mem (Finset.mem_insert_self d _)))
  have h4 : FourDistinct a b d z := ⟨hab, had, hza, hbd, hzb, hzd⟩
  obtain ⟨he1, he2, he3⟩ := h
  exact three_of_classIn_fourSet hc i h4 s(a, b) s(a, d) s(b, d)
    (classIn_fourSet_mem hc i h4 a b he1 (mem_fourSet_a h4) (mem_fourSet_b h4) hab)
    (classIn_fourSet_mem hc i h4 a d he2 (mem_fourSet_a h4) (mem_fourSet_d h4) had)
    (classIn_fourSet_mem hc i h4 b d he3 (mem_fourSet_b h4) (mem_fourSet_d h4) hbd)
    (three_edges_ne hab had hbd)

/-- The upper bound proved in this development: `f(n,4,5) ≤ n²` (the injective colouring). -/
theorem upper_bound_sq (n : ℕ) : EG n ≤ n * n := EG_le_sq n

end JSP140
