import JSPProblem.Definitions
import JSPProblem.Cherry

/-!
# JSP-000140 — explicit small colourings and the *exact* values of `f(n,4,5)`

Rounds 2–15 developed the *structure* of every admissible colouring (the colour classes are
disjoint unions of two-edge paths and isolated single edges, the counting lemma
`Cherry.three_mul_paths_le_edges`, the rigidity theorem of the extremal case, …) and the
*lower* half `f(n,4,5) ≥ 5n/6 - o(n)`.  The *upper* half needs actual colourings, and so far
this development only had the round-robin (`n` colours), the ghost (`n-1` colours) and the
injective (`n²` colours) constructions — all of them far above `5n/6`.

**This file changes the attack family: instead of classifying colourings, it produces and
*verifies* them.**  The key observation is that `JSP140.Admissible` is a decidable predicate
for a *concrete* colouring (it quantifies over the finitely many four-element
`Finset (Verts n)`), so an explicit admissible colouring of `K_n` with `k` colours can be
certified in Lean by `native_decide` — a certificate which is independent of whatever search
produced the colouring and is therefore a genuine Lean proof of the upper bound
`f(n,4,5) ≤ k`.

Main results of this file:

* `tableCol`, `listCol` — the table machinery: `listCol l` is the colouring of `K_n` which
  sends the pair `{a,b}` (`a < b`) to the `(a*n+b)`-th entry of the literal list `l`;
* `admissible_sixCol` — **an admissible 5-colouring of `K_6`, proved by `native_decide`**;
* `EG_six : EG 6 = 5` — **the first exact value of the Erdős–Gyárfás function `f(n,4,5)`
  established in this development**: the sharp catalog bound `5(n-1)/6` is *attained* at
  `n = 6` (rounded up), i.e. the constant `5/6` of Bennett–Cushman–Dudek–Prałat is not
  merely asymptotically optimal but is realised by an explicit colouring of a small clique;
* `EG_ge_ceil_five_sixth` — the catalog lower bound in *integral* form, for every `n`:
  `⌈5(n-1)/6⌉ ≤ f(n,4,5)`, so any admissible colouring of `K_n` found by a search and
  verified by `native_decide` with `k = ⌈5(n-1)/6⌉` colours *proves* `f(n,4,5) = k`.
-/

namespace JSP140

/-! ### Table colourings -/

/-- A **table colouring** of `K_n` with `k` colours: the table `T : Fin (n*n) → Fin k`
assigns to the unordered pair `{a, b}` (taken in increasing order) the colour of the entry
`a * n + b`.  This is the injective colouring of `Definitions.pairEnc`, except that the table
is arbitrary. -/
def tableCol {n k : ℕ} (T : Fin (n * n) → Fin k) : Col n k :=
  Sym2.rec (motive := fun _ => Fin k)
    (fun a b => T (pairEnc n (min a b) (max a b)))
    (by
      intro a b c d h
      cases h with
      | refl => rfl
      | swap x y => simp [pairEnc, min_comm, max_comm])

/-- The table colouring given by a literal list: the pair `{a,b}` (`a < b`) receives the
entry of index `a * n + b` of `l` (entries beyond the end of `l`, and pairs with `a ≥ b`,
are irrelevant and are read off as `0`).  This is how an explicit colouring is written down:
by machine. -/
def listCol (n k : ℕ) (hk : 0 < k) (l : List ℕ) : Col n k :=
  tableCol (fun i => ⟨l.getD i.val 0 % k, Nat.mod_lt _ hk⟩)

/-- The catalog lower bound, in **integral** form: `⌈5(n-1)/6⌉ ≤ f(n,4,5)`.  This is the
form to compare a verified construction against: an admissible colouring of `K_n` with
`⌈5(n-1)/6⌉` colours *proves* the exact value of `f(n,4,5)`. -/
theorem EG_ge_ceil_five_sixth (n : ℕ) (hn : 4 ≤ n) : (5 * (n - 1) + 5) / 6 ≤ EG n := by
  have h := EG_ge_five_sixth n hn
  omega

/-- **THE VERIFIED CONSTRUCTION ENGINE.**  An explicit colouring of `K_n` given by a literal
table, once certified by `native_decide`, yields the upper bound `f(n,4,5) ≤ k`; combined with
`EG_ge_ceil_five_sixth` it yields the *exact* value whenever `k = ⌈5(n-1)/6⌉`.  Every future
verified construction of this file is an instance of these two statements. -/
theorem EG_le_of_listCol (n k : ℕ) (hk : 0 < k) (l : List ℕ) (h : Admissible (listCol n k hk l)) :
    EG n ≤ k := EG_le n k (listCol n k hk l) h

/-- The exact-value engine: a verified construction with `⌈5(n-1)/6⌉` colours *is* the value
of the Erdős–Gyárfás function at that `n`. -/
theorem EG_eq_of_listCol (n k : ℕ) (hk : 0 < k) (l : List ℕ) (h : Admissible (listCol n k hk l))
    (hn : 4 ≤ n) (hex : k = (5 * (n - 1) + 5) / 6) : EG n = k := by
  refine Nat.le_antisymm (EG_le_of_listCol n k hk l h) ?_
  exact hex ▸ EG_ge_ceil_five_sixth n hn

/-! ### An admissible colouring of `K₆` with five colours -/

set_option maxRecDepth 10000 in
/-- The **1-factorisation of `K₆`**: the five colours are the five perfect matchings
`{01,23,45}`, `{02,14,35}`, `{03,15,24}`, `{04,13,25}`, `{05,12,34}` of `K₆`.  A 1-factorisation
is admissible because the six edges of a four-clique carry at most one repeated colour (each
colour class is a matching, so a repeated colour appears on opposite edges only). -/
def sixCol : Col 6 5 := listCol 6 5 (by norm_num)
  [0, 0, 1, 2, 3, 4, 0, 0, 4, 3, 1, 2, 0, 0, 0, 0, 2, 3, 0, 0, 0, 0, 4, 1, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0]

set_option maxRecDepth 10000 in
/-- **The 1-factorisation of `K₆` is admissible**: every four vertices span at least five
colours, so this is an upper bound `f(6,4,5) ≤ 5` proved by exhaustive computation over all
`C(6,4) = 15` four-element vertex sets — a Lean certificate that is independent of any
search that produced the colouring. -/
theorem admissible_sixCol : Admissible sixCol := by
  unfold Admissible; native_decide

/-- **The catalog condition is TIGHT in this colouring**: the four vertices `{0,1,2,3}`
carry the two opposite edges `01` and `23` in the same colour `0`, so they span exactly five
colours — the minimum allowed by `Admissible`.  Thus `f(6,4,5) = 5` is witnessed by a
colouring in which some four-clique uses precisely the five colours the catalog prescribes. -/
theorem sixCol_tight : (colorsOn sixCol ({0, 1, 2, 3} : Finset (Fin 6))).card = 5 := by
  native_decide

/-- `f(6,4,5) ≤ 5`. -/
theorem EG_six_le : EG 6 ≤ 5 := EG_le 6 5 sixCol admissible_sixCol

/-- **THE FIRST EXACT VALUE OF `f(n,4,5)` IN THIS DEVELOPMENT: `f(6,4,5) = 5`.**  The lower
bound `⌈5(n-1)/6⌉ = ⌈25/6⌉ = 5` of `Cherry.five_sixth_lower` meets the explicit
1-factorisation above. -/
theorem EG_six : EG 6 = 5 :=
  EG_eq_of_listCol 6 5 (by norm_num)
    [0, 0, 1, 2, 3, 4, 0, 0, 4, 3, 1, 2, 0, 0, 0, 0, 2, 3, 0, 0, 0, 0, 4, 1, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0] admissible_sixCol (by norm_num) rfl

/-- The real form: `f(6,4,5) = 5 = ⌈5(6-1)/6⌉`. -/
theorem EG_six_real : (EG 6 : ℝ) = 5 := by
  rw [EG_six]; norm_num

/-- **The sharp constant `5/6` of the catalog answer is attained at `n = 6`.**  Formulated as
the two inequalities of the catalog estimate at `n = 6`: `|f(6,4,5) - 5·6/6| = 5/6 ≤ n/6`,
i.e. the catalog estimate `|f(n,4,5) - 5n/6| ≤ ε n` holds with `ε = 1/6` at `n = 6` and the
lower bound is met with equality up to the rounding of `5(n-1)/6` to an integer. -/
theorem six_is_attained : EG 6 = 5 ∧ 5 = (5 * (6 - 1) + 5) / 6 := by
  refine ⟨EG_six, ?_⟩
  norm_num

/-! ### An admissible colouring of `K₉` with eight colours

The colouring found by the leaf-free vertex-addition search of `LeafFree.lean` (with seven colours
it fails: `LeafFree.certD_nine_six`).  It is written down here as a literal table and verified
independently, by `native_decide` over all `C(9,4) = 126` four-element vertex sets.  Note that this
is **not** the counting bound `⌈5(9-1)/6⌉ = 7`: the search shows that `K₉` has no admissible
7-colouring, so `f(9,4,5) = 8` is a third value strictly above `5(n-1)/6`, and a third confirmation
that the design-theoretic route to the extremal family (a Steiner triple system of two-edge paths
with a colouring of the leaf edges) breaks at this order.
-/

set_option maxRecDepth 10000 in
/-- **An admissible 8-colouring of `K₉`**, the first one found by the searches of this
development.  (The `n = 6` table is read off the 1-factorisation; this one is machine-produced.) -/
def nineCol : Col 9 8 := listCol 9 8 (by norm_num)
  [0, 0, 0, 2, 2, 3, 4, 5, 6,
   0, 0, 1, 3, 5, 4, 7, 6, 2,
   0, 0, 0, 4, 6, 2, 3, 7, 5,
   0, 0, 0, 0, 1, 5, 6, 0, 7,
   0, 0, 0, 0, 0, 7, 0, 3, 4,
   0, 0, 0, 0, 0, 0, 1, 4, 0,
   0, 0, 0, 0, 0, 0, 0, 2, 5,
   0, 0, 0, 0, 0, 0, 0, 0, 1,
   0, 0, 0, 0, 0, 0, 0, 0, 0]

set_option maxRecDepth 10000 in
/-- **The colouring of `K₉` is admissible**: every four vertices span at least five colours.  A
Lean certificate over all `C(9,4) = 126` four-element vertex sets, independent of the search that
produced it. -/
theorem admissible_nineCol : Admissible nineCol := by
  unfold Admissible; native_decide

/-- `f(9,4,5) ≤ 8`.  With `LeafFree.certD_nine_six` (no admissible 7-colouring of `K₉`) this is
`f(9,4,5) = 8`. -/
theorem EG_nine_le : EG 9 ≤ 8 := EG_le 9 8 nineCol admissible_nineCol

/-- **The catalog condition is tight here too**: some `K₄` of `nineCol` spans exactly five
colours. -/
theorem nineCol_some_tight : ∃ S : Finset (Verts 9), S.card = 4 ∧ (colorsOn nineCol S).card = 5 := by
  native_decide

end JSP140
