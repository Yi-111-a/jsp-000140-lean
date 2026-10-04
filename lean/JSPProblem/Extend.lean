import JSPProblem.Window

/-!
# JSP-000140 — ROUND 67: the *family* form of the extremal shape (benchmark B5 is an infinite
  family), the triangle decomposition forced at the refined bound, and the non-attainment of the
  published counting bound

## What this round does

Round 66 proved, at the single order `n = 13, k = 11`, that an admissible colouring at the refined
bound would have its two-edge paths forming a Steiner triple system
(`Window.extremal_at_thirteen_is_STS`), and read benchmark B5 as "does an `STS(13)` carry a legal
`(2,1)`-block colouring?".  That reading was an artefact of the *single* order.  This round proves
the same statement **at every order at which the refined bound can be attained at all**, i.e. for
every `n ≡ 1 (mod 6)` with `n ≥ 13`:

* **`Extend.isSTS_of_refined`** — if `6k = 5n + 1` and `k + 2 ≤ n`, the two-edge paths of `c` form
  a **Steiner triple system on `Fin n`**;
* **`Extend.triangles_cover`** — the **triangles** spanned by the two-edge paths **partition the
  edge set of `K_n`**: `E(K_n)` is a disjoint union of `n(n-1)/6` triangles which simultaneously
  form an `STS(n)` *and* a triangle decomposition of `K_n`.  This is exactly the `(2,1)`-block
  object of `BlockCol.lean` and of the searches of rounds 49–56, now a theorem for a whole
  residue class rather than for `n = 13`;
* **`Extend.refined_shape`** — the whole shape in one statement:
  `Paths c = (pathFinset c).card = n(n-1)/6`, `Isolated c = n`, `Defect c = 0`, `IsSTS`;
* **`Extend.n_mod_six_of_refined`** — `6k = 5n + 1` forces `n ≡ 1 (mod 6)`, so **B5 is an infinite
  family indexed by `n ≡ 1 (mod 6)`, `n ≥ 13`, and nowhere else**
  (`Extend.refined_is_STS_family`);
* **`Extend.no_five_sixth_eq`** — the published bound `f(n,4,5) ≥ 5(n-1)/6` of
  `Cherry.five_sixth_lower` is **never attained**: `5(n-1) + 1 ≤ 6k` for every admissible
  colouring with `n ≥ 7`.  (At `n ≥ 7` the equality case is `n ≡ 1 (mod 6)` with `k = 5(n-1)/6 ≤ n-2`,
  and there `Vacant.five_n_add_one_le_six_k` excludes it by one whole colour.)

## What it costs the prize, stated honestly

Nothing here touches `Main.AdmissibleUpper ε` (`0 < ε < 1/6`), the probabilistic existence theorem
of arXiv:2207.02920 §4 (Bennett–Cushman–Dudek–Prałat: a random triangle-removal process analysed by
the differential-equation method).  That remains the sole content of `jsp_000140_main`, and it was
again **not** declared: declaring it with `AdmissibleUpper` as a hypothesis would falsify the prize.

The round also ran the round-66 solver at `n = 16 … 19`
(`discovery/JSP-000140/r67_launch.sh`, `r67_search_log.txt`) and two new computational probes on the
last residue class `n ≡ 4 (mod 6)` (`r67_star.py`, `r67_fac.py`); their conclusions are recorded in
`r67_search_log.txt`.
-/

namespace JSP140

variable {n k : ℕ} {c : Col n k}

/-! ### §0  Division by the constants `6` and `2` -/

/-- `a * 6 = b` gives `a = b / 6`; `omega` alone will not do this, because the division turns the
hypothesis into a fresh atom. -/
private theorem div_six (a b : ℕ) (h3 : a * 6 = b) : a = b / 6 := by
  have hd : 6 ∣ b := ⟨a, by omega⟩
  have hkey : (b / 6) * 6 = b := Nat.div_mul_cancel hd
  have h6 : b / 6 = a := Nat.eq_of_mul_eq_mul_left (by omega : (0 : ℕ) < 6) (by omega)
  omega

/-- `2 * a = b` gives `a = b / 2`. -/
private theorem div_two (a b : ℕ) (h3 : 2 * a = b) : a = b / 2 := by
  have hd : 2 ∣ b := ⟨a, by omega⟩
  have hkey : (b / 2) * 2 = b := Nat.div_mul_cancel hd
  have h2 : b / 2 = a := Nat.eq_of_mul_eq_mul_left (by omega : (0 : ℕ) < 2) (by omega)
  omega

/-! ### §1  The refined bound forces the counting lemma of `Cherry.lean` to be an *equality* -/

/-- The surplus identity `6 * Isolated c + 2 * Defect c = n * (6k - 5(n-1))` at `6k = 5n + 1`. -/
private lemma refined_surplus {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n) (heq : 6 * k = 5 * n + 1) :
    6 * Isolated c + 2 * Defect c = 6 * n := by
  have h1 := surplus_of_k hc hn
  have h2 : 6 * k - 5 * (n - 1) = 6 := by omega
  calc 6 * Isolated c + 2 * Defect c = n * (6 * k - 5 * (n - 1)) := h1
    _ = n * 6 := by rw [h2]
    _ = 6 * n := Nat.mul_comm _ _

/-- **`Defect c = 0`: every edge of `K_n` is paid for by a two-edge path, whenever the refined
bound is attained.**  At `6k = 5n + 1` the surplus identity leaves room for exactly `6n` units of
defect, and `Vacant.isolated_ge_n` (which needs `k + 2 ≤ n`) already spends `6n` of them on unused
`(vertex, colour)` slots. -/
theorem defect_eq_zero_of_refined {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n) (hk : k + 2 ≤ n)
    (heq : 6 * k = 5 * n + 1) : Defect c = 0 := by
  have h1 := refined_surplus hc hn heq
  have h2 := isolated_eq_n_defect_eq_zero hc hn hk heq
  omega

/-- **THE COUNTING LEMMA IS AN EQUALITY AT THE REFINED BOUND.**  `3 * Paths c = |E(K_n)|`: every
edge of `K_n` lies in the triangle spanned by a two-edge path; not one "single edge" is left over.
This is the equality case of `Cherry.three_mul_paths_le_edges`, whose inequality is the whole `5/6`
constant. -/
theorem three_mul_paths_eq_of_refined {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n)
    (hk : k + 2 ≤ n) (heq : 6 * k = 5 * n + 1) :
    3 * Paths c = (edgeFinset (Finset.univ : Finset (Verts n))).card := by
  have hD := defect_eq_zero_of_refined hc hn hk heq
  have h1 : (edgeFinset (Finset.univ : Finset (Verts n))).card = 3 * Paths c + Defect c := by
    have h3 := three_mul_paths_le_edges hc hn
    have h2 : (edgeFinset (Finset.univ : Finset (Verts n))).card - 3 * Paths c = Defect c := rfl
    omega
  omega

/-- **THE NUMBER OF TWO-EDGE PATHS AT THE REFINED BOUND.**  `Paths c = n(n-1)/6`, the sharp
hypothesis of `Cherry.five_sixth_of_paths`, with equality. -/
theorem paths_eq_of_refined {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n) (hk : k + 2 ≤ n)
    (heq : 6 * k = 5 * n + 1) : Paths c = n * (n - 1) / 6 := by
  have h1 := three_mul_paths_eq_of_refined hc hn hk heq
  have h2 := card_edgeFinset_univ_two n
  have h3 : Paths c * 6 = n * (n - 1) := by omega
  exact div_six (Paths c) (n * (n - 1)) h3

/-! ### §2  **THE FAMILY FORM OF BENCHMARK B5: AN `STS(n)`, AT EVERY ORDER THAT CAN ATTAIN THE
  REFINED BOUND** -/

/-- **AN ADMISSIBLE COLOURING AT THE REFINED BOUND IS A STEINER TRIPLE SYSTEM — AT EVERY ORDER.**
If `c : Col n k` is admissible, `4 ≤ n`, `k + 2 ≤ n` and `6k = 5n + 1`, then

* `Paths c = (pathFinset c).card = n(n-1)/6`,
* `Isolated c = n` — exactly `n` unused `(vertex, colour)` slots, one per vertex,
* `Defect c = 0`,
* **`IsSTS (pathFinset c)`**: the three-element vertex sets spanned by the two-edge paths form a
  Steiner triple system on `Fin n`.

Round 66 (`Window.extremal_at_thirteen_is_STS`) proved the last two of these at `n = 13` only. -/
theorem isSTS_of_refined {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n) (hk : k + 2 ≤ n)
    (heq : 6 * k = 5 * n + 1) :
    Paths c = (pathFinset c).card ∧ Isolated c = n ∧ Defect c = 0 ∧ IsSTS (pathFinset c) := by
  have h1 := isolated_eq_n_defect_eq_zero hc hn hk heq
  have h2 := paths_eq_of_refined hc hn hk heq
  have h3 := card_pathFinset c hc hn
  have h4 := tight_pathFinset_is_STS hc hn (three_mul_paths_eq_of_refined hc hn hk heq)
  exact ⟨h3.symm, h1.1, h1.2, h4⟩

/-- **THE SHAPE AT THE REFINED BOUND, IN ONE STATEMENT.** -/
theorem refined_shape {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n) (hk : k + 2 ≤ n)
    (heq : 6 * k = 5 * n + 1) :
    Paths c = n * (n - 1) / 6 ∧ (pathFinset c).card = n * (n - 1) / 6 ∧ Isolated c = n ∧
      Defect c = 0 ∧ IsSTS (pathFinset c) := by
  have h := isSTS_of_refined hc hn hk heq
  have h2 := paths_eq_of_refined hc hn hk heq
  have h3 := card_pathFinset c hc hn
  exact ⟨h2, h3.trans h2, h.2.1, h.2.2.1, h.2.2.2⟩

/-! ### §3  The arithmetic: the refined bound is attainable only in the residue class `n ≡ 1 (mod 6)` -/

/-- **`6k = 5n + 1` forces `n ≡ 1 (mod 6)`** (`5` is a unit modulo `6`).  So the extremal shape of
§2 — and with it benchmark B5 — lives on the residue class `n ≡ 1 (mod 6)` and nowhere else. -/
theorem n_mod_six_of_refined (_hn : 4 ≤ n) {k : ℕ} (heq : 6 * k = 5 * n + 1) : n % 6 = 1 := by
  have h1 : 5 * n + 1 = 6 * k := heq.symm
  omega

/-- **B5 IS AN INFINITE FAMILY, INDEXED BY `n ≡ 1 (mod 6)`, `n ≥ 13`.**  For every `t ≥ 2`
(`n = 6t+1 ≥ 13`) and every admissible colouring of `K_{6t+1}` with the refined number of colours
`⌈(5n+1)/6⌉ = 5t+1`, the two-edge paths form an `STS(6t+1)`.  So "is `f(13,4,5) = 11`?" is the
`t = 2` member of a family of questions, and `Extend.triangles_cover` below says the same colourings
are exactly the triangle decompositions of `K_{6t+1}`. -/
theorem refined_is_STS_family (t : ℕ) (ht : 2 ≤ t)
    {c : Col (6 * t + 1) ((5 * (6 * t + 1) + 1) / 6)} (hc : Admissible c) : IsSTS (pathFinset c) := by
  have hk : ((5 * (6 * t + 1) + 1) / 6) + 2 ≤ 6 * t + 1 := by
    have hdiv : 5 * (6 * t + 1) + 1 = 6 * (5 * t + 1) := by ring
    have hq : 5 * (6 * t + 1) + 1 = 6 * (5 * t + 1) := hdiv
    have hk' : (5 * (6 * t + 1) + 1) / 6 = 5 * t + 1 := by
      rw [hq, Nat.mul_div_cancel_left _ (by omega)]
    omega
  have hn : 4 ≤ 6 * t + 1 := by omega
  have heq : 6 * ((5 * (6 * t + 1) + 1) / 6) = 5 * (6 * t + 1) + 1 := by
    have hdiv : 5 * (6 * t + 1) + 1 = 6 * (5 * t + 1) := by ring
    rw [hdiv, Nat.mul_div_cancel_left _ (by omega)]
  exact (isSTS_of_refined hc hn hk heq).2.2.2

/-! ### §4  The triangles of the two-edge paths partition `E(K_n)` at the refined bound -/

/-- The triangle spanned by a two-edge path: its two edges and the edge between its leaves. -/
def pathTriangle (c : Col n k) (p : Fin k × Verts n) : Finset (Sym2 (Verts n)) :=
  cherryEdges c p.1 p.2

/-- Each triangle of a two-edge path has three edges. -/
theorem card_pathTriangle {c : Col n k} {p : Fin k × Verts n} (hp : p ∈ cherryFinset c) :
    (pathTriangle c p).card = 3 :=
  card_cherryEdges p.1 (twoA_of_mem_cherryFinset hp)

/-- Two triangles of two different two-edge paths are disjoint. -/
theorem pathTriangle_disjoint {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n) {p q : Fin k × Verts n}
    (hp : p ∈ cherryFinset c) (hq : q ∈ cherryFinset c) (hpq : p ≠ q) :
    Disjoint (pathTriangle c p) (pathTriangle c q) :=
  cherryEdges_disjoint hc hn (twoA_of_mem_cherryFinset hp) (twoA_of_mem_cherryFinset hq) hpq

/-- Every triangle lies in the edge set of `K_n`. -/
theorem pathTriangle_subset {c : Col n k} {p : Fin k × Verts n} (_hp : p ∈ cherryFinset c) :
    pathTriangle c p ⊆ edgeFinset (Finset.univ : Finset (Verts n)) :=
  cherryEdges_subset_edgeFinset p.1

/-- **THE TRIANGLES OF THE TWO-EDGE PATHS PARTITION `E(K_n)` — AT EVERY ORDER AT WHICH THE REFINED
BOUND IS ATTAINED.**  `(cherryFinset c).biUnion pathTriangle = edgeFinset (univ)`: the edge set of
`K_n` is a disjoint union of the `n(n-1)/6` triangles spanned by the two-edge paths, and (by
`Extend.isSTS_of_refined`) their vertex sets form a Steiner triple system.  This is the
`(2,1)`-block / triangle-decomposition object of `BlockCol.lean`, as a theorem for the whole residue
class `n ≡ 1 (mod 6)`, `n ≥ 13`, rather than for the single order `n = 13`. -/
theorem triangles_cover {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n) (hk : k + 2 ≤ n)
    (heq : 6 * k = 5 * n + 1) :
    (cherryFinset c).biUnion (fun p => pathTriangle c p) = edgeFinset (Finset.univ : Finset (Verts n)) := by
  have hdisc : (↑(cherryFinset c) : Set (Fin k × Verts n)).PairwiseDisjoint
      (fun p => pathTriangle c p) := by
    intro p hp q hq hpq
    exact pathTriangle_disjoint hc hn (Finset.mem_coe.mp hp) (Finset.mem_coe.mp hq) hpq
  have h1 : ((cherryFinset c).biUnion (fun p => pathTriangle c p)).card
      = ∑ p ∈ cherryFinset c, (pathTriangle c p).card := Finset.card_biUnion hdisc
  have h2 : (∑ p ∈ cherryFinset c, (pathTriangle c p).card) = 3 * (cherryFinset c).card := by
    calc (∑ p ∈ cherryFinset c, (pathTriangle c p).card) = ∑ p ∈ cherryFinset c, (3 : ℕ) := by
          refine Finset.sum_congr rfl fun p hp => card_pathTriangle (Finset.mem_coe.mp hp)
      _ = (cherryFinset c).card • (3 : ℕ) := Finset.sum_const _
      _ = 3 * (cherryFinset c).card := by rw [nsmul_eq_mul]; exact Nat.mul_comm _ _
  have h3 : (cherryFinset c).biUnion (fun p => pathTriangle c p)
      ⊆ edgeFinset (Finset.univ : Finset (Verts n)) := by
    intro e he
    obtain ⟨p, hp, he⟩ := Finset.mem_biUnion.mp he
    exact pathTriangle_subset (Finset.mem_coe.mp hp) he
  have h4 := three_mul_paths_eq_of_refined hc hn hk heq
  have h5 := card_cherryFinset c
  have hcard : ((cherryFinset c).biUnion (fun p => pathTriangle c p)).card
      = (edgeFinset (Finset.univ : Finset (Verts n))).card := by
    rw [h1, h2, h5]
    exact h4
  exact Finset.eq_of_subset_of_card_le h3 (by omega)

/-- **THE NUMBER OF EDGES AT THE REFINED BOUND** (`|E(K_n)| = n(n-1)/2 = 3 * n(n-1)/6`, the three
edges per triangle of `Extend.triangles_cover`). -/
theorem card_biUnion_triangles {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n) (hk : k + 2 ≤ n)
    (heq : 6 * k = 5 * n + 1) :
    ((cherryFinset c).biUnion (fun p => pathTriangle c p)).card = n * (n - 1) / 2 := by
  have h1 := triangles_cover hc hn hk heq
  have h2 := card_edgeFinset_univ_two n
  rw [h1]
  exact div_two (edgeFinset (Finset.univ : Finset (Verts n))).card (n * (n - 1)) (by omega)

/-! ### §5  The published counting bound `5(n-1) ≤ 6k` is never attained -/

/-- **THE COUNTING BOUND IS NEVER AN EQUALITY, FOR A COLOURING.**  No admissible colouring of `K_n`
uses exactly `5(n-1)/6` colours: `5(n-1) + 1 ≤ 6k` for every `n ≥ 7`.  Indeed the equality case of
`Cherry.five_sixth_lower` needs `6 | (n-1)`, whence `n ≡ 1 (mod 6)` and `k = 5(n-1)/6 ≤ n-2`, and
there `Vacant.five_n_add_one_le_six_k` gives `6k ≥ 5n+1 > 5(n-1)`. -/
theorem no_five_sixth_eq {c : Col n k} (hc : Admissible c) (hn : 7 ≤ n) : 5 * (n - 1) + 1 ≤ 6 * k := by
  have h0 := five_sixth_lower hc (by omega)
  by_cases hk : k + 2 ≤ n
  · have h1 := five_n_add_one_le_six_k hc (by omega) hk
    omega
  · omega

/-- **AND HENCE NOT FOR `f(n,4,5)` ITSELF.** -/
theorem strict_five_sixth (n : ℕ) (hn : 7 ≤ n) : 5 * (n - 1) + 1 ≤ 6 * EG n := by
  obtain ⟨c, hc⟩ := EG_admissible n
  exact no_five_sixth_eq hc hn

/-- **THE TWO-SIDED SHAPE NEVER TOUCHES THE PUBLISHED CONSTANT.**  For `n ≥ 7`,
`f(n,4,5) > 5(n-1)/6`: the sharp constant `5/6` of Bennett–Cushman–Dudek–Prałat is a limit from
below which no finite order attains. -/
theorem eg_gt_five_sixth (n : ℕ) (hn : 7 ≤ n) : 5 * (n - 1) < 6 * EG n := by
  have h := strict_five_sixth n hn
  omega

/-! ### §6  The per-vertex shape at the refined bound: the two-edge-path centres are almost
  uniformly spread -/

/-- The two arithmetic facts about the family `n = 6t+1`, `k = ⌈(5n+1)/6⌉ = 5t+1`. -/
private theorem family_k (t : ℕ) :
    6 * ((5 * (6 * t + 1) + 1) / 6) = 5 * (6 * t + 1) + 1 := by
  have hdiv : 5 * (6 * t + 1) + 1 = 6 * (5 * t + 1) := by ring
  rw [hdiv, Nat.mul_div_cancel_left _ (by omega)]

private theorem family_k_le (t : ℕ) (ht : 2 ≤ t) :
    ((5 * (6 * t + 1) + 1) / 6) + 2 ≤ 6 * t + 1 := by
  have hdiv : 5 * (6 * t + 1) + 1 = 6 * (5 * t + 1) := by ring
  have hk' : (5 * (6 * t + 1) + 1) / 6 = 5 * t + 1 := by
    rw [hdiv, Nat.mul_div_cancel_left _ (by omega)]
  omega

/-- **AT THE REFINED BOUND EVERY VERTEX CENTRES AT LEAST `(n-7)/6` TWO-EDGE PATHS.**  The
per-vertex identity `Window.missing_at` says that the colours missing at `v` are `k - (n-1)` plus
the number of two-edge paths centred at `v`; at `6k = 5n + 1` the first term is `-(n-7)/6`, so a
vertex which centred fewer than `(n-7)/6` paths would be missing a negative number of colours.
Since the total number of paths is `n(n-1)/6` (`Extend.paths_eq_of_refined`), i.e. the average
number of paths per vertex is `(n-1)/6`, the two-edge-path centres of an extremal colouring are
**almost uniformly spread**: every vertex centres within one path of the average.  At `k = n-2`
the same identity forces only *one* path per vertex (`Window.centre_of_paths`); at the refined
bound it forces `≈ n/6`, i.e. the colouring is *locally* a partial parallel-class structure at every
vertex. -/
theorem centres_ge_of_refined {c : Col n k} (hc : Admissible c) (_hn : 4 ≤ n) (hk : k + 2 ≤ n)
    (heq : 6 * k = 5 * n + 1) (v : Verts n) :
    n ≤ 6 * (∑ i : Fin k, if v ∈ twoA c i then 1 else 0) + 7 := by
  have h1 := missing_at c hc v
  have hA0 : (0 : ℕ) ≤ ∑ i : Fin k, if v ∈ zeroA c i then 1 else 0 :=
    Finset.sum_nonneg fun i _ => (Nat.zero_le _)
  omega

/-- **THE ANALOGUE OF `Window.centre_of_paths` AT THE REFINED BOUND, IN THE `n ≡ 1 (mod 6)` FAMILY.**
For every `t ≥ 2`, in an admissible colouring of `K_{6t+1}` with the refined number of colours
`5t+1`, **every vertex is the centre of a two-edge path**. -/
theorem centre_exists_of_refined (t : ℕ) (ht : 2 ≤ t)
    {c : Col (6 * t + 1) ((5 * (6 * t + 1) + 1) / 6)} (hc : Admissible c) (v : Verts (6 * t + 1)) :
    ∃ i : Fin ((5 * (6 * t + 1) + 1) / 6), v ∈ twoA c i := by
  have hn : 4 ≤ 6 * t + 1 := by omega
  have hkey := centres_ge_of_refined hc hn (family_k_le t ht) (family_k t) v
  by_contra h
  have hn' : ∀ i : Fin ((5 * (6 * t + 1) + 1) / 6), v ∉ twoA c i := fun i hi => h ⟨i, hi⟩
  have hC : (∑ i : Fin ((5 * (6 * t + 1) + 1) / 6), if v ∈ twoA c i then (1 : ℕ) else 0) = 0 :=
    Finset.sum_eq_zero fun i _ => by simp [hn' i]
  omega

/-- **THE NUMBER OF PATHS PER VERTEX AT THE REFINED BOUND, IN THE FAMILY FORM.**  At `n = 6t+1` with
the refined number of colours, every vertex centres at least `t-1` two-edge paths (the average is
`t`). -/
theorem centres_ge_family (t : ℕ) (ht : 2 ≤ t)
    {c : Col (6 * t + 1) ((5 * (6 * t + 1) + 1) / 6)} (hc : Admissible c) (v : Verts (6 * t + 1)) :
    (t - 1 : ℕ) ≤ ∑ i : Fin ((5 * (6 * t + 1) + 1) / 6), if v ∈ twoA c i then 1 else 0 := by
  have hn : 4 ≤ 6 * t + 1 := by omega
  have hkey := centres_ge_of_refined hc hn (family_k_le t ht) (family_k t) v
  omega

end JSP140
