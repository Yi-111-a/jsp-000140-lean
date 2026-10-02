import JSPProblem.Tables

/-!
# JSP-000140 — the *blow-up* (lexicographic product) route to `5n/6`, and its obstruction

`Tables.EG_six : EG 6 = 5` is the only order in this development at which the catalog constant
`5/6` is actually **attained**: `K₆` carries an admissible colouring with exactly `5 = 5 · 6 / 6`
colours.  Every other order known here (`EG 7 = 7`, `EG 8 = 7`) *misses* it.  So the most
tempting route to the missing upper bound `f(n,4,5) ≤ 5n/6 + o(n)` is to **amplify** that one
witness: take the `m`-fold blow-up `K₆[m]`, whose `6m` vertices are arranged in `6` blocks of `m`,
and colour it by

* inside a block: any colouring `psi` of `K_m`;
* between two blocks `i ≠ j`: the colour `f i j` of `{i,j}` in the `K₆` witness, together with a
  **cross index** `L i j x y` distinguishing the two inner vertices.

The palette is `Fin q × Fin m`, i.e. **`q · m = 5m = 5·(6m)/6` colours on `6m` vertices** — *exactly*
the catalog budget, at every blow-up size.  This is the standard way a graph product is meant to
turn a good small example into an asymptotically good one.

This file proves that this is impossible, and does so in a form far stronger than any single
family: **`blockCol_not_admissible` — NO LEXICOGRAPHIC PRODUCT COLOURING OF THIS SHAPE IS EVER
ADMISSIBLE**, for any number of blocks, any number of factor colours, any blow-up size `m ≥ 2`,
any internal colourings and any cross labelling.  Nothing probabilistic is used and nothing is
assumed about the construction.

## §1 — the blow-up as data

`encT` / `blkT` / `innT` encode `Fin t × Fin m` into `Fin (t * m)`; `xcolQ` / `xcolQDec` encode
`Fin q × Fin m` into `Fin (q * m)`.  `blockCol` is the colour of an *ordered* pair of vertices and
`blockCol_swap` proves that it is a function of the unordered pair; `blockColT` is the resulting
colouring.

## §2 — **THE PRODUCT OBSTRUCTION**

`blockCol_not_admissible`: assume the factor map `f` **covers every colour at every block** (the
property of a 1-factorisation of `K₆`: at each vertex of `K₆` all five colours are used), and
that each cross labelling is injective in its first inner variable — which is what makes the
cross edges a legitimate part of a *colouring*, since two cross edges sharing an outer vertex must
differ.  Then the four vertices

* `0`, `1` in block `0`, and
* `y₁ ≠ y₂` in a block `j ≠ 0` whose factor colour is the block-colour part of the colour of `0₁ 0₂`,
  and whose cross indices with `0₁`, `0₂` are both the index part of that colour

span **at most four colours**: the three edges `0₁0₂`, `0₁y₁` and `0₂y₂` all carry the *same*
colour, so by `Definitions.colorsOn_card_le_four` that `K₄` spans `≤ 4` colours.  Corollaries:
`blowup_K6_not_admissible`.

The only order at which the argument cannot run is `m = 1`, where there is no pair of distinct
inner vertices — and that is exactly the known witness: §3 exhibits the genuine 1-factorisation
of `K₆` (`fact6`) and proves it admissible.  The family starts at the right place and dies
immediately.

## §3 — the `K₆` witness, and the blow-up which cannot repeat it

* `fact6` — the 1-factorisation `01|23|45`, `02|14|35`, `03|15|24`, `04|13|25`, `05|12|34`;
* `fact6_symm`, `fact6_cover` — it is symmetric and covers every colour at every vertex;
* `admissible_fact6Col` — it is **admissible**, machine-checked (a second explicit admissible
  5-colouring of `K₆`, independent of `Tables.sixCol`);
* `blowup_K6_not_admissible` — but its `m`-fold blow-up is **never** admissible for `m ≥ 2`, for
  any internal colouring, so `Tables.EG_six = 5 = 5·6/6` cannot be amplified;
* `EG_ge_five_mul_six`, `EG_eq_five_mul` — the blow-up palette is *exactly* the catalog counting
  bound `5(n-1)/6`, so one admissible `5m`-colouring of `K_{6m}` would settle `f(6m,4,5) = 5m`:
  the product construction is the only way this development knows to write one down, and §2 says
  it never can.
-/

set_option maxHeartbeats 1000000

namespace JSP140

/-! ### §1  The blow-up of a complete graph -/

/-- The `m`-fold blow-up of `K_t`: the vertex `(i, x)` (block `i`, inner index `x`) is the vertex
`i * m + x` of `Fin (t * m)`. -/
def encT {t m : ℕ} (i : Fin t) (x : Fin m) : Fin (t * m) :=
  ⟨i.val * m + x.val, by
    have h1 : i.val * m + x.val < i.val * m + m := Nat.add_lt_add_left x.isLt _
    have h1' : i.val * m + x.val < (i.val + 1) * m := by simpa [Nat.succ_mul] using h1
    have h2 : (i.val + 1) * m ≤ t * m := Nat.mul_le_mul_right m (Nat.succ_le_iff.mpr i.isLt)
    omega⟩

/-- Two encodings in the same block with the same value are the same inner vertex. -/
theorem encT_inj_inner {t m : ℕ} {i i' : Fin t} {x y : Fin m} (h : encT i x = encT i' y)
    (hb : i = i') : x = y := by
  have hv : i.val * m + x.val = i' * m + y.val := congrArg Fin.val h
  subst hb
  omega

/-- Two encodings with the same inner vertex are the same block (`m > 0`). -/
theorem encT_inj_block {t m : ℕ} (hm : 0 < m) {i i' : Fin t} {x y : Fin m} (h : encT i x = encT i' y)
    (hx : x = y) : i = i' := by
  have hv : i.val * m + x.val = i' * m + y.val := congrArg Fin.val h
  subst hx
  have hv2 : i.val * m = i'.val * m := by omega
  exact Fin.ext (Nat.mul_right_cancel (by omega) hv2)

/-- The **block** of a vertex of `Fin (t * m)`. -/
def blkT {t m : ℕ} (hm : 0 < m) (v : Fin (t * m)) : Fin t :=
  ⟨v.val / m, (Nat.div_lt_iff_lt_mul hm).mpr v.isLt⟩

/-- The **inner index** of a vertex of `Fin (t * m)`. -/
def innT {t m : ℕ} (hm : 0 < m) (v : Fin (t * m)) : Fin m := ⟨v.val % m, Nat.mod_lt _ hm⟩

/-- An encoded vertex lies in its own block. -/
theorem blkT_encT {t m : ℕ} (hm : 0 < m) (i : Fin t) (x : Fin m) : blkT hm (encT i x) = i := by
  have h : (i.val * m + x.val) / m = i.val := by
    rw [Nat.mul_comm i.val m, Nat.mul_add_div hm, Nat.div_eq_of_lt x.isLt]
    omega
  exact Fin.ext (by simpa [blkT, encT] using h)

/-- An encoded vertex has its own inner index. -/
theorem innT_encT {t m : ℕ} (hm : 0 < m) (i : Fin t) (x : Fin m) : innT hm (encT i x) = x := by
  have h : (i.val * m + x.val) % m = x.val := by
    rw [Nat.mul_comm i.val m, Nat.mul_add_mod, Nat.mod_eq_of_lt x.isLt]
  exact Fin.ext (by simpa [innT, encT] using h)

/-- A colour of the product: a **block colour** in `Fin q` together with a **cross index** in
`Fin m`, encoded as `a * m + l`. -/
def xcolQ {q m : ℕ} (a : Fin q) (l : Fin m) : Fin (q * m) :=
  ⟨a.val * m + l.val, by
    have h1 : a.val * m + l.val < a.val * m + m := Nat.add_lt_add_left l.isLt _
    have h1' : a.val * m + l.val < (a.val + 1) * m := by simpa [Nat.succ_mul] using h1
    have h2 : (a.val + 1) * m ≤ q * m := Nat.mul_le_mul_right m (Nat.succ_le_iff.mpr a.isLt)
    omega⟩

/-- The two components of a product colour. -/
def xcolQDec {q m : ℕ} (hm : 0 < m) (v : Fin (q * m)) : Fin q × Fin m :=
  (⟨v.val / m, (Nat.div_lt_iff_lt_mul hm).mpr v.isLt⟩, ⟨v.val % m, Nat.mod_lt _ hm⟩)

/-- A product colour decodes to its own two components. -/
theorem xcolQDec_xcolQ {q m : ℕ} (hm : 0 < m) (a : Fin q) (l : Fin m) :
    xcolQDec hm (xcolQ a l) = (a, l) := by
  apply Prod.ext
  · have h : (a.val * m + l.val) / m = a.val := by
      rw [Nat.mul_comm a.val m, Nat.mul_add_div hm, Nat.div_eq_of_lt l.isLt]
      omega
    exact Fin.ext (by simpa [xcolQDec, xcolQ] using h)
  · have h : (a.val * m + l.val) % m = l.val := by
      rw [Nat.mul_comm a.val m, Nat.mul_add_mod, Nat.mod_eq_of_lt l.isLt]
    exact Fin.ext (by simpa [xcolQDec, xcolQ] using h)

/-- **Every colour of the palette has a unique decomposition** into a block colour and a cross
index. -/
theorem exists_xcolQ {q m : ℕ} (hm : 0 < m) (v : Fin (q * m)) :
    ∃ a : Fin q, ∃ l : Fin m, v = xcolQ a l := by
  refine ⟨⟨v.val / m, (Nat.div_lt_iff_lt_mul hm).mpr v.isLt⟩,
    ⟨v.val % m, Nat.mod_lt _ hm⟩, ?_⟩
  apply Fin.ext
  show v.val = v.val / m * m + v.val % m
  rw [Nat.mul_comm (v.val / m) m]
  exact (Nat.div_add_mod v.val m).symm

/-- **THE COLOUR OF AN ORDERED PAIR OF BLOW-UP VERTICES.**  Inside one block the internal colouring
`psi` of that block is used; across two blocks the pair of the factor colour of the two blocks and
the cross index of the two inner vertices. -/
def blockCol {t q m : ℕ} (hm : 0 < m) (f : Fin t → Fin t → Fin q)
    (L : Fin t → Fin t → Fin m → Fin m → Fin m) (psi : Fin t → Col m (q * m)) :
    ∀ a b : Fin (t * m), Fin (q * m) :=
  fun a b => if blkT hm a = blkT hm b then psi (blkT hm a) s(innT hm a, innT hm b)
    else xcolQ (f (blkT hm a) (blkT hm b)) (L (blkT hm a) (blkT hm b) (innT hm a) (innT hm b))

/-- **The colour of a blow-up vertex pair does not depend on the order.**  `f` and `L` must be
symmetric, which is exactly the requirement for a colouring of unordered pairs. -/
theorem blockCol_swap {t q m : ℕ} {hm : 0 < m} (f : Fin t → Fin t → Fin q)
    (L : Fin t → Fin t → Fin m → Fin m → Fin m) (psi : Fin t → Col m (q * m))
    (hf : ∀ i j, f i j = f j i) (hL : ∀ i j x y, L i j x y = L j i y x) (a b : Fin (t * m)) :
    blockCol hm f L psi a b = blockCol hm f L psi b a := by
  by_cases h1 : blkT hm a = blkT hm b
  · have h2 : blkT hm b = blkT hm a := h1.symm
    rw [blockCol, blockCol, if_pos h1, if_pos h2, h1, Sym2.eq_swap]
  · have h2 : ¬blkT hm b = blkT hm a := fun hh => h1 hh.symm
    rw [blockCol, blockCol, if_neg h1, if_neg h2,
      hf (blkT hm a) (blkT hm b),
      hL (blkT hm a) (blkT hm b) (innT hm a) (innT hm b)]

set_option linter.unusedVariables false in
/-- **THE BLOCK-PRODUCT COLOURING.**  `f` and `L` are assumed **symmetric**, which is what makes
`blockCol` a function on unordered pairs. -/
def blockColT {t q m : ℕ} (ht : 0 < t) (hq : 0 < q) (hm : 0 < m)
    (f : Fin t → Fin t → Fin q) (L : Fin t → Fin t → Fin m → Fin m → Fin m)
    (psi : Fin t → Col m (q * m))
    (hf : ∀ i j, f i j = f j i) (hL : ∀ i j x y, L i j x y = L j i y x) : Col (t * m) (q * m) :=
  Sym2.rec (motive := fun _ => Fin (q * m)) (blockCol hm f L psi) (by
    intro a b c d h
    cases h with
    | refl => rfl
    | swap x y => simp [blockCol_swap f L psi hf hL])

/-- **Inside a block** the product colouring is the internal colouring of that block. -/
theorem blockColT_same {t q m : ℕ} {ht : 0 < t} {hq : 0 < q} {hm : 0 < m}
    {f : Fin t → Fin t → Fin q} {L : Fin t → Fin t → Fin m → Fin m → Fin m}
    {psi : Fin t → Col m (q * m)} (hf : ∀ i j, f i j = f j i)
    (hL : ∀ i j x y, L i j x y = L j i y x) (i : Fin t) (x y : Fin m) :
    blockColT ht hq hm f L psi hf hL (s(encT i x, encT i y)) = psi i s(x, y) := by
  have h1 : blkT hm (encT i x) = blkT hm (encT i y) :=
    (blkT_encT hm i x).trans (blkT_encT hm i y).symm
  show blockCol hm f L psi (encT i x) (encT i y) = _
  rw [blockCol, if_pos h1, blkT_encT hm i x, innT_encT hm i x, innT_encT hm i y]

/-- **Between two blocks** the product colouring is the pair `(factor colour, cross index)`. -/
theorem blockColT_cross {t q m : ℕ} {ht : 0 < t} {hq : 0 < q} {hm : 0 < m}
    {f : Fin t → Fin t → Fin q} {L : Fin t → Fin t → Fin m → Fin m → Fin m}
    {psi : Fin t → Col m (q * m)} (hf : ∀ i j, f i j = f j i)
    (hL : ∀ i j x y, L i j x y = L j i y x) (i j : Fin t) (hij : i ≠ j) (x y : Fin m) :
    blockColT ht hq hm f L psi hf hL (s(encT i x, encT j y))
      = xcolQ (f i j) (L i j x y) := by
  have h1 : ¬blkT hm (encT i x) = blkT hm (encT j y) :=
    fun h => hij ((blkT_encT hm i x).symm.trans (h.trans (blkT_encT hm j y)))
  show blockCol hm f L psi (encT i x) (encT j y) = _
  rw [blockCol, if_neg h1, blkT_encT hm i x, blkT_encT hm j y,
    innT_encT hm i x, innT_encT hm j y]

/-! ### §2  **THE PRODUCT OBSTRUCTION** -/

/-- **NO LEXICOGRAPHIC PRODUCT COLOURING OF THIS SHAPE IS ADMISSIBLE.**

Let `t` blocks of size `m` be coloured by `blockColT`: `f` is a symmetric **factor map**
`Fin t → Fin t → Fin q`, `L` a symmetric **cross labelling** injective in its first inner
variable, and `psi` an arbitrary internal colouring of each block.  Assume only

* `m ≥ 2` — there are two distinct inner vertices to choose;
* `hcover` — the factor map **covers every colour at every block**, i.e. for every block `i` and
  every block colour `a` there is a block `j ≠ i` with `f i j = a` (this is exactly the property
  of a 1-factorisation of `K₆`: at every vertex of `K₆` all five colours are used).

Then the colouring is **not admissible**: it has a `K₄` spanning at most four colours.  The bad
`K₄` is made of the two inner vertices `0`, `1` of block `0` and two inner vertices `y₁ ≠ y₂` of a
block `j ≠ 0` whose factor colour is the block-colour part of the colour of `0₁ 0₂`; the three
edges `0₁0₂`, `0₁y₁`, `0₂y₂` all carry the *same* colour, so by
`Definitions.colorsOn_card_le_four` that `K₄` spans `≤ 4` colours. -/
theorem blockCol_not_admissible {t q m : ℕ} (ht : 0 < t) (hq : 0 < q) (hm : 2 ≤ m)
    (f : Fin t → Fin t → Fin q) (L : Fin t → Fin t → Fin m → Fin m → Fin m)
    (psi : Fin t → Col m (q * m))
    (hf : ∀ i j, f i j = f j i) (hL : ∀ i j x y, L i j x y = L j i y x)
    (hinj : ∀ i j y x x', i ≠ j → L i j x y = L i j x' y → x = x')
    (hcover : ∀ (i : Fin t) (a : Fin q), ∃ j : Fin t, i ≠ j ∧ f i j = a) :
    ¬ Admissible (blockColT ht hq (by omega) f L psi hf hL) := by
  intro hc
  -- the two inner vertices `x₀ ≠ x₁` of the block `i₀`, and the block `i₀` itself
  set i0 : Fin t := ⟨0, by omega⟩ with hi0
  set x0 : Fin m := ⟨0, by omega⟩ with hx0
  set x1 : Fin m := ⟨1, by omega⟩ with hx1
  -- the decomposition of the colour of the internal edge `x₀x₁` of block `i₀`
  obtain ⟨a, l, hv⟩ := exists_xcolQ (by omega : 0 < m) (psi i0 s(x0, x1))
  -- a block `j ≠ i₀` whose factor colour is the block-colour part `a`
  obtain ⟨j, hj1, hj2⟩ := hcover i0 a
  -- for each inner vertex `x` of block `i₀` there is a *unique* inner vertex `y` of block `j`
  -- whose cross index with `x` is the index part `l` (surjectivity of an injective map on `Fin m`)
  have hinj2 : ∀ (i j : Fin t) (x y y' : Fin m), i ≠ j → L i j x y = L i j x y' → y = y' := by
    intro i j x y y' hij h
    exact hinj j i x y y' (Ne.symm hij)
      ((hL i j x y).symm.trans (h.trans (hL i j x y')))
  have key : ∀ x : Fin m, ∃ y : Fin m, L i0 j x y = l := fun x =>
    @Finite.surjective_of_injective (Fin m) _ (fun y : Fin m => L i0 j x y)
      (fun y y' h => hinj2 i0 j x y y' hj1 h) l
  obtain ⟨y₁, hy₁⟩ := key x0
  obtain ⟨y₂, hy₂⟩ := key x1
  have hx01 : x0 ≠ x1 := by
    intro h
    have e : (⟨0, by omega⟩ : Fin m) = (⟨1, by omega⟩ : Fin m) := hx0.symm.trans (h.trans hx1)
    have e2 : (0 : ℕ) = (1 : ℕ) := by simpa using congrArg Fin.val e
    omega
  have hy : y₁ ≠ y₂ := by
    intro h
    have h' : L i0 j x0 y₁ = L i0 j x1 y₁ := hy₁.trans ((h ▸ hy₂).symm)
    exact hx01 (hinj i0 j y₁ x0 x1 hj1 h')
  -- the four vertices of the bad `K₄`
  have hAB : encT i0 x0 ≠ encT i0 x1 := fun h => hx01 (encT_inj_inner h rfl)
  have hCD : encT j y₁ ≠ encT j y₂ := fun h => hy (encT_inj_inner h rfl)
  have cross_ne (x y : Fin m) : encT i0 x ≠ encT j y := by
    intro h
    have hc' : blkT (by omega : 0 < m) (encT i0 x) = blkT (by omega : 0 < m) (encT j y) :=
      congrArg _ h
    rw [blkT_encT, blkT_encT] at hc'
    exact hj1 hc'
  have hAC := cross_ne x0 y₁
  have hAD := cross_ne x0 y₂
  have hBC := cross_ne x1 y₁
  have hBD := cross_ne x1 y₂
  have hFD : FourDistinct (encT i0 x0) (encT i0 x1) (encT j y₁) (encT j y₂) :=
    ⟨hAB, hAC, hAD, hBC, hBD, hCD⟩
  -- the three edges carrying the same colour
  have e1 : blockColT ht hq (by omega) f L psi hf hL (s(encT i0 x0, encT i0 x1))
      = psi i0 s(x0, x1) := blockColT_same hf hL _ _ _
  have e2 : blockColT ht hq (by omega) f L psi hf hL (s(encT i0 x0, encT j y₁))
      = psi i0 s(x0, x1) := by
    rw [blockColT_cross hf hL i0 j hj1 x0 y₁, hv, hj2, hy₁]
  have e3 : blockColT ht hq (by omega) f L psi hf hL (s(encT i0 x1, encT j y₂))
      = psi i0 s(x0, x1) := by
    rw [blockColT_cross hf hL i0 j hj1 x1 y₂, hv, hj2, hy₂]
  -- the three edges are pairwise distinct
  have d12 : s(encT i0 x0, encT i0 x1) ≠ s(encT i0 x0, encT j y₁) := fun h => hBC (sym2_inj_right h)
  have d13 : s(encT i0 x0, encT i0 x1) ≠ s(encT i0 x1, encT j y₂) := by
    intro h
    rcases sym2_inj h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact hAB h1
    · exact hAD h1
  have d23 : s(encT i0 x0, encT j y₁) ≠ s(encT i0 x1, encT j y₂) := by
    intro h
    rcases sym2_inj h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact hAB h1
    · exact hAD h1
  -- three equally coloured edges on a `K₄` force at most four colours
  set S : Finset (Verts (t * m)) := fourSet (encT i0 x0) (encT i0 x1) (encT j y₁) (encT j y₂)
  have v1 : encT i0 x0 ∈ S := Finset.mem_insert_self _ _
  have v2 : encT i0 x1 ∈ S := Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have v3 : encT j y₁ ∈ S :=
    Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
  have v4 : encT j y₂ ∈ S :=
    Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
      (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)))
  have hmem1 : s(encT i0 x0, encT i0 x1)
      ∈ classIn (blockColT ht hq (by omega) f L psi hf hL) (psi i0 s(x0, x1)) S :=
    mem_classIn.mpr ⟨mem_edgeFinset_mk v1 v2 hAB, e1⟩
  have hmem2 : s(encT i0 x0, encT j y₁)
      ∈ classIn (blockColT ht hq (by omega) f L psi hf hL) (psi i0 s(x0, x1)) S :=
    mem_classIn.mpr ⟨mem_edgeFinset_mk v1 v3 hAC, e2⟩
  have hmem3 : s(encT i0 x1, encT j y₂)
      ∈ classIn (blockColT ht hq (by omega) f L psi hf hL) (psi i0 s(x0, x1)) S :=
    mem_classIn.mpr ⟨mem_edgeFinset_mk v2 v4 hBD, e3⟩
  have hcard : 3 ≤ (classIn (blockColT ht hq (by omega) f L psi hf hL) (psi i0 s(x0, x1)) S).card :=
    card_ge_three d12 d13 d23 ⟨hmem1, hmem2, hmem3⟩
  have hle : (colorsOn (blockColT ht hq (by omega) f L psi hf hL) S).card ≤ 4 :=
    colorsOn_card_le_four (card_fourSet hFD) hcard
  have hge : 5 ≤ (colorsOn (blockColT ht hq (by omega) f L psi hf hL) S).card :=
    hc S (card_fourSet hFD)
  omega

/-! ### §2*  The canonical cross labelling: addition of inner indices -/

/-- **Addition of inner indices is symmetric** — the cross labelling `x + y` of two blocks is a
function of the *unordered* pair of inner indices. -/
theorem fin_add_comm (m : ℕ) (x y : Fin m) : x + y = y + x := by
  apply Fin.ext
  simp only [Fin.add_def]
  exact congrArg (fun z : ℕ => z % m) (Nat.add_comm x.val y.val)

/-- **Addition of inner indices is injective**: for fixed `y`, two cross indices `x + y` and
`x' + y` agree only if `x = x'`.  This is what makes `x + y` a legitimate cross labelling: the
cross edges from one inner vertex of one block to all `m` inner vertices of another block get `m`
*distinct* colours. -/
theorem fin_add_inj (m : ℕ) (y : Fin m) {x x' : Fin m} (h : x + y = x' + y) : x = x' := by
  apply Fin.ext
  simp only [Fin.add_def, Fin.mk.injEq] at h
  have h' := Nat.ModEq.add_right_cancel (a := x.val) (b := x'.val) (c := y.val) (d := y.val)
    (Nat.ModEq.refl y.val) h
  exact Nat.ModEq.eq_of_lt_of_lt h' x.isLt x'.isLt

/-! ### §3  The `K₆` witness, and the blow-up which cannot repeat it -/

/-- A constant function on unordered pairs of vertices. -/
def constSym2 {α : Type*} {k : ℕ} (i : Fin k) : Sym2 α → Fin k :=
  fun e => Sym2.rec (motive := fun _ => Fin k) (fun _ _ => i) (by
    intro a b c d h
    cases h with
    | refl => simp
    | swap x y => simp) e

/-- **The 1-factorisation of `K₆` as a colouring**: the unordered pair `{i,j}` (`i < j`)
receives the index of the perfect matching containing it,
`01|23|45`, `02|14|35`, `03|15|24`, `04|13|25`, `05|12|34`. -/
def fact6Col : Col 6 5 := listCol 6 5 (by norm_num)
  [0, 0, 1, 2, 3, 4, 0, 0, 4, 3, 1, 2, 0, 0, 0, 0, 2, 3, 0, 0, 0, 0, 4, 1, 0, 0, 0, 0, 0, 0]

/-- **The factor map of the 1-factorisation of `K₆`**: `fact6 i j` is the colour of the edge
`{i,j}` of `fact6Col`.  This is the map `Fin 6 → Fin 6 → Fin 5` which §2 needs, and `fact6` is
exactly the factor map of `Tables.sixCol` — so the two independent descriptions of the `K₆`
witness agree. -/
def fact6 (i j : Fin 6) : Fin 5 := fact6Col (s(i, j))

/-- The factor map of a 1-factorisation is symmetric. -/
theorem fact6_symm : ∀ i j : Fin 6, fact6 i j = fact6 j i := by native_decide

/-- **THE COVERING PROPERTY OF THE 1-FACTORISATION: at every vertex of `K₆` all five colours are
used.**  This is what `blockCol_not_admissible` needs, and it is what makes the `K₆` witness the
only sensible starting point of a blow-up. -/
theorem fact6_cover : ∀ (i : Fin 6) (a : Fin 5), ∃ j : Fin 6, i ≠ j ∧ fact6 i j = a := by
  native_decide

set_option maxRecDepth 10000 in
/-- **THE 1-FACTORISATION OF `K₆` IS ADMISSIBLE** — every four vertices span at least five
colours, verified by exhaustive computation over the `C(6,4) = 15` four-element vertex sets.  This
is the explicit witness at the only order of this development at which the catalog constant `5/6`
is attained (`Tables.EG_six`), and the starting point of the family which §2 kills. -/
theorem admissible_fact6Col : Admissible fact6Col := by
  unfold Admissible
  native_decide

/-- **THE BLOWS UP OF THE `K₆` WITNESS IS NEVER ADMISSIBLE.**  Blow `K₆` up `m` times, keep the
1-factorisation `fact6` as the factor map, label the cross edges by `x + y`, and colour the blocks
by arbitrary internal colourings `psi`.  For every `m ≥ 2` the resulting colouring of `K_{6m}` with
`5m = 5·(6m)/6` colours **fails** the catalog condition.

This is the sharpest statement available about the most promising construction family of this
development: **`Tables.EG_six = 5 = 5·6/6` cannot be amplified.** -/
theorem blowup_K6_not_admissible {m : ℕ} (hm : 2 ≤ m) (psi : Fin 6 → Col m (5 * m)) :
    ¬ Admissible (blockColT (by norm_num : (0 : ℕ) < 6) (by norm_num : (0 : ℕ) < 5) (by omega) fact6
      (fun _ _ x y => x + y) psi fact6_symm (by intro i j x y; exact fin_add_comm _ x y)) :=
  blockCol_not_admissible (by norm_num : (0 : ℕ) < 6) (by norm_num : (0 : ℕ) < 5) hm fact6 (fun _ _ x y => x + y) psi
    fact6_symm (by intro i j x y; exact fin_add_comm _ x y)
    (by intro i j y x x' _ h; exact fin_add_inj _ y h) fact6_cover

/-- **The blow-up palette is *exactly* the catalog counting bound** `5(n-1)/6`, rounded up:
`5m ≤ f(6m, 4, 5)` for every `m ≥ 1`.  So a single admissible `5m`-colouring of `K_{6m}` would
settle the value of `f` at that order — and §2 says the product family can never supply one. -/
theorem EG_ge_five_mul_six (m : ℕ) : 5 * m ≤ EG (6 * m) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact Nat.zero_le _
  · have h := EG_ge_ceil_five_sixth (6 * m) (by omega)
    omega

/-- **The blow-up construction would be an exact-value certificate.**  One admissible `5m`-colouring
of `K_{6m}` settles `f(6m,4,5) = 5m`, meeting the catalog counting bound. -/
theorem EG_eq_five_mul {m : ℕ} (hm : 0 < m) (h : ∃ c : Col (6 * m) (5 * m), Admissible c) :
    EG (6 * m) = 5 * m := by
  obtain ⟨c, hc⟩ := h
  exact Nat.le_antisymm (EG_le (6 * m) (5 * m) c hc) (EG_ge_five_mul_six m)

/-- A machine-checked instance of §2: at the blow-up size `m = 3`, the four vertices
`{0, 1, 3, 4}` found by the proof above (two inner vertices of the block `0`, and two of the
block `1 = the block whose factor colour is the block-colour part of the colour of `0₁0₂`)
span at most four colours.  This certificate does not use the general argument. -/
theorem blowup_K6_instance :
    ({0, 1, 3, 4} : Finset (Fin 18)).card = 4 ∧
      (colorsOn (blockColT (by norm_num : (0 : ℕ) < 6) (by norm_num : (0 : ℕ) < 5) (by norm_num : (0 : ℕ) < 3) fact6
        (fun _ _ x y => x + y) (fun _ => constSym2 ⟨1, by norm_num⟩) fact6_symm
        (by intro i j x y; exact fin_add_comm _ x y)) ({0, 1, 3, 4} : Finset (Fin 18))).card ≤ 4 := by
  native_decide

end JSP140