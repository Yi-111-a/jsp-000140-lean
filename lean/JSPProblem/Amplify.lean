import JSPProblem.Restriction
import JSPProblem.Product

/-!
# JSP-000140 — the cross-index space of a blow-up, the exact budget threshold, and the first
  admissible lexicographic blow-up in this development

`Product.lean` (round 47) killed the blow-up (lexicographic product) route to the missing upper
bound `f(n,4,5) ≤ 5n/6 + o(n)`, in the only shape the catalog budget allows: the cross-index space
is `Fin m`, the same as the set of inner vertices of a block, so the palette is `Fin q × Fin m` =
`q·m` colours.  Its mechanism was: decompose the colour of an internal edge `x₀x₁` as
`(a, l)`, pick the block `j ≠ i₀` whose *factor* colour is `a` (the covering property of a
1-factorisation), and then find `y₁ ≠ y₂` in block `j` with
`L i₀ j x₀ y₁ = L i₀ j x₁ y₂ = l` — possible because `y ↦ L i₀ j x₀ y` is **injective on `Fin m`
and hence surjective onto `Fin m`**.

That last step is exactly where the argument is confined, and this file replaces it.

## §1 — the blow-up with an *arbitrary* cross-index space

The palette is `Fin (q * r)` = a factor colour in `Fin q` times a **cross index in `Fin r`**, with
`r` completely free and unrelated to the block size `m`.  `blockColRT` is the corresponding
colouring; `blockColRT_same` / `blockColRT_cross` are its two halves.

## §2 — the cross indices seen from one inner vertex

`xrange L i j x` is the set of cross indices the edges from the inner vertex `x` of block `i` to
block `j` receive.  `hinj` (the cross labelling is injective in its first inner variable, which is
what makes it a legitimate part of a colouring) forces `x ↦ L i j x ·` to be injective, whence
`m ≤ r` (`m_le_r_of_hinj`), `card_xrange : (xrange L i j x).card = m` and
`card_xrange_le : ≤ r`.

## §3 — **THE INDEX-AVOIDANCE THEOREM** (the new mechanism)

`bad_fourSet` exhibits the bad `K₄` explicitly: whenever a cross index `l₀` is *hit from both
ends* of an internal edge — `l₀ ∈ xrange L i j x₀ ∩ xrange L i j x₁` — the four vertices
`x₀, x₁` of block `i` and `y₁ ≠ y₂` of block `j` span **at most four colours**, because the three
edges `x₀x₁`, `x₀y₁`, `x₁y₂` all carry `xcolQ (f i j) l₀`.

`xrange_avoid` is its consequence for an admissible colouring:

> **If the product colouring is admissible, then for every block `i`, every `j ≠ i`, every internal
> edge `x₀x₁` whose colour is `xcolQ (f i j) l₀`, and every pair of distinct inner vertices,
> the cross index `l₀` is missed by the cross edges of `x₀` or by those of `x₁`.**

No surjectivity is used, and no relation between `m` and `r` is assumed.  This is the statement
round 47 could not prove, because it never needed `y ↦ L i j x ·` to be onto.

## §4 — **THE BUDGET IS EXACTLY THE POINT AT WHICH THE FAMILY DIES**

* **`xrange_eq_univ_of_le`** — if `r ≤ m` then the cross-index set of an inner vertex has `m = r`
  elements inside `Fin r`, i.e. it is *all* of `Fin r`: **a cross-index space within the budget
  hides nothing**, every colour index is hit from every inner vertex;
* **`blockColRT_not_admissible_of_budget`** — so for `r ≤ m` a bad `K₄` always exists.  This is the
  budget case, and it is proved *without* the surjectivity step of round 47;
* **`m_le_r_of_hinj`** — injectivity of the cross labelling already forces `m ≤ r`, so `r ≤ m`
  means `r = m`: **the palette `q·m` is the single smallest palette the shape admits**;
* **`r_gt_m_of_admissible` / `r_ge_succ_of_admissible` / `palette_ge_succ_of_admissible`** — and it
  is *strictly* too small: an admissible blow-up needs `r ≥ m + 1`, hence a palette of at least
  `q·(m+1) > q·m` colours.  With the `K₆` factor and `q = 5` (`Product.EG_ge_five_mul_six`:
  `5m ≤ f(6m,4,5)`) the family therefore misses the catalog counting bound by at least five
  colours;
* `no_amplify_K6_within_budget` — the budget case for the `K₆` witness, quantified over the
  palette.

## §5 — **… AND THE FAMILY IS NOT DEAD, ONLY WASTEFUL: AN ADMISSIBLE BLOW-UP AT PALETTE `5 · 10`**

`Lblk6` labels the cross edges between the blocks `i, j` of a blow-up of `K₆` by `K₂` by the
(ordered by block index) pair of inner indices, so the four cross edges between two blocks get the
four cross indices `0, 1, 2, 3`; `psi6` colours the single internal edge of block `i` by the
product colour `xblock = (i mod 5)`, `xindex = 4 + i`, which no cross edge ever carries.
`admissible_blowup_K6_m2` is the machine-checked statement

    **there is an admissible edge colouring of `K₁₂` with 50 colours which is a lexicographic
    blow-up of the `K₆` witness of this development by `K₂`**,

while the counting bound at `n = 12` is `⌈5 · 11 / 6⌉ = 10`.  Together with §4 this pins the
family down exactly: **a blow-up is admissible, but only at a palette strictly above `q·m`; the
`+1` in the cross-index space is the whole content of the failure of the `5n/6` route.**

## §6 — a blow-up is only as good as the colourings inside its blocks

`colorsOn_block` / `restrictCol_block` / `Admissible_block`: restricting the blow-up to the
vertices of one block reproduces the internal colouring `psi i` exactly, so **an admissible blow-up
forces every internal colouring to be admissible** — the internal colourings would have to solve
the same Erdős–Gyárfás problem inside every block.
-/

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

namespace JSP140

/-! ### §1  A blow-up with an arbitrary cross-index space `Fin r` -/

/-- **THE BLOW-UP COLOURING WITH AN ARBITRARY CROSS-INDEX SPACE.**  The palette is
`Fin (q * r)` — a factor colour in `Fin q` together with a cross index in `Fin r` — with `r`
completely free: the round-47 construction is the special case `r = m`, and the catalog budget
`q·r ≤ q·m` is the case `r ≤ m`. -/
def blockColR {t q m r : ℕ} (hm : 0 < m) (f : Fin t → Fin t → Fin q)
    (L : Fin t → Fin t → Fin m → Fin m → Fin r) (psi : Fin t → Col m (q * r)) :
    ∀ a b : Fin (t * m), Fin (q * r) :=
  fun a b => if blkT hm a = blkT hm b then psi (blkT hm a) s(innT hm a, innT hm b)
    else xcolQ (m := r) (f (blkT hm a) (blkT hm b)) (L (blkT hm a) (blkT hm b) (innT hm a) (innT hm b))

/-- The blow-up colouring is a function of the unordered pair when `f` and `L` are symmetric. -/
theorem blockColR_swap {t q m r : ℕ} {hm : 0 < m} (f : Fin t → Fin t → Fin q)
    (L : Fin t → Fin t → Fin m → Fin m → Fin r) (psi : Fin t → Col m (q * r))
    (hf : ∀ i j, f i j = f j i) (hL : ∀ i j x y, L i j x y = L j i y x) (a b : Fin (t * m)) :
    blockColR hm f L psi a b = blockColR hm f L psi b a := by
  by_cases h1 : blkT hm a = blkT hm b
  · have h2 : blkT hm b = blkT hm a := h1.symm
    rw [blockColR, blockColR, if_pos h1, if_pos h2, h1, Sym2.eq_swap]
  · have h2 : ¬blkT hm b = blkT hm a := fun hh => h1 hh.symm
    rw [blockColR, blockColR, if_neg h1, if_neg h2,
      hf (blkT hm a) (blkT hm b),
      hL (blkT hm a) (blkT hm b) (innT hm a) (innT hm b)]

/-- **THE BLOW-UP COLOURING**, as a colouring of the unordered pairs of `K_{t·m}`. -/
def blockColRT {t q m r : ℕ} (ht : 0 < t) (hq : 0 < q) (hm : 0 < m)
    (f : Fin t → Fin t → Fin q) (L : Fin t → Fin t → Fin m → Fin m → Fin r)
    (psi : Fin t → Col m (q * r))
    (hf : ∀ i j, f i j = f j i) (hL : ∀ i j x y, L i j x y = L j i y x) : Col (t * m) (q * r) :=
  Sym2.rec (motive := fun _ => Fin (q * r)) (blockColR hm f L psi) (by
    intro a b c d h
    cases h with
    | refl => rfl
    | swap x y => simp [blockColR_swap f L psi hf hL])

/-- Inside a block, the blow-up colouring is the internal colouring of that block. -/
theorem blockColRT_same {t q m r : ℕ} {ht : 0 < t} {hq : 0 < q} {hm : 0 < m}
    {f : Fin t → Fin t → Fin q} {L : Fin t → Fin t → Fin m → Fin m → Fin r}
    {psi : Fin t → Col m (q * r)} {hf : ∀ i j, f i j = f j i}
    {hL : ∀ i j x y, L i j x y = L j i y x} (i : Fin t) (x y : Fin m) :
    blockColRT ht hq hm f L psi hf hL (s(encT i x, encT i y)) = psi i s(x, y) := by
  have h1 : blkT hm (encT i x) = blkT hm (encT i y) :=
    (blkT_encT hm i x).trans (blkT_encT hm i y).symm
  show blockColR hm f L psi (encT i x) (encT i y) = _
  rw [blockColR, if_pos h1, blkT_encT hm i x, innT_encT hm i x, innT_encT hm i y]

/-- Between two blocks, the blow-up colouring is the pair (factor colour, cross index). -/
theorem blockColRT_cross {t q m r : ℕ} {ht : 0 < t} {hq : 0 < q} {hm : 0 < m}
    {f : Fin t → Fin t → Fin q} {L : Fin t → Fin t → Fin m → Fin m → Fin r}
    {psi : Fin t → Col m (q * r)} {hf : ∀ i j, f i j = f j i}
    {hL : ∀ i j x y, L i j x y = L j i y x} (i j : Fin t) (hij : i ≠ j) (x y : Fin m) :
    blockColRT ht hq hm f L psi hf hL (s(encT i x, encT j y))
      = xcolQ (m := r) (f i j) (L i j x y) := by
  have h1 : ¬blkT hm (encT i x) = blkT hm (encT j y) :=
    fun h => hij ((blkT_encT hm i x).symm.trans (h.trans (blkT_encT hm j y)))
  show blockColR hm f L psi (encT i x) (encT j y) = _
  rw [blockColR, if_neg h1, blkT_encT hm i x, blkT_encT hm j y,
    innT_encT hm i x, innT_encT hm j y]

/-! ### §2  The cross indices seen from one inner vertex -/

/-- **THE CROSS INDEX SET OF AN INNER VERTEX**: the set of cross indices which the `m` edges from
the inner vertex `x` of block `i` to the inner vertices of block `j` receive. -/
def xrange {t m r : ℕ} (L : Fin t → Fin t → Fin m → Fin m → Fin r) (i j : Fin t) (x : Fin m) :
    Finset (Fin r) := (Finset.univ : Finset (Fin m)).image (L i j x)

theorem mem_xrange {t m r : ℕ} (L : Fin t → Fin t → Fin m → Fin m → Fin r) (i j : Fin t)
    (x y : Fin m) : L i j x y ∈ xrange L i j x :=
  Finset.mem_image.mpr ⟨y, Finset.mem_univ _, rfl⟩

/-- **INJECTIVITY OF THE CROSS LABELLING FORCES THE CROSS-INDEX SPACE TO BE AT LEAST AS LARGE AS
THE BLOCK**: `Fin m` injects into `Fin r`.  So the palette `q·r` of the shape is never smaller than
`q·m`, and the catalog budget `q·r ≤ q·m` leaves no choice at all. -/
theorem m_le_r_of_hinj {t m r : ℕ} (L : Fin t → Fin t → Fin m → Fin m → Fin r)
    (hinj : ∀ i j y x x', i ≠ j → L i j x y = L i j x' y → x = x')
    (i : Fin t) (j : Fin t) (hij : i ≠ j) (y : Fin m) : m ≤ r := by
  have h1 : Fintype.card (Fin m) ≤ Fintype.card (Fin r) :=
    Fintype.card_le_of_injective (fun x : Fin m => L i j x y)
      (fun a b hab => hinj i j y a b hij hab)
  simpa using h1

/-- **Injectivity of the cross labelling makes the cross index set as large as the block.** -/
theorem card_xrange {t m r : ℕ} (L : Fin t → Fin t → Fin m → Fin m → Fin r)
    (i j : Fin t) (x : Fin m) (hinj : ∀ y y', L i j x y = L i j x y' → y = y') :
    (xrange L i j x).card = m := by
  rw [xrange, Finset.card_image_iff.mpr
    (Set.injOn_of_injective (f := L i j x) fun a b h => hinj a b h)]
  simp

/-- The cross index set sits inside the cross-index space. -/
theorem card_xrange_le {t m r : ℕ} (L : Fin t → Fin t → Fin m → Fin m → Fin r) (i j : Fin t)
    (x : Fin m) : (xrange L i j x).card ≤ r := by
  exact le_trans (Finset.card_le_card (Finset.subset_univ _)) (by simp)

/-! ### §3  **THE INDEX-AVOIDANCE MECHANISM** -/

/-- **A CROSS INDEX HIT FROM BOTH ENDS OF AN INTERNAL EDGE PRODUCES A BAD `K₄`.**

Let the product colouring of `K_{t·m}` be `blockColRT`, let the internal edge `x₀x₁` of block `i`
carry the product colour `xcolQ (f i j) l₀` — i.e. its factor-colour part is exactly the factor
colour of the two blocks `i` and `j` — and suppose the cross index `l₀` is realised by the edge
`x₀y₁` and by the edge `x₁y₂`, with `y₁ ≠ y₂` inside block `j`.  Then the three edges `x₀x₁`,
`x₀y₁`, `x₁y₂` all carry the *same* colour, and the four vertices
`x₀, x₁, y₁, y₂` span **at most four** colours. -/
theorem bad_fourSet {t q m r : ℕ} {ht : 0 < t} {hq : 0 < q} {hr : 0 < r} {hm : 0 < m}
    {f : Fin t → Fin t → Fin q} {L : Fin t → Fin t → Fin m → Fin m → Fin r}
    {psi : Fin t → Col m (q * r)} {hf : ∀ i j, f i j = f j i}
    {hL : ∀ i j x y, L i j x y = L j i y x}
    (i j : Fin t) (hij : i ≠ j) (a₀ : Fin q) (hfij : f i j = a₀)
    (x₀ x₁ y₁ y₂ : Fin m) (hne : x₀ ≠ x₁) (hy : y₁ ≠ y₂) (l₀ : Fin r)
    (hp : psi i s(x₀, x₁) = xcolQ (m := r) a₀ l₀)
    (h1 : L i j x₀ y₁ = l₀) (h2 : L i j x₁ y₂ = l₀) :
    (colorsOn (blockColRT ht hq hm f L psi hf hL)
      (fourSet (encT i x₀) (encT i x₁) (encT j y₁) (encT j y₂))).card ≤ 4 := by
  have hAB : encT i x₀ ≠ encT i x₁ := fun h => hne (encT_inj_inner h rfl)
  have hCD : encT j y₁ ≠ encT j y₂ := fun h => hy (encT_inj_inner h rfl)
  have cross_ne (x y : Fin m) : encT i x ≠ encT j y := by
    intro h
    have hc' : blkT hm (encT i x) = blkT hm (encT j y) := congrArg _ h
    rw [blkT_encT, blkT_encT] at hc'
    exact hij hc'
  have hAC := cross_ne x₀ y₁
  have hAD := cross_ne x₀ y₂
  have hBC := cross_ne x₁ y₁
  have hBD := cross_ne x₁ y₂
  have hFD : FourDistinct (encT i x₀) (encT i x₁) (encT j y₁) (encT j y₂) :=
    ⟨hAB, hAC, hAD, hBC, hBD, hCD⟩
  -- the three edges carrying the same colour
  have e1 : blockColRT ht hq hm f L psi hf hL (s(encT i x₀, encT i x₁)) = psi i s(x₀, x₁) :=
    blockColRT_same _ _ _
  have e2 : blockColRT ht hq hm f L psi hf hL (s(encT i x₀, encT j y₁)) = psi i s(x₀, x₁) := by
    rw [blockColRT_cross _ _ hij x₀ y₁, hfij, h1, hp]
  have e3 : blockColRT ht hq hm f L psi hf hL (s(encT i x₁, encT j y₂)) = psi i s(x₀, x₁) := by
    rw [blockColRT_cross _ _ hij x₁ y₂, hfij, h2, hp]
  -- the three edges are pairwise distinct
  have d12 : s(encT i x₀, encT i x₁) ≠ s(encT i x₀, encT j y₁) := fun h => hBC (sym2_inj_right h)
  have d13 : s(encT i x₀, encT i x₁) ≠ s(encT i x₁, encT j y₂) := by
    intro h
    rcases sym2_inj h with ⟨h1', h2'⟩ | ⟨h1', h2'⟩
    · exact hAB h1'
    · exact hAD h1'
  have d23 : s(encT i x₀, encT j y₁) ≠ s(encT i x₁, encT j y₂) := by
    intro h
    rcases sym2_inj h with ⟨h1', h2'⟩ | ⟨h1', h2'⟩
    · exact hAB h1'
    · exact hAD h1'
  set S : Finset (Verts (t * m)) := fourSet (encT i x₀) (encT i x₁) (encT j y₁) (encT j y₂)
  have v1 : encT i x₀ ∈ S := Finset.mem_insert_self _ _
  have v2 : encT i x₁ ∈ S := Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have v3 : encT j y₁ ∈ S :=
    Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
  have v4 : encT j y₂ ∈ S :=
    Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
      (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)))
  have hmem1 : s(encT i x₀, encT i x₁)
      ∈ classIn (blockColRT ht hq hm f L psi hf hL) (psi i s(x₀, x₁)) S :=
    mem_classIn.mpr ⟨mem_edgeFinset_mk v1 v2 hAB, e1⟩
  have hmem2 : s(encT i x₀, encT j y₁)
      ∈ classIn (blockColRT ht hq hm f L psi hf hL) (psi i s(x₀, x₁)) S :=
    mem_classIn.mpr ⟨mem_edgeFinset_mk v1 v3 hAC, e2⟩
  have hmem3 : s(encT i x₁, encT j y₂)
      ∈ classIn (blockColRT ht hq hm f L psi hf hL) (psi i s(x₀, x₁)) S :=
    mem_classIn.mpr ⟨mem_edgeFinset_mk v2 v4 hBD, e3⟩
  have hcard : 3 ≤ (classIn (blockColRT ht hq hm f L psi hf hL) (psi i s(x₀, x₁)) S).card :=
    card_ge_three d12 d13 d23 ⟨hmem1, hmem2, hmem3⟩
  exact colorsOn_card_le_four (card_fourSet hFD) hcard

/-- **THE INDEX-AVOIDANCE THEOREM.**

Assume the product colouring of `K_{t·m}` is **admissible**, the factor map `f` is **symmetric and
covers every colour at every block** (`hcover`, the 1-factorisation property), the cross labelling
`L` is **symmetric** and **injective in its first inner variable** (`hinj`), and the internal
colourings are arbitrary.  Then for every block `i`, every block `j ≠ i`, every internal edge
`x₀x₁` of block `i` whose colour is `xcolQ (f i j) l₀`, and every `x₀ ≠ x₁`, the cross index `l₀`
is **missed** by the cross edges out of `x₀` or by the cross edges out of `x₁`.

No surjectivity is used, and no relation between the block size `m` and the cross-index space `r`
is assumed: the statement holds at **every** palette `Fin (q·r)`. -/
theorem xrange_avoid {t q m r : ℕ} {ht : 0 < t} {hq : 0 < q} {hr : 0 < r} {hm : 0 < m}
    {f : Fin t → Fin t → Fin q} {L : Fin t → Fin t → Fin m → Fin m → Fin r}
    {psi : Fin t → Col m (q * r)} {hf : ∀ i j, f i j = f j i}
    {hL : ∀ i j x y, L i j x y = L j i y x}
    {hinj : ∀ i j y x x', i ≠ j → L i j x y = L i j x' y → x = x'}
    {hcover : ∀ (i : Fin t) (a : Fin q), ∃ j : Fin t, i ≠ j ∧ f i j = a}
    (hc : Admissible (blockColRT ht hq hm f L psi hf hL))
    (hm2 : 2 ≤ m) (i j : Fin t) (hij : i ≠ j) (a₀ : Fin q) (hfij : f i j = a₀)
    (x₀ x₁ : Fin m) (hne : x₀ ≠ x₁) (l₀ : Fin r)
    (hp : psi i s(x₀, x₁) = xcolQ (m := r) a₀ l₀) :
    l₀ ∉ xrange L i j x₀ ∨ l₀ ∉ xrange L i j x₁ := by
  have key : ¬ (l₀ ∈ xrange L i j x₀ ∧ l₀ ∈ xrange L i j x₁) := by
    intro hmem
    obtain ⟨y₁, hy₁m, hy₁⟩ := Finset.mem_image.mp hmem.1
    obtain ⟨y₂, hy₂m, hy₂⟩ := Finset.mem_image.mp hmem.2
    by_cases hy : y₁ = y₂
    · -- the two witnesses coincide, and injectivity in the first inner variable forbids it
      exact hne (hinj i j y₁ x₀ x₁ hij (hy₁.trans (hy ▸ hy₂.symm)))
    · have cross_ne (x y : Fin m) : encT i x ≠ encT j y := by
        intro h
        have hc' : blkT hm (encT i x) = blkT hm (encT j y) := congrArg _ h
        rw [blkT_encT, blkT_encT] at hc'
        exact hij hc'
      have hne4 : FourDistinct (encT i x₀) (encT i x₁) (encT j y₁) (encT j y₂) :=
        ⟨fun h => hne (encT_inj_inner h rfl), cross_ne x₀ y₁, cross_ne x₀ y₂,
          cross_ne x₁ y₁, cross_ne x₁ y₂, fun h => hy (encT_inj_inner h rfl)⟩
      have hle := bad_fourSet (ht := ht) (hr := hr) (hq := hq) (hm := hm) (hf := hf) (hL := hL)
        (i := i) (j := j) hij a₀ hfij x₀ x₁ y₁ y₂ hne hy l₀ hp hy₁ hy₂
      have hge : 5 ≤ (colorsOn (blockColRT ht hq hm f L psi hf hL)
          (fourSet (encT i x₀) (encT i x₁) (encT j y₁) (encT j y₂))).card :=
        hc _ (card_fourSet hne4)
      omega
  by_cases h0 : l₀ ∈ xrange L i j x₀
  · by_cases h1 : l₀ ∈ xrange L i j x₁
    · exact (key ⟨h0, h1⟩).elim
    · exact Or.inr h1
  · exact Or.inl h0

/-! ### §4  **THE BUDGET IS EXACTLY THE POINT AT WHICH THE FAMILY DIES** -/

/-- **A CROSS-INDEX SPACE WITHIN THE BUDGET HIDES NOTHING**: if `r ≤ m` then the cross-index set of
an inner vertex has `m = r` elements inside `Fin r`, i.e. it is *all* of `Fin r`, so every colour
index is realised from every inner vertex.  This is the case round 47 could not reach, because its
surjectivity step needed `m ≤ r`. -/
theorem xrange_eq_univ_of_le {t m r : ℕ} (L : Fin t → Fin t → Fin m → Fin m → Fin r)
    (hrle : r ≤ m) (inj : ∀ (i j : Fin t) (hij : i ≠ j) (x : Fin m),
      ∀ y y', L i j x y = L i j x y' → y = y') (i j : Fin t) (hij : i ≠ j) (x : Fin m) :
    xrange L i j x = (Finset.univ : Finset (Fin r)) := by
  apply Finset.eq_univ_of_card
  have hcard : (xrange L i j x).card = m := card_xrange L i j x (inj i j hij x)
  have hle : (xrange L i j x).card ≤ r := card_xrange_le L i j x
  rw [hcard] at hle
  simp only [Fintype.card_fin] at hle ⊢
  omega

/-- Symmetry of `L` turns injectivity in the first inner variable into injectivity in the second. -/
theorem inj_cross_second {t m r : ℕ} (L : Fin t → Fin t → Fin m → Fin m → Fin r)
    (hL : ∀ i j x y, L i j x y = L j i y x)
    (hinj : ∀ i j y x x', i ≠ j → L i j x y = L i j x' y → x = x')
    (i j : Fin t) (hij : i ≠ j) (x : Fin m) :
    ∀ y y', L i j x y = L i j x y' → y = y' := by
  intro y y' h
  exact hinj j i x y y' (Ne.symm hij) ((hL i j x y).symm.trans (h.trans (hL i j x y')))

/-- **THE BLOW-UP FAMILY IS DEAD AT THE CATALOG BUDGET.**  If the cross-index space satisfies
`r ≤ m` — equivalently, the palette `q·r` does not exceed `q·m` — then every colour index is hit
from both ends of every internal edge, so a `K₄` spanning at most four colours exists.

Together with `m_le_r_of_hinj` this says: **`q·m` is the only palette the shape admits below its
next value, and it is refuted.**  The proof uses no surjectivity step, so unlike round 47 it also
covers the case `r < m` formally. -/
theorem blockColRT_not_admissible_of_budget {t q m r : ℕ} {ht : 0 < t} {hq : 0 < q} {hr : 0 < r}
    {hm : 0 < m} {f : Fin t → Fin t → Fin q} {L : Fin t → Fin t → Fin m → Fin m → Fin r}
    {psi : Fin t → Col m (q * r)} {hf : ∀ i j, f i j = f j i}
    {hL : ∀ i j x y, L i j x y = L j i y x}
    {hinj : ∀ i j y x x', i ≠ j → L i j x y = L i j x' y → x = x'}
    {hcover : ∀ (i : Fin t) (a : Fin q), ∃ j : Fin t, i ≠ j ∧ f i j = a}
    (hm2 : 2 ≤ m) (hrle : r ≤ m) :
    ¬ Admissible (blockColRT ht hq (by omega) f L psi hf hL) := by
  intro hc
  have inj : ∀ (i j : Fin t) (hij : i ≠ j) (x : Fin m),
      ∀ y y', L i j x y = L i j x y' → y = y' := fun i j hij x => inj_cross_second L hL hinj i j hij x
  set i0 : Fin t := ⟨0, by omega⟩ with hi0
  set x0 : Fin m := ⟨0, by omega⟩ with hx0
  set x1 : Fin m := ⟨1, by omega⟩ with hx1
  obtain ⟨a, l, hv⟩ := exists_xcolQ hr (psi i0 s(x0, x1))
  obtain ⟨j, hj1, hj2⟩ := hcover i0 a
  have hx01 : x0 ≠ x1 := by
    intro h
    have e : (⟨0, by omega⟩ : Fin m) = (⟨1, by omega⟩ : Fin m) := hx0.symm.trans (h.trans hx1)
    have e2 : (0 : ℕ) = (1 : ℕ) := by simpa using congrArg Fin.val e
    omega
  have hA0 : xrange L i0 j x0 = (Finset.univ : Finset (Fin r)) :=
    xrange_eq_univ_of_le L hrle inj i0 j hj1 x0
  have hA1 : xrange L i0 j x1 = (Finset.univ : Finset (Fin r)) :=
    xrange_eq_univ_of_le L hrle inj i0 j hj1 x1
  rcases xrange_avoid (hr := hr) (hinj := hinj) (hcover := hcover) (hm := hm) (hc := hc) hm2 i0 j hj1 a hj2 x0 x1 hx01 l hv with h | h
  · exact h (hA0 ▸ Finset.mem_univ l)
  · exact h (hA1 ▸ Finset.mem_univ l)

/-- **THE SHARP QUANTITATIVE FORM: AN ADMISSIBLE BLOW-UP NEEDS A STRICTLY LARGER CROSS-INDEX SPACE
THAN BLOCK SIZE.**  `m = r` is impossible by `blockColRT_not_admissible_of_budget`, so `m < r`. -/
theorem r_gt_m_of_admissible {t q m r : ℕ} {ht : 0 < t} {hq : 0 < q} {hr : 0 < r} {hm : 0 < m}
    {f : Fin t → Fin t → Fin q} {L : Fin t → Fin t → Fin m → Fin m → Fin r}
    {psi : Fin t → Col m (q * r)} {hf : ∀ i j, f i j = f j i}
    {hL : ∀ i j x y, L i j x y = L j i y x}
    {hinj : ∀ i j y x x', i ≠ j → L i j x y = L i j x' y → x = x'}
    {hcover : ∀ (i : Fin t) (a : Fin q), ∃ j : Fin t, i ≠ j ∧ f i j = a}
    (hm2 : 2 ≤ m) (hc : Admissible (blockColRT ht hq (by omega) f L psi hf hL)) : m < r := by
  by_contra hcon
  exact (blockColRT_not_admissible_of_budget (hr := hr) (hinj := hinj) (hcover := hcover)
    (hm := hm) hm2 (Nat.le_of_not_gt hcon)) hc

/-- **THE EXACT THRESHOLD OF THE SHAPE: `r ≥ m + 1`.** -/
theorem r_ge_succ_of_admissible {t q m r : ℕ} {ht : 0 < t} {hq : 0 < q} {hr : 0 < r} {hm : 0 < m}
    {f : Fin t → Fin t → Fin q} {L : Fin t → Fin t → Fin m → Fin m → Fin r}
    {psi : Fin t → Col m (q * r)} {hf : ∀ i j, f i j = f j i}
    {hL : ∀ i j x y, L i j x y = L j i y x}
    {hinj : ∀ i j y x x', i ≠ j → L i j x y = L i j x' y → x = x'}
    {hcover : ∀ (i : Fin t) (a : Fin q), ∃ j : Fin t, i ≠ j ∧ f i j = a}
    (hm2 : 2 ≤ m) (hc : Admissible (blockColRT ht hq (by omega) f L psi hf hL)) : m + 1 ≤ r :=
  r_gt_m_of_admissible (hr := hr) (hinj := hinj) (hcover := hcover) (hm := hm) hm2 hc

/-- **... HENCE A PALETTE OF AT LEAST `q·(m+1) = q·m + q` COLOURS.**  With the `K₆` witness as factor
and `q = 5` this exceeds the catalog counting bound `5m ≤ f(6m,4,5)` (`Product.EG_ge_five_mul_six`)
by at least five colours: **the blow-up route cannot even reach the counting bound, let alone
`5n/6`.** -/
theorem palette_ge_succ_of_admissible {t q m r : ℕ} {ht : 0 < t} {hq : 0 < q} {hr : 0 < r}
    {hm : 0 < m} {f : Fin t → Fin t → Fin q} {L : Fin t → Fin t → Fin m → Fin m → Fin r}
    {psi : Fin t → Col m (q * r)} {hf : ∀ i j, f i j = f j i}
    {hL : ∀ i j x y, L i j x y = L j i y x}
    {hinj : ∀ i j y x x', i ≠ j → L i j x y = L i j x' y → x = x'}
    {hcover : ∀ (i : Fin t) (a : Fin q), ∃ j : Fin t, i ≠ j ∧ f i j = a}
    (hm2 : 2 ≤ m) (hc : Admissible (blockColRT ht hq (by omega) f L psi hf hL)) :
    q * m + q ≤ q * r := by
  have h := r_ge_succ_of_admissible (hr := hr) (hinj := hinj) (hcover := hcover) (hm := hm) hm2 hc
  calc q * m + q = q * (m + 1) := by ring
    _ ≤ q * r := by
      simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using Nat.mul_le_mul h (le_refl q)

/-- **NO ADMISSIBLE COLOURING OF `K_{6m}` IS A BLOW-UP OF THE `K₆` WITNESS AT A PALETTE WITHIN THE
COUNTING BUDGET**, quantified over the palette: for every `r ≤ m` and every family of internal
colourings and every admissible cross labelling, the blow-up with palette `Fin (5 * r)` fails the
catalog condition. -/
theorem no_amplify_K6_within_budget (m : ℕ) (hm : 2 ≤ m) (r : ℕ) (hr : 0 < r) (hrle : r ≤ m)
    (L : Fin 6 → Fin 6 → Fin m → Fin m → Fin r) (psi : Fin 6 → Col m (5 * r))
    (hL : ∀ i j x y, L i j x y = L j i y x)
    (hinj : ∀ i j y x x', i ≠ j → L i j x y = L i j x' y → x = x') :
    ¬ Admissible (blockColRT (by norm_num : (0 : ℕ) < 6) (by norm_num : (0 : ℕ) < 5) (by omega) fact6
      L psi fact6_symm hL) := by
  refine blockColRT_not_admissible_of_budget (f := fact6) (L := L) (psi := psi)
    (hm := by omega) (hr := hr) (hf := fact6_symm) (hL := hL) (hinj := hinj)
    (hcover := fact6_cover) hm hrle

/-! ### §5  **… AND THE FAMILY IS NOT DEAD, ONLY WASTEFUL: AN ADMISSIBLE BLOW-UP AT PALETTE
  `5 · 10`** -/

/-- **THE CANONICAL CROSS LABELLING OF A `K₆`-BY-`K₂` BLOW-UP.**  Between the blocks `i` and `j`
(in the order `i < j`) the cross index is `2x + y` of the two inner indices, so the four cross
edges between two blocks get the four cross indices `0, 1, 2, 3`, and the labelling is symmetric in
the unordered pair of blocks. -/
def Lblk6 (i j : Fin 6) (x y : Fin 2) : Fin 10 :=
  if i.val = j.val then ⟨x.val + y.val, by omega⟩
  else if i.val < j.val then ⟨x.val * 2 + y.val, by omega⟩
  else ⟨y.val * 2 + x.val, by omega⟩

theorem Lblk6_symm : ∀ i j : Fin 6, ∀ x y : Fin 2, Lblk6 i j x y = Lblk6 j i y x := by
  intro i j x y
  by_cases he : i.val = j.val
  · apply Fin.ext
    simp only [Lblk6, if_pos he, if_pos he.symm]
    omega
  · have he' : ¬j.val = i.val := by omega
    by_cases h : i.val < j.val
    · rw [Lblk6, if_neg he, if_pos h, Lblk6, if_neg he', if_neg (by omega : ¬j.val < i.val)]
    · rw [Lblk6, if_neg he, if_neg h, Lblk6, if_neg he', if_pos (by omega : j.val < i.val)]

theorem Lblk6_inj : ∀ (i j : Fin 6) (y : Fin 2) (x x' : Fin 2), i ≠ j →
    Lblk6 i j x y = Lblk6 i j x' y → x = x' := by native_decide

theorem Lblk6_inj' : ∀ (i j : Fin 6) (x : Fin 2) (y y' : Fin 2), i ≠ j →
    Lblk6 i j x y = Lblk6 i j x y' → y = y' := by native_decide

/-- **THE CROSS EDGES BETWEEN TWO BLOCKS USE ONLY THE FIRST FOUR CROSS INDICES**, which is what
leaves `4 + i` free for the internal edge of block `i`. -/
theorem Lblk6_lt_four : ∀ i j : Fin 6, ∀ x y : Fin 2, Lblk6 i j x y < 4 := by native_decide

/-- **THE INTERNAL COLOURING OF A `K₆`-BY-`K₂` BLOW-UP**: the single edge of the block `i` of `K₂`
receives the product colour with factor `i mod 5` and cross index `4 + i`, which no cross edge ever
carries. -/
def psi6 (i : Fin 6) : Col 2 50 := constSym2 ⟨(i.val % 5) * 10 + 4 + i.val, by omega⟩

/-- The internal colour of block `i` has cross index `4 + i`. -/
theorem psi6_val (i : Fin 6) : psi6 i s(0, 1) = ⟨(i.val % 5) * 10 + 4 + i.val, by omega⟩ := rfl

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 200000 in
/-- **THE FIRST ADMISSIBLE LEXICOGRAPHIC BLOW-UP IN THIS DEVELOPMENT.**

Blow the `K₆` witness `fact6Col` of `Product.lean` — the only order of this development at which the
catalog constant `5/6` is attained — up by `K₂`, label the cross edges by `Lblk6` and colour each
block by the single colour `psi6 i`.  The result is an **admissible** edge colouring of `K₁₂` with
`50 = 5 · 10` colours: every one of the `C(12,4) = 495` four-vertex sets spans at least five
colours (`native_decide`).

The counting bound at `n = 12` is `⌈5 · 11 / 6⌉ = 10`, and §4 shows that **no** blow-up of this shape
can be admissible at a palette `≤ 5m`: the family is admissible, but only at a palette strictly
above `q·m`, and so it misses `5n/6` by an unbounded factor. -/
theorem admissible_blowup_K6_m2 :
    Admissible (blockColRT (by norm_num : (0 : ℕ) < 6) (by norm_num : (0 : ℕ) < 5)
      (by norm_num : (0 : ℕ) < 2) fact6 Lblk6 psi6 fact6_symm Lblk6_symm) := by
  unfold Admissible
  native_decide

/-- **THE VALUE `f(12,4,5)` IS AT MOST `50` BY A LEXICOGRAPHIC BLOW-UP** — the first upper bound for
`f` obtained from a product construction in this development.  It is far above the counting bound
`10`, which is exactly the phenomenon §4 proves is unavoidable for this shape. -/
theorem EG_le_fifty_blowup : EG 12 ≤ 50 := by
  refine EG_le 12 50 _ admissible_blowup_K6_m2

/-- **AND THE COUNTING BOUND AT `n = 12` IS `10`, SO THE BLOW-UP IS A FACTOR `5` OFF THE BUDGET.** -/
theorem counting_bound_at_twelve : (5 * (12 - 1) + 5) / 6 = 10 := by norm_num

/-! ### §6  A blow-up is only as good as the colourings inside its blocks -/

/-- The inner vertices of block `i`, as an injection. -/
def encInj {t m : ℕ} (hm : 0 < m) (i : Fin t) : Verts m ↪ Verts (t * m) :=
  ⟨encT i, fun _ _ h => encT_inj_inner h rfl⟩

/-- Restricting the blow-up to one block gives back the internal colouring. -/
theorem restrictCol_block {t q m r : ℕ} {ht : 0 < t} {hq : 0 < q} {hm : 0 < m}
    {f : Fin t → Fin t → Fin q} {L : Fin t → Fin t → Fin m → Fin m → Fin r}
    {psi : Fin t → Col m (q * r)} {hf : ∀ i j, f i j = f j i}
    {hL : ∀ i j x y, L i j x y = L j i y x} (i : Fin t) :
    restrictCol (encInj hm i) (blockColRT ht hq hm f L psi hf hL) = psi i := by
  funext e
  obtain ⟨a, b, hab⟩ := Sym2.exists.mp (show ∃ e' : Sym2 (Verts m), e = e' from ⟨e, rfl⟩)
  rw [hab, restrictCol]
  show blockColRT ht hq hm f L psi hf hL (s(encT i a, encT i b)) = psi i (s(a, b))
  exact blockColRT_same i a b

set_option maxHeartbeats 0 in
/-- **THE COLOURS INSIDE ONE BLOCK ARE EXACTLY THE COLOURS OF THE INTERNAL COLOURING.** -/
theorem colorsOn_block {t q m r : ℕ} {ht : 0 < t} {hq : 0 < q} {hm : 0 < m}
    {f : Fin t → Fin t → Fin q} {L : Fin t → Fin t → Fin m → Fin m → Fin r}
    {psi : Fin t → Col m (q * r)} {hf : ∀ i j, f i j = f j i}
    {hL : ∀ i j x y, L i j x y = L j i y x} (i : Fin t) (S : Finset (Verts m)) :
    colorsOn (blockColRT ht hq hm f L psi hf hL) (Finset.image (encT i) S) = colorsOn (psi i) S := by
  have h1 : colorsOn (blockColRT ht hq hm f L psi hf hL) (Finset.image (encT i) S)
      = colorsOn (restrictCol (encInj hm i) (blockColRT ht hq hm f L psi hf hL)) S :=
    colorsOn_restrictCol S (encInj hm i).injective
  rw [restrictCol_block] at h1
  exact h1

/-- **AN ADMISSIBLE BLOW-UP FORCES EVERY INTERNAL COLOURING TO BE ADMISSIBLE.**  A block is a set
of `m` of the `t·m` vertices, so a `K₄` inside it must span five colours of the blow-up, which —
by `restrictCol_block` — are the colours of the internal colouring.  So a lexicographic product is
never better than the colourings it is built from. -/
theorem Admissible_block {t q m r : ℕ} {ht : 0 < t} {hq : 0 < q} {hm : 0 < m}
    {f : Fin t → Fin t → Fin q} {L : Fin t → Fin t → Fin m → Fin m → Fin r}
    {psi : Fin t → Col m (q * r)} {hf : ∀ i j, f i j = f j i}
    {hL : ∀ i j x y, L i j x y = L j i y x} (hc : Admissible (blockColRT ht hq hm f L psi hf hL))
    (i : Fin t) : Admissible (psi i) := by
  have h1 : Admissible (restrictCol (encInj hm i) (blockColRT ht hq hm f L psi hf hL)) :=
    hc.restrict (encInj hm i).injective
  rwa [restrictCol_block] at h1

/-- **AND THEREFORE `f(m,4,5) ≤ q·r` FOR AN ADMISSIBLE BLOW-UP**: the internal colouring is itself
an admissible colouring of `K_m` with the whole palette. -/
theorem EG_le_palette_of_admissible {t q m r : ℕ} {ht : 0 < t} {hq : 0 < q} {hm : 0 < m}
    {f : Fin t → Fin t → Fin q} {L : Fin t → Fin t → Fin m → Fin m → Fin r}
    {psi : Fin t → Col m (q * r)} {hf : ∀ i j, f i j = f j i}
    {hL : ∀ i j x y, L i j x y = L j i y x}
    (hc : Admissible (blockColRT ht hq hm f L psi hf hL)) (i : Fin t) : EG m ≤ q * r :=
  EG_le m (q * r) (psi i) (Admissible_block hc i)

end JSP140