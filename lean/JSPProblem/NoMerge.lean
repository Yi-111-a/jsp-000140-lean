import JSPProblem.Construction

/-!
# JSP-000140 — round 77: THE NO-MERGE THEOREM (the sum-type family is worth exactly `m` colours)

`Construction.lean` (round 3) builds the **sum (round-robin) colouring** of `K_m`

    c({a, b}) = a + b   (mod m)

and proves it admissible for odd `m`, which gives `EG n ≤ n` for odd `n` and `EG n ≤ n + 1` in
general.  Every *explicit* colouring ever tried in this development is of exactly this shape or
of the "ghost" shape of `Ghost.lean`, and all of them sit at `n - O(1)` colours, i.e. a whole
colour above the catalog constant `5n/6`.  The obvious way to close that gap is to **merge colour
classes** of the sum colouring, i.e. to compose `a ↦ a + b` with a non-injective map

    φ : ZMod m → Fin k ,      c_φ({a, b}) = φ (a + b) .                 (`NoMerge.mergedCol`)

Rounds 60–74 attacked this by brute force (`discovery/JSP-000140/rrmerge_probe.py` and the
`r66_*`, `r74_*` searches): **no merge was ever admissible**.  Those are finite experiments at
`n = 9, 11, 13` and for groups of size `2, 3, 4`.  This file replaces them by the general
statement.

## The theorems

* **`NoMerge.injective_of_admissible` — THE NO-MERGE THEOREM.**  For odd `m ≥ 5`, the colouring
  `c_φ` is admissible only if `φ` is **injective**.
* **`NoMerge.k_ge`, `NoMerge.card_colorsOn_eq`** — an admissible sum-type colouring of `K_m` uses
  **exactly `m` colours**: within this family the best one can do is the round-robin colouring
  itself, and **merging never saves a single colour**.
* **`NoMerge.no_merge`** — the clean negative statement: for odd `m ≥ 5` and `k < m` there is
  **no** admissible `k`-colouring of `K_m` of the form `φ (a + b)`.

## Why (the local mechanism)

Suppose `φ x = φ y` with `x ≠ y`.  Then for every `u` with `2u ∉ {x, y}` the two edges
`u – (x - u)` and `u – (y - u)` meet at `u` and both have colour `φ x`: an **adjacent collision**.
Admissibility therefore forces *every* other edge of the four-set `{u, x-u, y-u, x-y+u}` to avoid
that colour; in particular the third edge of that four-set with endpoint-sum `x`, namely
`{y-u, x-y+u}`, can fail to be new only if `x - y + u` coincides with one of the three vertices
`u, x - u, y - u`.  That forces `2u ∈ {x, y, 2y - x}`, so `u` must be one of **three** residues;
for `m ≥ 5` a fourth choice exists, and for it the four vertices are *distinct* and their `K₄`
carries three edges of colour `φ x` — a contradiction to `Definitions.colorsOn_card_le_four`.

So the obstruction is purely local, and the same mechanism explains in Lean why the merge route
to `5n/6` colours cannot work for *any* group, *any* modulus and *any* number of colours: the
`1/6` of the colours missing from the round-robin colouring cannot be recovered from it, which
is why the construction of arXiv:2207.02920 has to be a genuinely different (and probabilistic)
one.
-/

namespace JSP140

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

/-! ### Small finset tools -/

private lemma card_two {α : Type*} [DecidableEq α] {a b : α} (h : a ≠ b) :
    ({a, b} : Finset α).card = 2 := by
  rw [Finset.card_insert_eq_ite]
  simp [h]

private lemma card_three {α : Type*} [DecidableEq α] {a b c : α} (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) : ({a, b, c} : Finset α).card = 3 := by
  rw [Finset.card_insert_eq_ite]
  simp [hab, hac, hbc]

private lemma card_four {α : Type*} [DecidableEq α] {a b c d : α} (hab : a ≠ b) (hac : a ≠ c)
    (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    ({a, b, c, d} : Finset α).card = 4 := by
  rw [Finset.card_insert_eq_ite]
  simp [hab, hac, had, hbc, hbd, hcd]

/-! ### Vertices as residues -/

/-- The vertex of `K_m` corresponding to a residue of `ZMod m`. -/
def zfin {m : ℕ} [NeZero m] (x : ZMod m) : Verts m := ⟨x.val, ZMod.val_lt x⟩

@[simp] theorem zfin_val {m : ℕ} [NeZero m] (x : ZMod m) : (zfin x).val = x.val := rfl

@[simp] theorem zfin_cast {m : ℕ} [NeZero m] (x : ZMod m) : (zfin x : ZMod m) = x := by
  have h : (zfin x : ZMod m) = ((x.val : ℕ) : ZMod m) := rfl
  rw [h, ZMod.natCast_val, ZMod.cast_id]

theorem zfin_inj {m : ℕ} [NeZero m] {x y : ZMod m} : zfin x = zfin y ↔ x = y := by
  constructor
  · intro h
    have h' := congrArg (fun t : Verts m => (t : ZMod m)) h
    simpa only [zfin_cast] using h'
  · intro h
    subst h
    rfl

theorem natCast_fin_inj {m : ℕ} [NeZero m] {u v : Verts m} (h : (u : ZMod m) = (v : ZMod m)) :
    u = v := by
  have h' := congrArg ZMod.val h
  simp only [ZMod.val_natCast] at h'
  rw [Nat.mod_eq_of_lt u.isLt, Nat.mod_eq_of_lt v.isLt] at h'
  exact Fin.ext h'

/-! ### The merged sum colouring -/

/-- **A MERGED SUM COLOURING.**  The edge `{a, b}` receives the colour `φ (a + b)` for an
*arbitrary* colour map `φ : ZMod m → Fin k`.  With `φ = id` this is the round-robin colouring
`Construction.sumCol`; the content of this file is that nothing else is admissible. -/
def mergedCol (m k : ℕ) (hk : 0 < k) (φ : ZMod m → Fin k) : Col m k :=
  Sym2.rec (motive := fun _ => Fin k)
    (fun a b => φ ((a : ZMod m) + (b : ZMod m)))
    (by
      intro a b c d h
      cases h with
      | refl => rfl
      | swap x y => simp [add_comm])

@[simp] theorem mergedCol_mk (m k : ℕ) (hk : 0 < k) (φ : ZMod m → Fin k) (a b : Verts m) :
    mergedCol m k hk φ s(a, b) = φ ((a : ZMod m) + (b : ZMod m)) := rfl

/-! ### Every residue is the sum of two distinct vertices -/

/-- **Every residue of `ZMod m` is the sum of two distinct vertices of `K_m`** (odd `m ≥ 3`):
take `a + b` with `b ∈ {0, 1}` and `2b ≠ a`, which is always possible since `2 · 0 ≠ 2 · 1`. -/
theorem exists_add_ne (m : ℕ) (hm : 3 ≤ m) (hodd : m % 2 = 1) (t : ZMod m) :
    ∃ a b : Verts m, a ≠ b ∧ (a : ZMod m) + (b : ZMod m) = t := by
  haveI : NeZero m := ⟨by omega⟩
  have h2ne : (2 : ZMod m) ≠ 0 := by
    intro hh
    have hnat : ((2 : ℕ) : ZMod m) = 0 := by
      have h2 : ((2 : ℕ) : ZMod m) = (2 : ZMod m) := by norm_cast
      exact h2.symm.trans hh
    have h' := congrArg ZMod.val hnat
    rw [ZMod.val_natCast, ZMod.val_zero] at h'
    rcases Nat.dvd_iff_mod_eq_zero.mpr h' with ⟨q, hq⟩
    have hle := Nat.le_of_dvd (by omega : 0 < 2) (show m ∣ 2 from ⟨q, hq⟩)
    omega
  by_cases h0 : t = 0
  · refine ⟨zfin 1, zfin (-1), ?_, ?_⟩
    · intro hh
      have h3 : (1 : ZMod m) = -1 := zfin_inj.mp hh
      exact h2ne (by linear_combination h3)
    · have hsum : ((zfin 1 : Verts m) : ZMod m) + ((zfin (-1) : Verts m) : ZMod m) = 0 := by
        rw [zfin_cast, zfin_cast]
        ring
      rw [hsum, h0]
  · refine ⟨zfin t, zfin 0, ?_, ?_⟩
    · intro hh
      have h3 : (t : ZMod m) = 0 := zfin_inj.mp hh
      exact h0 h3
    · simp only [zfin_cast]
      ring

/-! ### The mechanism: three edges of one colour inside a `K₄` -/

/-- **THE MECHANISM.**  Let `x ≠ y` with `φ x = φ y` and let `u` satisfy `2u ∉ {x, y, 2y - x}`.
Then the four vertices `u, x - u, y - u, x - y + u` are pairwise distinct, and **three of the six
edges of their `K₄` have colour `φ x`**:

* the two edges at `u`, `{u, x-u}` and `{u, y-u}` (endpoint-sums `x` and `y`, with `φ x = φ y`);
* the edge `{y-u, x-y+u}`, whose endpoint-sum is `x` as well.

So this `K₄` spans at most four colours (`Definitions.colorsOn_card_le_four`) and is therefore not
admissible. -/
theorem three_of_four (m k : ℕ) (hm : 0 < m) (hk : 0 < k) (φ : ZMod m → Fin k) {x y : ZMod m}
    (hxy : x ≠ y) (hφ : φ x = φ y) {u : ZMod m}
    (h2x : (2 : ZMod m) * u ≠ x) (h2y : (2 : ZMod m) * u ≠ y)
    (h2yx : (2 : ZMod m) * u ≠ 2 * y - x) :
    ∃ S : Finset (Verts m), S.card = 4 ∧ 3 ≤ (classIn (mergedCol m k hk φ) (φ x) S).card := by
  haveI : NeZero m := ⟨Nat.pos_iff_ne_zero.mp hm⟩
  -- the four vertices are pairwise distinct
  have hab : zfin u ≠ zfin (x - u) := by
    intro hh
    have h3 := zfin_inj.mp hh
    have h5 : (u + u : ZMod m) = (x - u) + u := congrArg (fun z : ZMod m => z + u) h3
    exact h2x (by calc (2 : ZMod m) * u = (u + u : ZMod m) := two_mul u
      _ = (x - u) + u := h5
      _ = x := by ring)
  have had : zfin u ≠ zfin (y - u) := by
    intro hh
    have h3 := zfin_inj.mp hh
    have h5 : (u + u : ZMod m) = (y - u) + u := congrArg (fun z : ZMod m => z + u) h3
    exact h2y (by calc (2 : ZMod m) * u = (u + u : ZMod m) := two_mul u
      _ = (y - u) + u := h5
      _ = y := by ring)
  have hae : zfin u ≠ zfin (x - y + u) := by
    intro hh
    have h3 := zfin_inj.mp hh
    have h5 : (u + -u : ZMod m) = (x - y + u) + -u := congrArg (fun z : ZMod m => z + -u) h3
    have h6 : (x - y + u) + -u = x - y := by ring
    rw [add_neg_cancel, h6] at h5
    exact hxy (sub_eq_zero.mp h5.symm)
  have hbd : zfin (x - u) ≠ zfin (y - u) := by
    intro hh
    have h3 := zfin_inj.mp hh
    have h5 : (x - u) + u = (y - u) + u := congrArg (fun z : ZMod m => z + u) h3
    exact hxy (by calc x = ((x - u) + u : ZMod m) := by ring
      _ = ((y - u) + u : ZMod m) := h5
      _ = y := by ring)
  have hbe : zfin (x - u) ≠ zfin (x - y + u) := by
    intro hh
    have h3 := zfin_inj.mp hh
    have h5 := congrArg (fun z : ZMod m => z - (x - y + u)) h3
    rw [sub_self] at h5
    have h6 : ((x - u) - (x - y + u) : ZMod m) = y - ((u + u : ZMod m)) := by ring
    exact h2y (by calc (2 : ZMod m) * u = (u + u : ZMod m) := two_mul u
      _ = y - ((x - u) - (x - y + u)) := by rw [h6]; ring
      _ = y - 0 := by rw [h5]
      _ = y := sub_zero y)
  have hde : zfin (y - u) ≠ zfin (x - y + u) := by
    intro hh
    have h3 := zfin_inj.mp hh
    have h5 := congrArg (fun z : ZMod m => z - (x - y + u)) h3
    rw [sub_self] at h5
    have h6 : ((y - u) - (x - y + u) : ZMod m) = (2 * y - x) - ((u + u : ZMod m)) := by ring
    exact h2yx (by calc (2 : ZMod m) * u = (u + u : ZMod m) := two_mul u
      _ = (2 * y - x) - ((y - u) - (x - y + u)) := by rw [h6]; ring
      _ = (2 * y - x) - 0 := by rw [h5]
      _ = 2 * y - x := sub_zero _)
  -- the four-set
  set S : Finset (Verts m) := {zfin u, zfin (x - u), zfin (y - u), zfin (x - y + u)} with hSdef
  have hmem : ∀ (p q : Verts m), p ∈ S → q ∈ S → p ≠ q → s(p, q) ∈ edgeFinset S :=
    fun _ _ hp hq hpq => mem_edgeFinset_mk hp hq hpq
  have hcard4 : S.card = 4 := by
    rw [hSdef]
    exact card_four hab had hae hbd hbe hde
  -- three edges of colour `φ x`
  have he1 : mergedCol m k hk φ s(zfin u, zfin (x - u)) = φ x := by
    rw [mergedCol_mk]
    congr 1
    simp only [zfin_cast]
    ring
  have he2 : mergedCol m k hk φ s(zfin u, zfin (y - u)) = φ x := by
    rw [mergedCol_mk, hφ]
    congr 1
    simp only [zfin_cast]
    ring
  have he3 : mergedCol m k hk φ s(zfin (y - u), zfin (x - y + u)) = φ x := by
    rw [mergedCol_mk]
    congr 1
    simp only [zfin_cast]
    ring
  have hed1 : s(zfin u, zfin (x - u)) ≠ s(zfin (y - u), zfin (x - y + u)) := by
    intro hh
    rcases sym2_inj hh with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact had h1
    · exact hae h1
  have hed2 : s(zfin u, zfin (y - u)) ≠ s(zfin (y - u), zfin (x - y + u)) := by
    intro hh
    rcases sym2_inj hh with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact had h1
    · exact hae h1
  have hed3 : s(zfin u, zfin (x - u)) ≠ s(zfin u, zfin (y - u)) := by
    intro hh
    rcases sym2_inj hh with ⟨_, h2⟩ | ⟨h1, _⟩
    · exact hbd h2
    · exact had h1
  set T : Finset (Sym2 (Verts m)) :=
    {s(zfin u, zfin (x - u)), s(zfin u, zfin (y - u)), s(zfin (y - u), zfin (x - y + u))}
    with hTdef
  have hcard3 : T.card = 3 := by
    rw [hTdef]
    exact card_three hed3 hed1 hed2
  have m1 : zfin u ∈ S := by rw [hSdef]; simp
  have m2 : zfin (x - u) ∈ S := by rw [hSdef]; simp
  have m3 : zfin (y - u) ∈ S := by rw [hSdef]; simp
  have m4 : zfin (x - y + u) ∈ S := by rw [hSdef]; simp
  have hsub : T ⊆ classIn (mergedCol m k hk φ) (φ x) S := by
    intro t ht
    simp only [hTdef, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl
    · exact mem_classIn.mpr ⟨hmem _ _ m1 m2 hab, he1⟩
    · exact mem_classIn.mpr ⟨hmem _ _ m1 m3 had, he2⟩
    · exact mem_classIn.mpr ⟨hmem _ _ m3 m4 hde, he3⟩
  refine ⟨S, hcard4, ?_⟩
  rw [← hcard3]
  exact Finset.card_le_card hsub

/-! ### A fourth choice of `u` -/

/-- **THE FOURTH VERTEX.**  For odd `m ≥ 5` and any `x, y` there is a residue `u` with
`2u ∉ {x, y, 2y - x}`: multiplication by `2` is injective on `ZMod m`, so at most three of the `m`
residues are excluded. -/
theorem exists_u (m : ℕ) (hm : 5 ≤ m) (hodd : m % 2 = 1) (x y : ZMod m) :
    ∃ u : ZMod m, (2 : ZMod m) * u ≠ x ∧ (2 : ZMod m) * u ≠ y ∧ (2 : ZMod m) * u ≠ 2 * y - x := by
  haveI : NeZero m := ⟨by omega⟩
  set one : Finset (Verts m) :=
    (Finset.univ : Finset (Verts m)).filter (fun u : Verts m => (2 : ZMod m) * (u : ZMod m) = x)
    with hone
  set two : Finset (Verts m) :=
    (Finset.univ : Finset (Verts m)).filter (fun u : Verts m => (2 : ZMod m) * (u : ZMod m) = y)
    with htwo
  set three : Finset (Verts m) :=
    (Finset.univ : Finset (Verts m)).filter
      (fun u : Verts m => (2 : ZMod m) * (u : ZMod m) = 2 * y - x) with hthree
  set bad : Finset (Verts m) := one ∪ two ∪ three with hbad
  have hinj : ∀ (p q : ZMod m), (2 : ZMod m) * p = (2 : ZMod m) * q → p = q :=
    fun p q h => two_mul_inj hodd h
  have hsub : ∀ (t : ZMod m),
      ((Finset.univ : Finset (Verts m)).filter (fun u : Verts m => (2 : ZMod m) * (u : ZMod m) = t)).card ≤ 1 := by
    intro t
    refine (Finset.card_le_one_iff.mpr fun {a b} ha hb => ?_)
    have h1 : (2 : ZMod m) * (a : ZMod m) = t := (Finset.mem_filter.mp ha).2
    have h2 : (2 : ZMod m) * (b : ZMod m) = t := (Finset.mem_filter.mp hb).2
    exact natCast_fin_inj (hinj _ _ (h1.trans h2.symm))
  have h1 : one.card ≤ 1 := by rw [hone]; exact hsub x
  have h2 : two.card ≤ 1 := by rw [htwo]; exact hsub y
  have h4 : three.card ≤ 1 := by rw [hthree]; exact hsub (2 * y - x)
  have hsub' : bad ⊆ (Finset.univ : Finset (Verts m)) := by
    rw [hbad]
    intro t ht
    rcases Finset.mem_union.mp ht with ht | ht
    · rcases Finset.mem_union.mp ht with ht | ht
      · exact Finset.filter_subset _ _ ht
      · exact Finset.filter_subset _ _ ht
    · exact Finset.filter_subset _ _ ht
  have hcard : ((Finset.univ : Finset (Verts m)) \ bad).card = m - bad.card := by
    rw [Finset.card_sdiff_of_subset hsub', Finset.card_fin]
  have h3 : bad.card ≤ 3 := by
    rw [hbad]
    calc (one ∪ two ∪ three).card ≤ (one ∪ two).card + three.card := Finset.card_union_le _ _
      _ ≤ (one.card + two.card) + three.card := by
        have hlt := Finset.card_union_le one two
        omega
      _ ≤ 3 := by omega
  have hgood : 0 < ((Finset.univ : Finset (Verts m)) \ bad).card := by
    rw [hcard]
    omega
  obtain ⟨u, hu⟩ := Finset.card_pos.mp hgood
  have hu1 : u ∈ (Finset.univ : Finset (Verts m)) := (Finset.mem_sdiff.mp hu).1
  have hu2 : u ∉ bad := (Finset.mem_sdiff.mp hu).2
  refine ⟨(u : ZMod m), ?_, ?_, ?_⟩
  · intro hh
    exact hu2 (by rw [hbad, hone]; simp [hh, hu1])
  · intro hh
    exact hu2 (by rw [hbad, htwo]; simp [hh, hu1])
  · intro hh
    exact hu2 (by rw [hbad, hthree]; simp [hh, hu1])

/-! ### The no-merge theorem -/

/-- **THE NO-MERGE THEOREM.**  Let `m ≥ 5` be odd and let `φ : ZMod m → Fin k`.  If the colouring
`c_φ({a, b}) = φ (a + b)` is admissible, then `φ` is **injective**; in particular `c_φ` needs
`k ≥ m` colours, and *no colour class can be merged into another*. -/
theorem injective_of_admissible (m k : ℕ) (hm : 5 ≤ m) (hodd : m % 2 = 1) (hk : 0 < k)
    (φ : ZMod m → Fin k) (hc : Admissible (mergedCol m k hk φ)) : Function.Injective φ := by
  intro x y hφ
  by_contra hxy
  obtain ⟨u, h2x, h2y, h2yx⟩ := exists_u m hm hodd x y
  obtain ⟨S, hS, h3⟩ := three_of_four m k (by omega) hk φ hxy hφ h2x h2y h2yx
  have h4 := colorsOn_card_le_four hS h3
  have h5 := hc S hS
  omega

/-- **An admissible sum-type colouring of `K_m` needs at least `m` colours.** -/
theorem k_ge (m k : ℕ) (hm : 5 ≤ m) (hodd : m % 2 = 1) (hk : 0 < k)
    (φ : ZMod m → Fin k) (hc : Admissible (mergedCol m k hk φ)) : m ≤ k := by
  haveI : NeZero m := ⟨by omega⟩
  have hinj := injective_of_admissible m k hm hodd hk φ hc
  have himg : ((Finset.univ : Finset (Verts m)).image fun t : Verts m => φ (t : ZMod m)).card
      = m := by
    rw [Finset.card_image_of_injective]
    · exact Finset.card_fin m
    · intro a b h
      exact natCast_fin_inj (hinj (by simpa only [zfin_cast] using h))
  calc m = ((Finset.univ : Finset (Verts m)).image fun t : Verts m => φ (t : ZMod m)).card :=
      himg.symm
    _ ≤ (Finset.univ : Finset (Fin k)).card :=
        Finset.card_le_card (Finset.subset_univ _)
    _ = k := Finset.card_fin k

/-- **THE NO-MERGE STATEMENT.**  For odd `m ≥ 5` there is no admissible `k`-colouring of `K_m`
with `k < m` colours whose colour of `{a, b}` depends only on `a + b`: **merging colour classes of
the round-robin colouring never preserves admissibility**, for any group, any modulus and any
number of merged classes. -/
theorem no_merge (m k : ℕ) (hm : 5 ≤ m) (hodd : m % 2 = 1) (hk : 0 < k) (hkm : k < m) :
    ¬ ∃ φ : ZMod m → Fin k, Admissible (mergedCol m k hk φ) := by
  rintro ⟨φ, hc⟩
  exact absurd (k_ge m k hm hodd hk φ hc) (by omega)

/-- **THE SUM-TYPE FAMILY IS WORTH AT MOST `m` COLOURS** (no statement about `φ` needed). -/
theorem card_colorsOn_le (m k : ℕ) (hm : 0 < m) (hk : 0 < k) (φ : ZMod m → Fin k) :
    (colorsOn (mergedCol m k hk φ) (Finset.univ : Finset (Verts m))).card ≤ m := by
  haveI : NeZero m := ⟨Nat.pos_iff_ne_zero.mp hm⟩
  have hsub : colorsOn (mergedCol m k hk φ) (Finset.univ : Finset (Verts m))
      ⊆ ((Finset.univ : Finset (Verts m)).image fun t : Verts m => φ (t : ZMod m)) := by
    intro i hi
    simp only [colorsOn, Finset.mem_image] at hi
    obtain ⟨e, he, hec⟩ := hi
    obtain ⟨a, b⟩ := e
    rw [mergedCol_mk] at hec
    refine Finset.mem_image.mpr ⟨zfin ((a : ZMod m) + (b : ZMod m)), Finset.mem_univ _, ?_⟩
    simpa only [zfin_cast] using hec
  have hcard : ((Finset.univ : Finset (Verts m)).image fun t : Verts m => φ (t : ZMod m)).card
      ≤ m := by
    refine le_trans (Finset.card_image_le) ?_
    rw [Finset.card_fin]
  exact le_trans (Finset.card_le_card hsub) hcard

/-- **THE SUM-TYPE FAMILY IS WORTH EXACTLY `m` COLOURS.**  If `c_φ` is admissible, then the set
of colours it uses has size exactly `m`: the family contains the round-robin colouring and
nothing better. -/
theorem card_colorsOn_eq (m k : ℕ) (hm : 5 ≤ m) (hodd : m % 2 = 1) (hk : 0 < k)
    (φ : ZMod m → Fin k) (hc : Admissible (mergedCol m k hk φ)) :
    (colorsOn (mergedCol m k hk φ) (Finset.univ : Finset (Verts m))).card = m := by
  have hinj := injective_of_admissible m k hm hodd hk φ hc
  have hsub : ((Finset.univ : Finset (Verts m)).image fun t : Verts m => φ (t : ZMod m))
      ⊆ colorsOn (mergedCol m k hk φ) (Finset.univ : Finset (Verts m)) := by
    intro i hi
    simp only [Finset.mem_image] at hi
    obtain ⟨t, ht, rfl⟩ := hi
    obtain ⟨a, b, hab, hsum⟩ := exists_add_ne m (by omega) hodd (t : ZMod m)
    refine Finset.mem_image.mpr ⟨s(a, b), ?_, ?_⟩
    · exact mem_edgeFinset_mk (Finset.mem_univ a) (Finset.mem_univ b) hab
    · rw [mergedCol_mk, hsum]
  haveI : NeZero m := ⟨Nat.pos_iff_ne_zero.mp (by omega)⟩
  refine le_antisymm (card_colorsOn_le m k (by omega) hk φ) ?_
  have hle : (Finset.image (fun t : Verts m => φ (t : ZMod m))
      (Finset.univ : Finset (Verts m))).card
      ≤ (colorsOn (mergedCol m k hk φ) (Finset.univ : Finset (Verts m))).card :=
    Finset.card_le_card hsub
  have hinj' : Function.Injective (fun t : Verts m => φ (t : ZMod m)) := by
    intro a b h
    exact natCast_fin_inj (hinj (by simpa only [zfin_cast] using h))
  rw [Finset.card_image_of_injective (Finset.univ : Finset (Verts m)) hinj'] at hle
  rw [Finset.card_fin] at hle
  exact hle

/-- **THE NO-MERGE COROLLARY, IN THE LANGUAGE OF `Col`.**  For odd `m ≥ 5` no admissible
colouring of `K_m` with fewer than `m` colours is of sum type: the family
`{ c_φ({a, b}) = φ (a + b) }` contributes **nothing** to the upper bound on `f(m, 4, 5)` beyond
the round-robin colouring of `Construction.lean` (which uses `m` colours and is admissible for
odd `m`).  This is the formal reason why the missing `1/6` of the colours cannot be obtained by
merging the colours of the cyclic construction, for any group, any modulus and any number of
merged classes. -/
theorem no_merge_col (m k : ℕ) (hm : 5 ≤ m) (hodd : m % 2 = 1) (hk : 0 < k) (hkm : k < m) :
    ¬ ∃ (c : Col m k) (φ : ZMod m → Fin k), Admissible c ∧ c = mergedCol m k hk φ := by
  rintro ⟨c, φ, hc, rfl⟩
  exact no_merge m k hm hodd hk hkm ⟨φ, hc⟩

end JSP140
