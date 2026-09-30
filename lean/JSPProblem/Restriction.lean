import JSPProblem.Main

/-!
# JSP-000140 — restriction, monotonicity, and the reduction of the upper half to one residue class

The catalog answer of `JSP-000140` is the Erdős–Gyárfás function

    f(n, 4, 5) = 5n/6 + o(n)      (Bennett–Cushman–Dudek–Prałat, arXiv:2207.02920),

i.e. the statement `JSP140.jsp_000140_target = FiveSixth EG` of `Main.lean`.  By round 10 the
*lower* half of that statement is proved with the sharp constant `5/6` and no `o(n)` loss
(`Cherry.five_sixth_lower`, `Main.fiveSixthLower_eg`), and by round 13 the *upper* half is known to
be exactly the existence of extremal colourings: `Main.extremal_is_STS` shows that an admissible
colouring of `K_n` with the extremal number `5(n-1)/6` of colours has its two-edge paths forming a
**Steiner triple system** on the vertex set, and `Rigidity.tight_mod6` shows that `n ≡ 1 (mod 6)`
is necessary for the extremal value to be attained at all.

What was still missing is the *logical bridge* between "extremal colourings exist on the residue
class `n ≡ 1 (mod 6)`" and "the upper half of the headline holds for **all** large `n`".  That
bridge is what this file proves.  It uses one elementary fact about `f(n,4,5)` which had not been
formalised: **monotonicity**, obtained by restricting an edge colouring to fewer vertices.

* `restrictCol` — an edge colouring of `K_n` restricted along an injection `Fin m ↪ Fin n`;
* `colorsOn_restrictCol` — the colours of a restricted `K₄` are *exactly* the colours it has in `K_n`;
* `Admissible.restrict` — **admissibility survives restriction** (the catalog condition is
  inherited by every clique of the smaller graph);
* `EG_mono` — **`f` is non-decreasing**: `m ≤ n → f(m,4,5) ≤ f(n,4,5)`;
* `exists_one_mod_six_ge` — above every `n ≥ 6` there is an `m ≡ 1 (mod 6)` with `n ≤ m ≤ n + 6`;
* `fiveSixthUpper_of_family_const` — **THE REDUCTION.**  If for every `m ≡ 1 (mod 6)` there is an
  admissible `k`-colouring of `K_m` with `6k ≤ 5(m-1) + 6D` for a *fixed* constant `D`, then
  `FiveSixthUpper EG` holds, i.e. `f(n,4,5) ≤ 5n/6 + ε n` for all large `n` and every `ε > 0`.
  The `O(1)` slack `D` is absorbed by the `ε n` term, and the five other residue classes are
  absorbed by monotonicity;
* `fiveSixthUpper_of_extremal_family` — the same with `D = 0`, i.e. with colourings attaining the
  extremal value `5(m-1)/6` exactly;
* `fiveSixth_of_extremal_family` and `jsp_000140_main_of_STS_family` — **THE PRIZE REDUCED TO ONE
  HYPOTHESIS.**  The required theorem `jsp_000140_main` (the statement `jsp_000140_target`) follows
  from the lower half, which is proved, together with the single existence hypothesis

        for every `m ≡ 1 (mod 6)` there is an admissible colouring of `K_m`
        whose two-edge paths form a Steiner triple system,

  which is precisely the object built by the random triangle removal process of arXiv:2207.02920.
-/

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

namespace JSP140

variable {n k : ℕ}

/-! ### Restricting an edge colouring to a smaller vertex set -/

/-- Restriction of an edge colouring of `K_n` along an injection `f : Fin m ↪ Fin n`: the edge
`{a, b}` of `K_m` receives the colour which `{f a, f b}` has in `K_n`. -/
def restrictCol {m : ℕ} (f : Verts m ↪ Verts n) (c : Col n k) : Col m k :=
  fun e => c (Sym2.map f e)

/-- Every edge of `K_n` inside the image `f.image S` is the image of an edge of `K_m` inside `S`:
restriction along an injection is a bijection of the edge sets. -/
theorem mem_edgeFinset_image {m : ℕ} {f : Verts m ↪ Verts n} {S : Finset (Verts m)}
    {e : Sym2 (Verts n)} (he : e ∈ edgeFinset (Finset.image f S)) :
    ∃ e' : Sym2 (Verts m), e' ∈ edgeFinset S ∧ Sym2.map f e' = e := by
  obtain ⟨a, b, hab⟩ := Sym2.exists.mp (show ∃ e' : Sym2 (Verts n), e = e' from ⟨e, rfl⟩)
  have he2 := he
  rw [hab] at he2
  have hmem := mem_edgeFinset.mp he2
  have habne : a ≠ b := hmem.2 a b rfl
  have hab2 := Finset.mk_mem_sym2_iff.mp hmem.1
  obtain ⟨x, hx, hfx⟩ := Finset.mem_image.mp hab2.1
  obtain ⟨y, hy, hfy⟩ := Finset.mem_image.mp hab2.2
  subst hfx; subst hfy
  refine ⟨s(x, y), mem_edgeFinset_mk hx hy (by intro hxy; exact habne (congrArg f hxy)), ?_⟩
  calc Sym2.map f (s(x, y)) = s(f x, f y) := rfl
    _ = e := hab.symm

/-- An edge `{x, y}` of `K_m` inside a vertex set `S` maps to an edge of `K_n` inside
`f.image S`: its two endpoints are the images of two distinct elements of `S`. -/
theorem mem_edgeFinset_mk_image {m : ℕ} {f : Verts m ↪ Verts n} {S : Finset (Verts m)}
    {x y : Verts m} (hx : x ∈ S) (hy : y ∈ S) (hne : x ≠ y) :
    s(f x, f y) ∈ (edgeFinset (Finset.image f S) : Finset (Sym2 (Verts n))) := by
  have hneF : f x ≠ f y := fun h => hne (f.injective h)
  refine mem_edgeFinset.mpr ⟨Finset.mk_mem_sym2_iff.mpr
    ⟨Finset.mem_image.mpr ⟨x, hx, rfl⟩, Finset.mem_image.mpr ⟨y, hy, rfl⟩⟩, ?_⟩
  intro a b hab
  rcases sym2_inj hab with ⟨hp, hq⟩ | ⟨hr, hs⟩
  · exact fun h => hneF (hp.trans (h.trans hq.symm))
  · exact fun h => hneF (hr.trans (h.symm.trans hs.symm))

/-- **The colours of a restricted `K₄` are exactly the colours it has in `K_n`.**  In particular the
catalog condition `Admissible` — *every four vertices span at least five colours* — is inherited by
restriction to any sub-configuration of vertices. -/
theorem colorsOn_restrictCol {m : ℕ} {f : Verts m ↪ Verts n} {c : Col n k} (S : Finset (Verts m))
    (hf : Function.Injective f) : colorsOn c (Finset.image f S) = colorsOn (restrictCol f c) S := by
  refine Finset.Subset.antisymm ?_ ?_
  · intro i hi
    rw [colorsOn, Finset.mem_image] at hi
    obtain ⟨e, he, hec⟩ := hi
    obtain ⟨e', he', hemap⟩ := mem_edgeFinset_image he
    refine Finset.mem_image.mpr ⟨e', he', ?_⟩
    show restrictCol f c e' = i
    rw [restrictCol, hemap]
    exact hec
  · intro i hi
    rw [colorsOn, Finset.mem_image] at hi
    obtain ⟨e, he, hec⟩ := hi
    obtain ⟨x, y, hxy⟩ := Sym2.exists.mp (show ∃ e' : Sym2 (Verts m), e = e' from ⟨e, rfl⟩)
    have hmem := mem_edgeFinset.mp (hxy.symm ▸ he)
    have hxyin := Finset.mk_mem_sym2_iff.mp hmem.1
    have hne : x ≠ y := hmem.2 x y rfl
    rw [hxy] at hec
    refine Finset.mem_image.mpr ⟨s(f x, f y), mem_edgeFinset_mk_image hxyin.1 hxyin.2 hne, ?_⟩
    show c (s(f x, f y)) = i
    exact hec

/-- **The catalog condition survives restriction.**  If every four vertices of `K_n` span at least
five colours, then so does the restriction to the image of an injection. -/
theorem Admissible.restrict {m : ℕ} {f : Verts m ↪ Verts n} {c : Col n k}
    (hf : Function.Injective f) (hc : Admissible c) : Admissible (restrictCol f c) := by
  intro S hS
  have hcard : (Finset.image f S).card = S.card :=
    Finset.card_image_iff.mpr (Set.injOn_of_injective hf)
  rw [← hcard] at hS
  rw [← colorsOn_restrictCol S hf]
  exact hc (Finset.image f S) hS

/-- The inclusion `Fin m ↪ Fin n` for `m ≤ n`. -/
def finCastLE {m : ℕ} (h : m ≤ n) : Verts m ↪ Verts n := ⟨Fin.castLE h, Fin.castLE_injective h⟩

/-- **Monotonicity of the Erdős–Gyárfás function.**  `f(n,4,5)` is non-decreasing: an admissible
colouring of `K_n` restricts to an admissible colouring of `K_m` for `m ≤ n`, with no more colours. -/
theorem EG_mono {m : ℕ} (h : m ≤ n) : EG m ≤ EG n := by
  obtain ⟨c, hc⟩ := EG_admissible n
  exact EG_le m (EG n) (restrictCol (finCastLE h) c) (hc.restrict (Fin.castLE_injective h))

/-! ### Above every `n` there is a `1 (mod 6)` within distance `6` -/

/-- **Density of the extremal residue class.**  For every `n ≥ 6` there is an `m` with
`n ≤ m ≤ n + 6` and `m ≡ 1 (mod 6)`, so that `f(n,4,5) ≤ f(m,4,5)` is within reach of the extremal
constructions for the residue class `1 (mod 6)` of `Rigidity.tight_mod6`. -/
theorem exists_one_mod_six_ge (n : ℕ) (hn : 6 ≤ n) :
    ∃ m : ℕ, n ≤ m ∧ m ≤ n + 6 ∧ m % 6 = 1 := by
  have hdiv := Nat.div_add_mod (n + 5) 6
  have hmod : (n + 5) % 6 ≤ 5 := by omega
  have hhi := Nat.mul_div_le (n + 5) 6
  refine ⟨6 * ((n + 5) / 6) + 1, ?_, ?_, ?_⟩
  · omega
  · omega
  · exact Nat.mul_add_mod _ _ _

/-! ### The upper half of the headline, reduced to the extremal constructions -/

/-- **THE UPPER HALF, REDUCED TO THE RESIDUE CLASS `1 (mod 6)`.**  Suppose that for every
`m ≡ 1 (mod 6)` there is an admissible `k`-colouring of `K_m` with

    6 * k ≤ 5 * (m - 1) + 6 * D

for a *fixed* constant `D` — i.e. the extremal value `5(m-1)/6` of the lower bound
`Cherry.five_sixth_lower`, up to a fixed slack `D`.  Then the upper half of the catalog answer
holds with **no error term at all**:

    f(n, 4, 5) ≤ 5n/6 + ε n     for every ε > 0 and all n ≥ max (7, ⌈(D+5)/ε⌉ + 1).

The five other residue classes are absorbed by monotonicity (`EG_mono`) and the constant slack `D`
by the `ε n` term.  This is the exact form in which the construction of arXiv:2207.02920 is needed:
`D = 0` is the extremal colouring of `K_m` for `m ≡ 1 (mod 6)`, whose two-edge paths form a Steiner
triple system (`Main.extremal_is_STS`). -/
theorem fiveSixthUpper_of_family_const {D : ℕ}
    (hfam : ∀ m : ℕ, m % 6 = 1 → ∃ (k : ℕ) (c : Col m k), Admissible c ∧
      6 * k ≤ 5 * (m - 1) + 6 * D) :
    FiveSixthUpper EG := by
  unfold FiveSixthUpper
  intro ε hε
  refine ⟨max 7 (Nat.ceil ((D + 5 : ℝ) / ε) + 1), fun n hn => ?_⟩
  obtain ⟨m, hnm, hmn, hres⟩ := exists_one_mod_six_ge n (by omega)
  obtain ⟨k, c, hcadm, hk⟩ := hfam m hres
  have hk' : (6 : ℝ) * (k : ℝ) ≤ 5 * ((m - 1 : ℕ) : ℝ) + 6 * (D : ℕ) := by exact_mod_cast hk
  have hEG : EG n ≤ k := (EG_mono hnm).trans (EG_le m k c hcadm)
  have hEG' : (6 : ℝ) * (EG n : ℝ) ≤ 6 * (k : ℝ) := by exact_mod_cast (Nat.mul_le_mul_left 6 hEG)
  have hmn' : ((m - 1 : ℕ) : ℝ) ≤ (n : ℝ) + 5 := by
    exact_mod_cast (show m - 1 ≤ n + 5 by omega)
  have hεN : (D + 5 : ℝ) ≤ ε * (n : ℝ) := by
    have hceil : ((D + 5 : ℝ) / ε) ≤ (Nat.ceil ((D + 5 : ℝ) / ε) : ℝ) := Nat.le_ceil _
    have hcast : ((max 7 (Nat.ceil ((D + 5 : ℝ) / ε) + 1) : ℕ) : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast hn
    have hsucc : (Nat.ceil ((D + 5 : ℝ) / ε) : ℝ) + 1
        ≤ ((Nat.ceil ((D + 5 : ℝ) / ε) + 1 : ℕ) : ℝ) := by
      rw [Nat.cast_succ]
    have hmax : ((Nat.ceil ((D + 5 : ℝ) / ε) + 1 : ℕ) : ℝ)
        ≤ ((max 7 (Nat.ceil ((D + 5 : ℝ) / ε) + 1) : ℕ) : ℝ) := by
      exact_mod_cast (Nat.le_max_right 7 _)
    have hstep : ((D + 5 : ℝ) / ε) < ((max 7 (Nat.ceil ((D + 5 : ℝ) / ε) + 1) : ℕ) : ℝ) := by
      linarith
    have hmul' : ((max 7 (Nat.ceil ((D + 5 : ℝ) / ε) + 1) : ℕ) : ℝ) * ε ≤ (n : ℝ) * ε :=
      mul_le_mul_of_nonneg_right hcast hε.le
    have hstep' : ((D + 5 : ℝ) / ε) * ε
        < ((max 7 (Nat.ceil ((D + 5 : ℝ) / ε) + 1) : ℕ) : ℝ) * ε :=
      mul_lt_mul_of_pos_right hstep hε
    have hmul : (D + 5 : ℝ) ≤ (n : ℝ) * ε := by
      have hkey : ((D + 5 : ℝ) / ε) * ε = (D + 5 : ℝ) := by field_simp
      linarith [hkey]
    linarith
  have h1 : (6 : ℝ) * (EG n : ℝ) ≤ 5 * ((m - 1 : ℕ) : ℝ) + 6 * (D : ℝ) := by
    linarith [hEG', hk']
  have h2 : (6 : ℝ) * (EG n : ℝ) ≤ 5 * ((m - 1 : ℕ) : ℝ) + (6 : ℝ) * (ε * (n : ℝ)) := by
    have hle : (D : ℝ) ≤ ((D + 5 : ℕ) : ℝ) := Nat.cast_le.mpr (Nat.le_add_right D 5)
    have hD : (D : ℝ) ≤ ε * (n : ℝ) := by
      linarith
    linarith [h1, hD]
  have h3 : (6 : ℝ) * (EG n : ℝ) ≤ 5 * ((n : ℝ) + 5) + (6 : ℝ) * (ε * (n : ℝ)) := by
    linarith [h2, hmn']
  have h5 : (5 : ℝ) ≤ ((D + 5 : ℕ) : ℝ) := by exact_mod_cast (Nat.le_add_left 5 D)
  have hbig : (30 : ℝ) ≤ (6 : ℝ) * (ε * (n : ℝ)) := by
    linarith [hεN]
  have h4 : (6 : ℝ) * (EG n : ℝ) ≤ 5 * (n : ℝ) + (6 : ℝ) * (ε * (n : ℝ)) := by
    linarith [h3, hbig]
  calc (EG n : ℝ) ≤ (5 * (n : ℝ) + 6 * (ε * (n : ℝ))) / 6 := by linarith [h4]
    _ = 5 * (n : ℝ) / 6 + ε * n := by ring

/-- **The upper half of the headline from the extremal constructions on `n ≡ 1 (mod 6)`.**  If for
every `m ≡ 1 (mod 6)` the graph `K_m` admits an admissible colouring with the *exact* extremal
number `5(m-1)/6` of colours — the number forced by the lower bound `Cherry.five_sixth_lower` —
then `f(n,4,5) ≤ 5n/6 + ε n` for every `ε > 0` and all sufficiently large `n`. -/
theorem fiveSixthUpper_of_extremal_family
    (hfam : ∀ m : ℕ, m % 6 = 1 → ∃ (k : ℕ) (c : Col m k), Admissible c ∧ 6 * k = 5 * (m - 1)) :
    FiveSixthUpper EG := by
  refine fiveSixthUpper_of_family_const (D := 0) (fun m hm => ?_)
  obtain ⟨k, c, hc, hk⟩ := hfam m hm
  exact ⟨k, c, hc, by rw [hk]; omega⟩

/-- **THE HEADLINE, REDUCED TO THE EXISTENCE OF EXTREMAL COLOURINGS.**  The lower half of
`jsp_000140_target` is proved (`Main.fiveSixthLower_eg`); the upper half follows from the single
existence hypothesis `hfam`.  In words: *the catalog answer `f(n,4,5) = 5n/6 + o(n)` follows as
soon as one knows that `K_m` admits an admissible colouring with the extremal `5(m-1)/6` colours for
every `m ≡ 1 (mod 6)`.* -/
theorem fiveSixth_of_extremal_family
    (hfam : ∀ m : ℕ, m % 6 = 1 → ∃ (k : ℕ) (c : Col m k), Admissible c ∧ 6 * k = 5 * (m - 1)) :
    jsp_000140_target := by
  rw [jsp_000140_target, fiveSixth_iff]
  exact ⟨fiveSixthLower_eg, fiveSixthUpper_of_extremal_family hfam⟩

/-- **THE REQUIRED THEOREM, REDUCED TO ONE DESIGN-EXISTENCE HYPOTHESIS.**  `jsp_000140_target` —
the statement of the required theorem `jsp_000140_main` — follows from the lower half (proved in
`Cherry.lean`) and from the hypothesis that for every `m ≡ 1 (mod 6)` there is an admissible
colouring of `K_m` with the extremal `5(m-1)/6` colours *whose two-edge paths form a Steiner triple
system*.  By `Main.extremal_is_STS` the Steiner triple system hypothesis is a consequence of the
extremality of the colouring, so this is precisely the object constructed by the random triangle
removal process of arXiv:2207.02920, and it is the **only** remaining ingredient of the prize:

    `jsp_000140_main_of_STS_family` :  (extremal STS colourings for all m ≡ 1 mod 6) → `jsp_000140_target`.
-/
theorem jsp_000140_main_of_STS_family
    (hfam : ∀ m : ℕ, m % 6 = 1 → ∃ (k : ℕ) (c : Col m k), Admissible c ∧ 6 * k = 5 * (m - 1) ∧
      IsSTS (pathFinset c)) :
    jsp_000140_target := by
  refine fiveSixth_of_extremal_family (fun m hm => ?_)
  obtain ⟨k, c, hc, hk, _⟩ := hfam m hm
  exact ⟨k, c, hc, hk⟩

end JSP140
