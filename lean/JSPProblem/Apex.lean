import JSPProblem.Strict
import JSPProblem.Rigidity

/-!
# JSP-000140 — how many colours a two-edge path can save, and the apex multiplicity it costs

Rounds 1–54 of this development produced the sharp lower bound

    `Cherry.five_sixth_lower`   `5 * (n-1) ≤ 6 * k`

and round 53 improved it by one unit (`Strict.not_sharp`: `6k = 5(n-1)` never happens), using
the local observation `Strict.apex_zeroA`:

> **the apex `u` of a labelled triangle `(u; p, q)` has no edge of colour `μ = c s(p,q)`.**

This file turns that observation into a **quantitative second-order bound**, and it is the first
statement in the development that says *how far below `n-1` an admissible colouring can be*.

## §1  What a two-edge path buys

`Surplus.global_identity` is the exact form of the counting argument:

    `n(n-1) + Isolated c = n * k + Paths c`,

i.e. with `I = Isolated c` (the number of `(vertex, colour)` incidences on which the colour does
not occur) and `P = Paths c` (the number of two-edge paths),

    `P - I = n * k - n * (n-1)`,

so each two-edge path *saves* `1/n` of a colour against the `n-1` of a colouring whose colour
classes are single edges only.  A colouring with `k < n-1` colours therefore **must** have
two-edge paths, and the deficit is exactly

    `n-1-k = (P - I) / n`.                                                     (`Paths.lean`'s identity)

## §2  The price of a path is paid at its apex

`Strict.apex_zeroA` says the leaf-colour `μ` of a path centred at `v` is *missing at `v`*, so each
**distinct** leaf-colour used at `v` costs one unit of `Isolated c`.  Paths may however *share* a
leaf-colour at one apex, and that is the whole content of this file: let `M` bound the number of
paths one apex may spend on a single leaf-colour, then

    `Paths c ≤ M * Isolated c`                                                 (`Apex.paths_le_mul_isolated`)

and combining this with `Cherry.paths_le` (`6P ≤ n(n-1)`) gives the **interpolating lower bound**

    `6 * M * k ≥ (n - 1) * (5 * M + 1)`,                                       (`Apex.apexBound`)

equivalently, in the form that says how much a path can save,

    `6 * M * (n - 1 - k) ≤ (M - 1) * (n - 1)`.                                (`Apex.deficit_le`)

## §3  Why the family of bounds is the right shape

`M` interpolates between the two constants this development knows:

* `M = 1` (`Apex.k_ge_of_unique_apexPair`, `Apex.deficit_one`): **no saving at all**, `k ≥ n-1`;
  this is the regime of the round-robin/ghost constructions, and it explains why they cannot be
  improved by any local rearrangement of a colouring whose two-edge paths all have distinct
  leaf-colours at their apex;
* `M → ∞` (`Apex.sharp_limit`): the sharp counting bound `6k ≥ 5(n-1)` of `Cherry.lean`, which is
  the `o(1)`-per-order end of the same family.

So **the closer a construction gets to `5n/6`, the more the leaf-colours of its paths must repeat at
their apexes** — quantified: to save `d` colours below `n-1` one needs multiplicity at least
`(n-1)/(6d) - 1` at some apex.  This is a *necessary* condition on the output of the first stage of
arXiv:2207.02920 §4, and it is not implied by anything proved in rounds 1–53.

Everything here is a theorem about *admissible colourings*; nothing new is assumed about their
existence, so the prize hypothesis `Main.AdmissibleUpper 1` is untouched.
-/

namespace JSP140

variable {n k : ℕ} {c : Col n k}

/-! ### §1  The two leaves of a two-edge path, and the colour of their edge -/

/-- **THE TWO LEAVES OF A TWO-EDGE PATH**, as a witness: `(a, b)` with `a ≠ b` and
`Nbrs c i v = {a, b}`.  This is the sigma form of `Finset.card_eq_two`, and it is the only place
where the two-element structure of a path centre is used. -/
noncomputable def leavesOf (c : Col n k) (i : Fin k) (v : Verts n) (hv : v ∈ twoA c i) :
    Verts n × Verts n :=
  ((Finset.card_eq_two.mp (card_twoA i hv)).choose,
   (Finset.card_eq_two.mp (card_twoA i hv)).choose_spec.choose)

/-- The two leaves of the two-edge path of colour `i` centred at `v` are exactly its two colour-`i`
neighbours, and they are distinct. -/
theorem leavesOf_spec {c : Col n k} {i : Fin k} {v : Verts n} (hv : v ∈ twoA c i) :
    Nbrs c i v = {(leavesOf c i v hv).1, (leavesOf c i v hv).2} ∧
      (leavesOf c i v hv).1 ≠ (leavesOf c i v hv).2 := by
  have hq := Finset.card_eq_two.mp (card_twoA i hv)
  refine ⟨?_, ?_⟩
  · rw [leavesOf]
    exact hq.choose_spec.choose_spec.2
  · rw [leavesOf]
    exact hq.choose_spec.choose_spec.1

/-- `cherryPair c p` is the pair of leaves of the two-edge path `p = (colour, centre)`, and the
dummy pair `⟨p.2, p.2⟩` when `p` is not a path. -/
noncomputable def cherryPair (c : Col n k) (p : Fin k × Verts n) : Verts n × Verts n :=
  if hp : p.2 ∈ twoA c p.1 then leavesOf c p.1 p.2 hp else (p.2, p.2)

/-- The two leaves of a two-edge path are exactly its centre's two colour-`p.1` neighbours, and they
are distinct: `a - v - b` is a two-edge path, not a loop. -/
theorem cherryPair_spec {p : Fin k × Verts n} (hp : p ∈ cherryFinset c) :
    Nbrs c p.1 p.2 = {(cherryPair c p).1, (cherryPair c p).2} ∧
      (cherryPair c p).1 ≠ (cherryPair c p).2 := by
  have h : p.2 ∈ twoA c p.1 := twoA_of_mem_cherryFinset hp
  have hS := leavesOf_spec (c := c) (i := p.1) (v := p.2) h
  rw [cherryPair, dite_eq_left h]
  exact hS

theorem cherryPair_ne {p : Fin k × Verts n} (hp : p ∈ cherryFinset c) :
    (cherryPair c p).1 ≠ (cherryPair c p).2 := (cherryPair_spec hp).2

/-- The two leaves of a two-edge path are exactly the two colour-`p.1` neighbours of the centre
`p.2`. -/
theorem Nbrs_cherryPair {p : Fin k × Verts n} (hp : p ∈ cherryFinset c) :
    Nbrs c p.1 p.2 = {(cherryPair c p).1, (cherryPair c p).2} := (cherryPair_spec hp).1

/-- **EVERY TWO-EDGE PATH OF AN ADMISSIBLE COLOURING IS A LABELLED TRIANGLE**: the two edges at the
centre share a colour, and the leaf edge has a different one.  This is the input of round 53's
`apex_zeroA`, in the language of `cherryFinset`. -/
theorem LabTri_cherryPair {p : Fin k × Verts n} (hc : Admissible c) (hn : 4 ≤ n)
    (hp : p ∈ cherryFinset c) :
    LabTri c p.2 (cherryPair c p).1 (cherryPair c p).2 := by
  have hv : p.2 ∈ twoA c p.1 := twoA_of_mem_cherryFinset hp
  have hN : Nbrs c p.1 p.2 = {(cherryPair c p).1, (cherryPair c p).2} := Nbrs_cherryPair hp
  have hne : (cherryPair c p).1 ≠ (cherryPair c p).2 := cherryPair_ne hp
  have hP1 : (cherryPair c p).1 ∈ Nbrs c p.1 p.2 := by rw [hN]; simp
  have hP2 : (cherryPair c p).2 ∈ Nbrs c p.1 p.2 := by rw [hN]; simp
  have h1 : p.2 ≠ (cherryPair c p).1 := (mem_Nbrs.mp hP1).1.symm
  have h2 : p.2 ≠ (cherryPair c p).2 := (mem_Nbrs.mp hP2).1.symm
  have h4 : c s(p.2, (cherryPair c p).1) = c s(p.2, (cherryPair c p).2) :=
    (mem_Nbrs.mp hP1).2.trans (mem_Nbrs.mp hP2).2.symm
  refine ⟨h1, h2, hne, h4, fun hcon => (cherry_leaf_pair hc hn hv hP1 hP2 hne).1 ?_⟩
  exact ((mem_Nbrs.mp hP1).2.symm.trans hcon).symm

/-! ### §2  The `(leaf colour, apex)` pair of a two-edge path -/

/-- The pair `(colour of the leaf edge, apex)` of the two-edge path `p`. -/
noncomputable def apexPair (c : Col n k) (p : Fin k × Verts n) : Fin k × Verts n :=
  (c s((cherryPair c p).1, (cherryPair c p).2), p.2)

/-- The set of `(leaf colour, apex)` pairs realised by the two-edge paths of `c`.  Its cardinality is
the number of *distinct* leaf-colours counted over all apexes — the number of units of
`Isolated c` that the two-edge paths of `c` cost. -/
noncomputable def apexFinset (c : Col n k) : Finset (Fin k × Verts n) :=
  (cherryFinset c).image (apexPair c)

theorem mem_apexFinset {y : Fin k × Verts n} :
    y ∈ apexFinset c ↔ ∃ p ∈ cherryFinset c, apexPair c p = y := by
  rw [apexFinset, Finset.mem_image]

/-- **THE COST OF A PATH IS PAID AT ITS APEX (round 53's observation, on the finset).** -/
theorem mem_apexFinset_zeroA {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n)
    {y : Fin k × Verts n} (hy : y ∈ apexFinset c) : y.2 ∈ zeroA c y.1 := by
  obtain ⟨p, hp, he⟩ := mem_apexFinset.mp hy
  have h1 := apex_zeroA hc (LabTri_cherryPair hc hn hp)
  rw [← he]
  exact h1

private theorem card_filter_le {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n) (i : Fin k) :
    ((apexFinset c).filter fun y => y.1 = i).card ≤ (zeroA c i).card := by
  have h1 : ((apexFinset c).filter fun y => y.1 = i).card
      ≤ ((zeroA c i).image fun v : Verts n => (i, v)).card := by
    refine Finset.card_le_card_of_injOn (f := fun y : Fin k × Verts n => (i, y.2))
      (s := (apexFinset c).filter fun y => y.1 = i)
      (t := (zeroA c i).image fun v : Verts n => (i, v)) ?_ ?_
    · intro y hy
      obtain ⟨hy1, hy2⟩ := Finset.mem_filter.mp hy
      exact Finset.mem_image.mpr ⟨y.2, hy2 ▸ mem_apexFinset_zeroA hc hn hy1, rfl⟩
    · intro y hy w hw h
      obtain ⟨hy1, hy2⟩ := Finset.mem_filter.mp hy
      obtain ⟨hw1, hw2⟩ := Finset.mem_filter.mp hw
      have h' : (i, y.2) = (i, w.2) := h
      refine Prod.ext_iff.mpr ⟨?_, Prod.mk.inj h' |>.2⟩
      exact hy2.trans hw2.symm
  have h2 : ((zeroA c i).image fun v : Verts n => (i, v)).card = (zeroA c i).card :=
    Finset.card_image_of_injective _ (fun v w h => congrArg Prod.snd h)
  exact h1.trans h2.le

/-- **THE COST, COUNTED: the distinct `(leaf colour, apex)` pairs are `Isolated c` units of defect,
so `|apexFinset c| ≤ Isolated c`.** -/
theorem card_apexFinset_le_isolated {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n) :
    (apexFinset c).card ≤ Isolated c := by
  have hcard : (apexFinset c).card
      = ∑ i : Fin k, ((apexFinset c).filter fun y => y.1 = i).card :=
    Finset.card_eq_sum_card_fiberwise (s := apexFinset c) (f := Prod.fst)
      (t := Finset.univ) (fun _ _ => Finset.mem_univ _)
  have hle : (∑ i : Fin k, ((apexFinset c).filter fun y => y.1 = i).card)
      ≤ ∑ i : Fin k, (zeroA c i).card :=
    Finset.sum_le_sum fun i _ => card_filter_le hc hn i
  unfold Isolated
  exact hcard.trans_le hle

/-! ### §3  Pigeonhole: `M` paths per `(leaf colour, apex)` pair -/

/-- **PIGEONHOLE OVER THE APEX PAIRS.**  If no `(leaf colour, apex)` pair carries more than `M`
two-edge paths, then `Paths c ≤ M * |apexFinset c|`. -/
theorem card_cherryFinset_le_mul_apexFinset {c : Col n k} {M : ℕ}
    (hmul : ∀ y : Fin k × Verts n,
      ((cherryFinset c).filter fun p => apexPair c p = y).card ≤ M) :
    (cherryFinset c).card ≤ M * (apexFinset c).card := by
  have h1 : (cherryFinset c).card
      = ∑ y ∈ apexFinset c, ((cherryFinset c).filter fun p => apexPair c p = y).card :=
    Finset.card_eq_sum_card_image (apexPair c) (cherryFinset c)
  have h2 : (∑ y ∈ apexFinset c, ((cherryFinset c).filter fun p => apexPair c p = y).card)
      ≤ ∑ _y ∈ apexFinset c, M := Finset.sum_le_sum fun y _ => hmul y
  have h3 : (∑ _y ∈ apexFinset c, M) = M * (apexFinset c).card := by
    simp [Finset.sum_const, Nat.mul_comm]
  omega

/-- **`Paths c ≤ M * Isolated c`.**  Two-edge paths are paid for in `Isolated c` units, at the rate
of at least one unit per `M` paths. -/
theorem paths_le_mul_isolated {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n) {M : ℕ} (hM : 1 ≤ M)
    (hmul : ∀ y : Fin k × Verts n,
      ((cherryFinset c).filter fun p => apexPair c p = y).card ≤ M) :
    Paths c ≤ M * Isolated c := by
  have h1 : Paths c ≤ M * (apexFinset c).card := by
    rw [← card_cherryFinset c]
    exact card_cherryFinset_le_mul_apexFinset hmul
  have h2 := card_apexFinset_le_isolated hc hn
  exact h1.trans (mul_le_mul_of_nonneg_left h2 (by omega))

/-! ### §4  The interpolating lower bound -/

/-- **THE APEX-MULTIPLICITY BOUND.**
`(n-1) * (5M+1) ≤ 6 * M * k` for every admissible colouring in which no `(leaf colour, apex)` pair
carries more than `M` two-edge paths.

Equivalently `5(n-1) + (n-1)/M ≤ 6k`: the sharper the counting constant one aims at, the more the
leaf-colours of the two-edge paths must repeat at their apexes.  For `M = 1` this reads `k ≥ n-1`
and for large `M` it tends to `Cherry.five_sixth_lower`. -/
theorem apexBound {M : ℕ} (hc : Admissible c) (hn : 4 ≤ n) (hM : 1 ≤ M)
    (hmul : ∀ y : Fin k × Verts n,
      ((cherryFinset c).filter fun p => apexPair c p = y).card ≤ M) :
    (n - 1) * (5 * M + 1) ≤ 6 * M * k := by
  have hA := paths_le_mul_isolated hc hn hM hmul
  have h6 : 6 * Paths c ≤ n * (n - 1) := by
    have h := six_mul_paths_le hc hn
    omega
  have hg := global_identity hc
  -- everything is linear once the products are frozen as atoms
  have h1 : (Paths c : ℤ) ≤ (M : ℤ) * (Isolated c : ℤ) := by exact_mod_cast hA
  have hg' : ((n : ℤ) * ((n - 1 : ℕ) : ℤ)) + (Isolated c : ℤ)
      = ((n : ℤ) * (k : ℤ)) + (Paths c : ℤ) := by exact_mod_cast hg
  have hmul1 : (M : ℤ) * (((n : ℤ) * ((n - 1 : ℕ) : ℤ)) + (Isolated c : ℤ))
      = (M : ℤ) * (((n : ℤ) * (k : ℤ)) + (Paths c : ℤ)) := by
    have h := congrArg (fun t : ℤ => (M : ℤ) * t) hg'
    calc (M : ℤ) * (((n : ℤ) * ((n - 1 : ℕ) : ℤ)) + (Isolated c : ℤ))
        = (M : ℤ) * (((n : ℤ) * ((n - 1 : ℕ) : ℤ)) + (Isolated c : ℤ)) := rfl
      _ = (M : ℤ) * (((n : ℤ) * (k : ℤ)) + (Paths c : ℤ)) := h
  have hstep1 : (Paths c : ℤ) + (M : ℤ) * (((n : ℤ) * ((n - 1 : ℕ) : ℤ)))
      ≤ (M : ℤ) * (((n : ℤ) * (k : ℤ)) + (Paths c : ℤ)) := by linarith
  have h6' : 6 * (Paths c : ℤ) ≤ (n : ℤ) * ((n - 1 : ℕ) : ℤ) := by exact_mod_cast h6
  have hmul2 : 6 * (Paths c : ℤ) * ((M : ℤ) - 1)
      ≤ ((n : ℤ) * ((n - 1 : ℕ) : ℤ)) * ((M : ℤ) - 1) :=
    mul_le_mul_of_nonneg_right (a := (M : ℤ) - 1) h6' (by linarith)
  have hstep3 : 6 * ((M : ℤ) * (Paths c : ℤ)) - 6 * (Paths c : ℤ)
      ≤ (M : ℤ) * (((n : ℤ) * ((n - 1 : ℕ) : ℤ))) - (n : ℤ) * ((n - 1 : ℕ) : ℤ) := by
    convert hmul2 using 1 <;> ring
  have hstep4 : 6 * ((Paths c : ℤ) + (M : ℤ) * (((n : ℤ) * ((n - 1 : ℕ) : ℤ))))
      ≤ 6 * ((M : ℤ) * (((n : ℤ) * (k : ℤ)) + (Paths c : ℤ))) :=
    mul_le_mul_of_nonneg_left (a := (6 : ℤ)) hstep1 (by norm_num)
  have hfinal : (5 * (M : ℤ) + 1) * ((n : ℤ) * ((n - 1 : ℕ) : ℤ))
      ≤ 6 * (M : ℤ) * ((n : ℤ) * (k : ℤ)) := by linarith
  have hh : (5 * M + 1) * (n * (n - 1)) ≤ 6 * M * (n * k) := by exact_mod_cast hfinal
  have hfin : n * ((n - 1) * (5 * M + 1)) ≤ n * (6 * M * k) := by
    calc n * ((n - 1) * (5 * M + 1)) = (5 * M + 1) * (n * (n - 1)) := by ring
      _ ≤ 6 * M * (n * k) := hh
      _ = n * (6 * M * k) := by ring
  exact le_of_mul_le_mul_left hfin (by omega)

/-- **THE SHARP FORM, IN UNITS OF COLOURS SAVED.**  If no `(leaf colour, apex)` pair carries more
than `M` two-edge paths, an admissible colouring saves at most `(M-1)(n-1)/(6M)` colours below
`n-1`.  For `M = 1` nothing can be saved at all. -/
theorem deficit_le {M : ℕ} (hc : Admissible c) (hn : 4 ≤ n) (hM : 1 ≤ M)
    (hmul : ∀ y : Fin k × Verts n,
      ((cherryFinset c).filter fun p => apexPair c p = y).card ≤ M) :
    6 * M * (n - 1 - k) ≤ (M - 1) * (n - 1) := by
  have h := apexBound hc hn hM hmul
  by_cases hk : k ≤ n - 1
  · have hsum : (M - 1) + (5 * M + 1) = 6 * M := by
      have hM1 : (M - 1) + 1 = M := Nat.sub_add_cancel hM
      omega
    have hd : (M - 1) * (n - 1) + (n - 1) * (5 * M + 1)
        = (n - 1) * ((M - 1) + (5 * M + 1)) := by
      calc (M - 1) * (n - 1) + (n - 1) * (5 * M + 1)
          = (n - 1) * (M - 1) + (n - 1) * (5 * M + 1) := by
            rw [Nat.mul_comm (M - 1) (n - 1)]
          _ = (n - 1) * ((M - 1) + (5 * M + 1)) := (Nat.mul_add (n - 1) (M - 1) (5 * M + 1)).symm
    have hrel : (M - 1) * (n - 1) + (n - 1) * (5 * M + 1) = 6 * M * (n - 1) := by
      rw [hd, hsum]
      ring
    have h2 : (n - 1 - k) + k = n - 1 := Nat.sub_add_cancel hk
    have hh := Nat.mul_add M (n - 1 - k) k
    have h5 : 6 * M * (n - 1 - k) + 6 * M * k = 6 * M * (n - 1) := by
      calc 6 * M * (n - 1 - k) + 6 * M * k = 6 * (M * (n - 1 - k) + M * k) := by ring
        _ = 6 * (M * ((n - 1 - k) + k)) := by rw [hh]
        _ = 6 * M * (n - 1) := by rw [h2]; ring
    omega
  · have hz : n - 1 - k = 0 := Nat.sub_eq_zero_of_le (by omega)
    simp [hz]

/-- **NO SAVING WITHOUT REPETITION.**  If the leaf-colours of the two-edge paths are distinct at
each apex (no `(leaf colour, apex)` pair carries two paths), the colouring uses **at least `n-1`
colours**.  This is the case `M = 1` of `deficit_le`, and it explains why a colouring whose colour
classes are single edges — the regime of `Construction.lean`'s round-robin and of `Ghost.lean` —
cannot be beaten below `n-1` by any rearrangement that keeps the leaf-colours distinct. -/
theorem k_ge_of_unique_apexPair {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n)
    (h : Set.InjOn (apexPair c) ↑(cherryFinset c)) : n - 1 ≤ k := by
  have hmul : ∀ y : Fin k × Verts n,
      ((cherryFinset c).filter fun p => apexPair c p = y).card ≤ 1 := by
    intro y
    refine Finset.card_le_one.mpr ?_
    intro p hp q hq
    have hp1 : p ∈ cherryFinset c := (Finset.mem_filter.mp hp).1
    have hp2 : apexPair c p = y := (Finset.mem_filter.mp hp).2
    have hq1 : q ∈ cherryFinset c := (Finset.mem_filter.mp hq).1
    have hq2 : apexPair c q = y := (Finset.mem_filter.mp hq).2
    exact h hp1 hq1 (hp2.trans hq2.symm)
  have h1 := deficit_le hc hn (by omega) hmul
  omega

/-- **NO PATH, NO SAVING.**  A colouring whose colour classes are single edges (`Paths c = 0`) uses
at least `n-1` colours, directly from `Surplus.global_identity`.  Together with
`k_ge_of_unique_apexPair` this brackets the whole family: `n-1` colours is the floor of the range of
`f(n,4,5)` below the `n - 1` line, and the sharp counting bound `5(n-1)/6` of `Cherry.lean` is the
ceiling above it. -/
theorem k_ge_of_no_path {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n) (h0 : Paths c = 0) :
    n - 1 ≤ k := by
  have hg := global_identity hc
  have h1 : n * (n - 1) ≤ n * k := by omega
  exact le_of_mul_le_mul_left h1 (by omega)

/-! ### §5  The same bound over `ℝ`, and what it forces -/

/-- **THE SAME BOUND OVER `ℝ`, in the form the headline uses.**  With apex multiplicity at most `M`,

    `5(n-1)/6 + (n-1)/(6M) ≤ f(n,4,5)`,

so the improvement over the sharp counting bound `5(n-1)/6` of `Cherry.five_sixth_lower` is
`(n-1)/(6M)`, and letting `M` grow reproduces `Cherry.EG_ge_five_sixth_real`.  This is a *second
order* statement: the better a construction does against `5n/6`, the more the leaf-colours of its
two-edge paths must repeat at their apexes. -/
theorem apexBound_real {M : ℕ} (hc : Admissible c) (hn : 4 ≤ n) (hM : 1 ≤ M)
    (hmul : ∀ y : Fin k × Verts n,
      ((cherryFinset c).filter fun p => apexPair c p = y).card ≤ M) :
    5 * ((n - 1 : ℕ) : ℝ) / 6 + ((n - 1 : ℕ) : ℝ) / (6 * (M : ℝ)) ≤ (k : ℝ) := by
  have h := apexBound hc hn hM hmul
  have h'' : ((n - 1 : ℕ) : ℝ) * (5 * (M : ℝ) + 1) ≤ 6 * (M : ℝ) * (k : ℝ) := by
    exact_mod_cast h
  calc 5 * ((n - 1 : ℕ) : ℝ) / 6 + ((n - 1 : ℕ) : ℝ) / (6 * (M : ℝ))
      = ((n - 1 : ℕ) : ℝ) * (5 * (M : ℝ) + 1) / (6 * (M : ℝ)) := by
        field_simp
    _ ≤ (k : ℝ) := by
        have hsim : ((n - 1 : ℕ) : ℝ) * (5 * (M : ℝ) + 1) ≤ (k : ℝ) * (6 * (M : ℝ)) := by
          linarith
        exact (div_le_iff₀ (b := ((n - 1 : ℕ) : ℝ) * (5 * (M : ℝ) + 1)) (a := (k : ℝ))
          (c := 6 * (M : ℝ)) (by positivity : (0 : ℝ) < 6 * M)).2 hsim

/-! ### §5  The number of colours a colouring can save below `n-1` -/

/-- **HOW MUCH MUST REPEAT.**  If an admissible colouring saves more than `(M-1)(n-1)/(6M)`
colours below `n-1`, then **some `(leaf colour, apex)` pair carries more than `M` two-edge paths**:
the leaf-colours of the paths at one apex cannot all be distinct, and the cheaper the colouring,
the worse the repetition. -/
theorem exists_fibre_gt_of_deficit {M : ℕ} (hc : Admissible c) (hn : 4 ≤ n) (hM : 1 ≤ M)
    (hd : 6 * M * (n - 1 - k) > (M - 1) * (n - 1)) :
    ∃ y : Fin k × Verts n, M < ((cherryFinset c).filter fun p => apexPair c p = y).card := by
  by_contra hcon
  have hmul : ∀ z : Fin k × Verts n,
      ((cherryFinset c).filter fun p => apexPair c p = z).card ≤ M := by
    intro z
    exact Nat.le_of_not_gt (not_exists.mp hcon z)
  have hle := deficit_le hc hn hM hmul
  omega

end JSP140
