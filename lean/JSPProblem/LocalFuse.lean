import JSPProblem.Fusion

/-!
# JSP-000140 — round 87: THE LOCALISED FUSION — the last colour-class surgery, and its exact price

Rounds 84–86 turned the basic move of the search programs of rounds 65–77 — **fusing two colour
classes** — into mathematics, in three successive forms:

* `Fusion.fuseCol_admissible_iff` (round 84): two colour classes may be merged iff no *tight*
  four-set meets both of them; `Fusion.optimal_fusion_blocked`: at an `EG`-optimal colouring
  every pair is blocked; `Fusion.EG_le_of_fuseCol`: a legal fusion gives `f(n,4,5) ≤ k - 1`.
* `Fusion.Ladder.saving` (round 85): a *chain* of legal fusions is a finite certificate,
  `f(n,4,5) ≤ (#colours used) - (#rungs)`; `Fusion.Ladder.no_mergedCol` closes it off the
  round-robin family.
* `Fusion.fuseSetCol_admissible_iff`, `Fusion.EG_le_of_fuseSetCol`,
  `Fusion.optimal_setFusion_blocked` (round 86): a whole **set** `I` of colours may be collapsed
  to a representative in one step, saving `|I| - 1` colours — and no set of size `≥ 2` fuses at
  an optimal colouring.

All of those moves are *global*: the recolouring `j ↦ i` is applied to **every** edge of colour
`j`.  The move a local search would actually try is the obvious remaining one: recolour only the
`j`-coloured edges **inside a vertex set** `A ⊆ V`, leaving the rest alone.  This file analyses
that move and shows, in the sharpest form, that it is worth nothing.

* **`Local.localFuseCol c i j A`** — `j ↦ i` on the edges of `K_A` only; `A = V` recovers
  `Fusion.fuseCol` (`Local.colorsOn_localFuseCol_univ`).
* **`Local.Confined c j A`** — every `j`-coloured edge of `K_n` lies inside `A`.

> **THE LOCALISATION THEOREM.**  Under confinement the localised fusion has *exactly* the effect of
> the global fusion on every vertex set (`Local.colorsOn_localFuseCol_eq_colorsOn_fuseCol_of_confinement`),
> hence the same admissibility (`Local.localFuseCol_admissible_iff_of_confinement`).  Consequently
> `Local.optimal_localFuse_blocked`: at an `EG`-optimal colouring **no confined localised fusion is
> admissible**, and `Local.localFuse_is_not_a_move_at_optimal`: at an `EG`-optimal colouring every
> *admissible* localised fusion whose target colour is still used keeps the palette **exactly**
> (`card = k`) — it must leave a `j`-coloured edge outside `A`, or it is not admissible at all.

The same three statements hold for a whole **set** of colours (`Local.localFuseSetCol`,
`Local.ConfinedSet`, `Local.optimal_localSetFusion_blocked`), and the price of a localised *set*
fusion, `Local.card_colorsOn_localFuseSetCol_univ_le`, is *stronger* than round 86's: it replaces
the "used colours" hypothesis by confinement.

§5 adds the four-set census description of the move (`Local.JInside`, `Local.TightAt`,
`Local.card_colorsOn_localFuseCol'`, `Local.localFuseCol_admissible_iff`): the four-sets a
localised fusion breaks are exactly the tight four-sets which carry colour `i` and a `j`-coloured
edge inside `A`; the broken family is monotone in `A` (`Local.TightAt_mono`), and at `A = V` it is
`Tight c i ∩ Tight c j`, i.e. round 84's criterion.

§6 instantiates the no-go at every colouring this development has verified.

With this file the **fusion programme is closed in all four forms**: pairs, chains, sets,
localisations.  The rate-`5/6` construction must be a genuinely different object — as in both
published papers, a probabilistic one.
-/

namespace JSP140

variable {n k : ℕ}

/-! ### §0  Incidence lemmas for `edgeFinset` -/

/-- **THE EDGES INSIDE A VERTEX SET.**  An edge `s(a, b)` with `a ≠ b` is an edge of `K_S` iff both
its endpoints are in `S` (`Definitions.mem_edgeFinset_mk` is one direction). -/
theorem mem_edgeFinset_mk_iff {n : ℕ} {S : Finset (Verts n)} {a b : Verts n} (hab : a ≠ b) :
    s(a, b) ∈ edgeFinset S ↔ a ∈ S ∧ b ∈ S := by
  constructor
  · intro h
    rw [mem_edgeFinset] at h
    have h1 := h.1
    rw [Finset.mem_sym2_iff] at h1
    exact ⟨h1 a (Sym2.mem_mk_left a b), h1 b (Sym2.mem_mk_right a b)⟩
  · intro h
    exact mem_edgeFinset_mk h.1 h.2 hab

/-- Every off-diagonal pair is an edge of the complete graph. -/
theorem mem_edgeFinset_univ {n : ℕ} {e : Sym2 (Verts n)} (he : OffDiag e) :
    e ∈ edgeFinset (Finset.univ : Finset (Verts n)) := by
  rw [mem_edgeFinset]
  exact ⟨Finset.mem_sym2_iff.mpr fun _ _ => Finset.mem_univ _, he⟩

/-- **THE EDGES OF `K_{S ∩ A}` ARE THE COMMON EDGES.**  The set of edges which a localised fusion
`j ↦ i` recolours on a vertex set `S` is `edgeFinset (S ∩ A)`; this identity is what makes the
four-set analysis of §5 a statement about `S ∩ A` alone. -/
theorem mem_edgeFinset_inter {n : ℕ} {S A : Finset (Verts n)} {e : Sym2 (Verts n)}
    (he : OffDiag e) :
    e ∈ edgeFinset (S ∩ A) ↔ e ∈ edgeFinset S ∧ e ∈ edgeFinset A := by
  have hmem : e ∈ edgeFinset (S ∩ A) ↔ e ∈ (S ∩ A).sym2 ∧ OffDiag e := mem_edgeFinset
  have hS : e ∈ edgeFinset S ↔ e ∈ S.sym2 ∧ OffDiag e := mem_edgeFinset
  have hA : e ∈ edgeFinset A ↔ e ∈ A.sym2 ∧ OffDiag e := mem_edgeFinset
  rw [hmem, hS, hA]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨⟨Finset.sym2_mono (fun _ ha => (Finset.mem_inter.mp ha).1) h1, h2⟩,
      ⟨Finset.sym2_mono (fun _ ha => (Finset.mem_inter.mp ha).2) h1, h2⟩⟩
  · rintro ⟨⟨hS1, hS2⟩, ⟨hA1, hA2⟩⟩
    exact ⟨Finset.mem_sym2_iff.mpr (fun x hx => Finset.mem_inter.mpr
      ⟨Finset.mem_sym2_iff.mp hS1 x hx, Finset.mem_sym2_iff.mp hA1 x hx⟩), he⟩

/-- **THE COLOURS ON A VERTEX SET DEPEND ONLY ON ITS EDGES.** -/
theorem colorsOn_eq_of_eq_on {n k : ℕ} {c c' : Col n k} {S : Finset (Verts n)}
    (h : ∀ e, e ∈ edgeFinset S → c e = c' e) : colorsOn c S = colorsOn c' S := by
  show (edgeFinset S).image c = (edgeFinset S).image c'
  exact Finset.image_congr fun _ he => h _ he

/-- The colours of a smaller vertex set are among the colours of a larger one. -/
theorem colorsOn_mono {n k : ℕ} (c : Col n k) {S T : Finset (Verts n)} (hST : S ⊆ T) :
    colorsOn c S ⊆ colorsOn c T := by
  intro x hx
  obtain ⟨e, he, heq⟩ := Finset.mem_image.mp hx
  exact Finset.mem_image.mpr ⟨e, edgeFinset_mono hST he, heq⟩

/-! ### §1  The localised fusion -/

/-- **THE LOCALISED FUSION.**  Colour `j` is recoloured to colour `i` on the edges of the complete
graph on `A` only; every other edge keeps its colour.  `A = V` is the fusion of round 84
(`Local.colorsOn_localFuseCol_univ`), and `A` containing all `j`-edges gives `Fusion.fuseCol` back
on every vertex set (`Local.colorsOn_localFuseCol_eq_colorsOn_fuseCol_of_confinement`). -/
def localFuseCol {n k : ℕ} (c : Col n k) (i j : Fin k) (A : Finset (Verts n)) : Col n k :=
  fun e => if e ∈ edgeFinset A ∧ c e = j then i else c e

@[simp] theorem localFuseCol_apply {n k : ℕ} (c : Col n k) (i j : Fin k)
    (A : Finset (Verts n)) (e : Sym2 (Verts n)) :
    localFuseCol c i j A e = if e ∈ edgeFinset A ∧ c e = j then i else c e := rfl

theorem localFuseCol_eq {n k : ℕ} {c : Col n k} {i j : Fin k} {A : Finset (Verts n)}
    {e : Sym2 (Verts n)} (h : ¬ (e ∈ edgeFinset A ∧ c e = j)) :
    localFuseCol c i j A e = c e := if_neg h

theorem localFuseCol_of {n k : ℕ} {c : Col n k} {i j : Fin k} {A : Finset (Verts n)}
    {e : Sym2 (Verts n)} (h : e ∈ edgeFinset A ∧ c e = j) :
    localFuseCol c i j A e = i := if_pos h

/-- On the *edges* of `K_n` the localised fusion with region `V` is the global fusion.  (On loops
the two may differ, since a loop is not an edge of `K_n` and carries no colour; `colorsOn` never
sees it, which is why the statements here are about `colorsOn` and not about the functions.) -/
theorem localFuseCol_univ_of_offDiag {n k : ℕ} {c : Col n k} {i j : Fin k}
    {e : Sym2 (Verts n)} (he : OffDiag e) :
    localFuseCol c i j (Finset.univ : Finset (Verts n)) e = fuseCol c i j e := by
  have hmem : e ∈ edgeFinset (Finset.univ : Finset (Verts n)) := mem_edgeFinset_univ he
  by_cases hj : c e = j
  · rw [localFuseCol_apply, fuseCol_apply, if_pos (And.intro hmem hj), if_pos hj]
  · rw [localFuseCol_apply, fuseCol_apply, if_neg (fun h => hj h.2), if_neg hj]

/-- **THE GLOBAL FUSION IS THE LOCALISED ONE ON THE WHOLE VERTEX SET.** -/
theorem colorsOn_localFuseCol_univ {n k : ℕ} (c : Col n k) (i j : Fin k) (S : Finset (Verts n)) :
    colorsOn (localFuseCol c i j (Finset.univ : Finset (Verts n))) S
      = colorsOn (fuseCol c i j) S :=
  colorsOn_eq_of_eq_on fun e he => localFuseCol_univ_of_offDiag (mem_edgeFinset.mp he).2

/-- **CONFINEMENT.**  Every edge of colour `j` lies inside the region `A` — the only way a localised
fusion can remove a colour from the palette. -/
def Confined {n k : ℕ} (c : Col n k) (j : Fin k) (A : Finset (Verts n)) : Prop :=
  ∀ e, OffDiag e → c e = j → e ∈ edgeFinset A

theorem Confined.univ {n k : ℕ} (c : Col n k) (j : Fin k) :
    Confined c j (Finset.univ : Finset (Verts n)) :=
  fun _ he _ => mem_edgeFinset_univ he

/-- A failing `Confined` instance is witnessed by an off-diagonal `j`-coloured edge outside `A`. -/
theorem exists_escaped_of_not_Confined {n k : ℕ} {c : Col n k} {j : Fin k}
    {A : Finset (Verts n)} (hne : ¬ Confined c j A) :
    ∃ e : Sym2 (Verts n), OffDiag e ∧ c e = j ∧ e ∉ edgeFinset A := by
  rw [Confined, not_forall] at hne
  obtain ⟨e, hnot⟩ := hne
  obtain ⟨hOD, hnc⟩ := not_imp.mp hnot
  obtain ⟨hcj, hnotA⟩ := not_imp.mp hnc
  exact ⟨e, hOD, hcj, hnotA⟩

/-- **THE LOCALISATION THEOREM, FOUR-SET BY FOUR-SET.**  If every `j`-coloured edge lies inside `A`
then the localised fusion has *exactly* the effect of the global fusion on every vertex set: a
confined localised fusion is not a new move, it is round 84's move. -/
theorem colorsOn_localFuseCol_eq_colorsOn_fuseCol_of_confinement {n k : ℕ} {c : Col n k}
    {i j : Fin k} {A : Finset (Verts n)} (hconf : Confined c j A) (S : Finset (Verts n)) :
    colorsOn (localFuseCol c i j A) S = colorsOn (fuseCol c i j) S := by
  refine colorsOn_eq_of_eq_on fun e he => ?_
  have hOD : OffDiag e := (mem_edgeFinset.mp he).2
  by_cases hj : c e = j
  · rw [localFuseCol_apply, fuseCol_apply, if_pos (And.intro (hconf e hOD hj) hj), if_pos hj]
  · rw [localFuseCol_apply, fuseCol_apply, if_neg (fun h => hj h.2), if_neg hj]

/-- **A CONFINED LOCALISED FUSION IS ADMISSIBLE IFF THE GLOBAL FUSION IS.** -/
theorem localFuseCol_admissible_iff_of_confinement {n k : ℕ} {c : Col n k} {i j : Fin k}
    {A : Finset (Verts n)} (hconf : Confined c j A) :
    Admissible (localFuseCol c i j A) ↔ Admissible (fuseCol c i j) := by
  constructor
  · intro hf S hS
    have h := hf S hS
    rwa [colorsOn_localFuseCol_eq_colorsOn_fuseCol_of_confinement hconf] at h
  · intro hf S hS
    have h := hf S hS
    rwa [← colorsOn_localFuseCol_eq_colorsOn_fuseCol_of_confinement hconf] at h

/-- **AT `A = V` NOTHING NEW HAPPENS** — the localised fusion is round 84's fusion. -/
theorem localFuseCol_admissible_iff_univ {n k : ℕ} {c : Col n k} {i j : Fin k} :
    Admissible (localFuseCol c i j (Finset.univ : Finset (Verts n))) ↔ Admissible (fuseCol c i j) :=
  localFuseCol_admissible_iff_of_confinement (Confined.univ c j)

/-! ### §2  The price: exactly one colour, and only under confinement -/

/-- **THE COLOUR `j` SURVIVES THE FUSION IFF THE REGION DOES NOT CONTAIN ALL OF ITS CLASS.**  This
is the whole content of the move on the palette: `j` is gone from the palette of the localised
fusion exactly when it is gone from the palette of `c`. -/
theorem mem_colorsOn_localFuseCol_univ_j {n k : ℕ} {c : Col n k} {i j : Fin k}
    {A : Finset (Verts n)} (hij : i ≠ j) :
    j ∈ colorsOn (localFuseCol c i j A) (Finset.univ : Finset (Verts n)) ↔ ¬ Confined c j A := by
  classical
  constructor
  · intro hx
    obtain ⟨e, he, heq⟩ := Finset.mem_image.mp hx
    have hOD : OffDiag e := (mem_edgeFinset.mp he).2
    have hne : ¬ (e ∈ edgeFinset A ∧ c e = j) := by
      intro h
      rw [localFuseCol_apply, if_pos h] at heq
      exact hij heq
    have hcj : c e = j := by
      by_contra hcj
      rw [localFuseCol_apply, if_neg hne] at heq
      exact hcj heq
    exact fun hconf => hne (And.intro (hconf e hOD hcj) hcj)
  · intro hne
    obtain ⟨e, hOD, hcj, hnot⟩ := exists_escaped_of_not_Confined hne
    refine Finset.mem_image.mpr ⟨e, mem_edgeFinset_univ hOD, ?_⟩
    rw [localFuseCol_apply, if_neg (fun h => hnot (And.left h))]
    exact hcj

/-- **A CONFINED LOCALISED FUSION SAVES A COLOUR** — the same price as round 84's global fusion,
neither more nor less (measured against the palette, exactly as in
`Fusion.card_colorsOn_fuseCol_univ_le`). -/
theorem card_colorsOn_localFuseCol_univ_le {n k : ℕ} {c : Col n k} {i j : Fin k}
    {A : Finset (Verts n)} (hconf : Confined c j A) (hij : i ≠ j) (hk : 0 < k) (hn : 2 ≤ n) :
    (colorsOn (localFuseCol c i j A) (Finset.univ : Finset (Verts n))).card ≤ k - 1 := by
  rw [colorsOn_localFuseCol_eq_colorsOn_fuseCol_of_confinement hconf]
  exact card_colorsOn_fuseCol_univ_le i j hij hk hn

/-- **THE SHARP PRICE: A CONFINED LOCALISED FUSION REPLACES THE PALETTE BY ITS ERASURE OF `j`.**
Every colour other than `j` survives on the whole vertex set (`i` was already used, and no
`j`-edge lies outside `A`), so the palette of the localised fusion is *literally* the palette of
`c` with `j` deleted. -/
theorem colorsOn_localFuseCol_univ_eq_of_confinement {n k : ℕ} {c : Col n k} {i j : Fin k}
    {A : Finset (Verts n)} (hconf : Confined c j A) (hij : i ≠ j)
    (hi : i ∈ colorsOn c (Finset.univ : Finset (Verts n))) :
    colorsOn (localFuseCol c i j A) (Finset.univ : Finset (Verts n))
      = (colorsOn c (Finset.univ : Finset (Verts n))).erase j := by
  classical
  have h1 : colorsOn (localFuseCol c i j A) (Finset.univ : Finset (Verts n))
      ⊆ (colorsOn c (Finset.univ : Finset (Verts n))).erase j := by
    intro x hx
    obtain ⟨e, he, heq⟩ := Finset.mem_image.mp hx
    have hOD : OffDiag e := (mem_edgeFinset.mp he).2
    refine Finset.mem_erase.mpr ⟨?_, ?_⟩
    · intro hxj
      by_cases h : e ∈ edgeFinset A ∧ c e = j
      · rw [localFuseCol_apply, if_pos h] at heq
        exact hij (heq.trans hxj)
      · rw [localFuseCol_apply, if_neg h] at heq
        exact h ⟨hconf e hOD (heq.trans hxj), heq.trans hxj⟩
    · by_cases h : e ∈ edgeFinset A ∧ c e = j
      · rw [localFuseCol_apply, if_pos h] at heq
        exact by rw [heq.symm]; exact hi
      · rw [localFuseCol_apply, if_neg h] at heq
        exact Finset.mem_image.mpr ⟨e, he, heq⟩
  have h2 : (colorsOn c (Finset.univ : Finset (Verts n))).erase j
      ⊆ colorsOn (localFuseCol c i j A) (Finset.univ : Finset (Verts n)) := by
    intro x hx
    rw [Finset.mem_erase] at hx
    obtain ⟨e, he, hxc⟩ := Finset.mem_image.mp hx.2
    by_cases h : e ∈ edgeFinset A ∧ c e = j
    · exact False.elim (absurd (hxc.symm.trans h.2) hx.1)
    · exact Finset.mem_image.mpr ⟨e, he, by rw [localFuseCol_apply, if_neg h]; exact hxc⟩
  exact Finset.Subset.antisymm h1 h2

/-- **AND THEREFORE IT LOSES AT MOST THE COLOUR `j`.** -/
theorem card_colorsOn_localFuseCol_univ_eq_of_confinement {n k : ℕ} {c : Col n k} {i j : Fin k}
    {A : Finset (Verts n)} (hconf : Confined c j A) (hij : i ≠ j)
    (hi : i ∈ colorsOn c (Finset.univ : Finset (Verts n))) :
    (colorsOn (localFuseCol c i j A) (Finset.univ : Finset (Verts n))).card
      = ((colorsOn c (Finset.univ : Finset (Verts n))).erase j).card := by
  rw [colorsOn_localFuseCol_univ_eq_of_confinement hconf hij hi]

/-- **AND THEREFORE, IF `j` IS USED, EXACTLY ONE COLOUR.**  This is the hypothesis set of a
productive localised fusion: the target colour is used and the fused colour is used. -/
theorem card_colorsOn_localFuseCol_univ_eq {n k : ℕ} {c : Col n k} {i j : Fin k}
    {A : Finset (Verts n)} (hconf : Confined c j A) (hij : i ≠ j)
    (hi : i ∈ colorsOn c (Finset.univ : Finset (Verts n)))
    (hj : j ∈ colorsOn c (Finset.univ : Finset (Verts n))) :
    (colorsOn (localFuseCol c i j A) (Finset.univ : Finset (Verts n))).card
      = (colorsOn c (Finset.univ : Finset (Verts n))).card - 1 := by
  rw [colorsOn_localFuseCol_univ_eq_of_confinement hconf hij hi, Finset.card_erase_of_mem hj]

/-- **AN UNCONFINED LOCALISED FUSION SAVES NOTHING**: the palette of `c` embeds in the palette of
the localised fusion, because colour `j` is still there. -/
theorem card_colorsOn_localFuseCol_univ_ge {n k : ℕ} {c : Col n k} {i j : Fin k}
    {A : Finset (Verts n)} (hij : i ≠ j) (hnot : ¬ Confined c j A) :
    (colorsOn c (Finset.univ : Finset (Verts n))).card
      ≤ (colorsOn (localFuseCol c i j A) (Finset.univ : Finset (Verts n))).card := by
  classical
  obtain ⟨e, hOD, hcj, _⟩ := exists_escaped_of_not_Confined hnot
  have hj : j ∈ colorsOn c (Finset.univ : Finset (Verts n)) :=
    Finset.mem_image.mpr ⟨e, mem_edgeFinset_univ hOD, hcj⟩
  have h3 : j ∈ colorsOn (localFuseCol c i j A) (Finset.univ : Finset (Verts n)) :=
    (mem_colorsOn_localFuseCol_univ_j hij).mpr hnot
  have hsub : (colorsOn c (Finset.univ : Finset (Verts n))).erase j
      ⊆ colorsOn (localFuseCol c i j A) (Finset.univ : Finset (Verts n)) := by
    intro x hx
    rw [Finset.mem_erase] at hx
    obtain ⟨e, he, hxc⟩ := Finset.mem_image.mp hx.2
    by_cases h : e ∈ edgeFinset A ∧ c e = j
    · exact False.elim (absurd (hxc.symm.trans h.2) hx.1)
    · refine Finset.mem_image.mpr ⟨e, he, ?_⟩
      rw [localFuseCol_apply, if_neg h]
      exact hxc
  have hpos : 0 < (colorsOn c (Finset.univ : Finset (Verts n))).card := Finset.card_pos.mpr ⟨j, hj⟩
  have hpos' : 0 < (colorsOn (localFuseCol c i j A) (Finset.univ : Finset (Verts n))).card :=
    Finset.card_pos.mpr ⟨j, h3⟩
  have hcard' : (colorsOn c (Finset.univ : Finset (Verts n))).card
      = ((colorsOn c (Finset.univ : Finset (Verts n))).erase j).card + 1 := by
    have h := Finset.card_erase_of_mem hj
    omega
  have hcard'' : ((colorsOn (localFuseCol c i j A) (Finset.univ : Finset (Verts n))).erase j).card + 1
      = (colorsOn (localFuseCol c i j A) (Finset.univ : Finset (Verts n))).card := by
    have h := Finset.card_erase_of_mem h3
    omega
  calc (colorsOn c (Finset.univ : Finset (Verts n))).card
      = ((colorsOn c (Finset.univ : Finset (Verts n))).erase j).card + 1 := hcard'
    _ ≤ ((colorsOn (localFuseCol c i j A) (Finset.univ : Finset (Verts n))).erase j).card + 1 := by
        have hsub' : (colorsOn c (Finset.univ : Finset (Verts n))).erase j
            ⊆ (colorsOn (localFuseCol c i j A) (Finset.univ : Finset (Verts n))).erase j := by
          intro x hx
          exact Finset.mem_erase.mpr
            ⟨Finset.mem_erase.mp hx |>.1, hsub (Finset.mem_erase.mpr (Finset.mem_erase.mp hx))⟩
        exact Nat.succ_le_succ (Finset.card_le_card hsub')
    _ = (colorsOn (localFuseCol c i j A) (Finset.univ : Finset (Verts n))).card := hcard''

/-- **AN UNCONFINED LOCALISED FUSION WITH A USED TARGET COLOUR CHANGES NOTHING AT ALL**: the
palette is *identical*, because colour `j` survives and colour `i` was already there.  Together
with `Local.card_colorsOn_localFuseCol_univ_ge` this is the exact dichotomy of §2. -/
theorem card_colorsOn_localFuseCol_univ_eq_of_escaped {n k : ℕ} {c : Col n k} {i j : Fin k}
    {A : Finset (Verts n)} (hij : i ≠ j) (hnot : ¬ Confined c j A)
    (hi : i ∈ colorsOn c (Finset.univ : Finset (Verts n))) :
    (colorsOn (localFuseCol c i j A) (Finset.univ : Finset (Verts n))).card
      = (colorsOn c (Finset.univ : Finset (Verts n))).card := by
  classical
  have hsub : colorsOn (localFuseCol c i j A) (Finset.univ : Finset (Verts n))
      ⊆ colorsOn c (Finset.univ : Finset (Verts n)) := by
    intro x hx
    obtain ⟨e, he, heq⟩ := Finset.mem_image.mp hx
    by_cases h : e ∈ edgeFinset A ∧ c e = j
    · rw [localFuseCol_apply, if_pos h] at heq
      exact by rw [heq.symm]; exact hi
    · rw [localFuseCol_apply, if_neg h] at heq
      exact Finset.mem_image.mpr ⟨e, he, heq⟩
  exact le_antisymm (Finset.card_le_card hsub)
    (card_colorsOn_localFuseCol_univ_ge hij hnot)

/-- **A CONFINED LOCALISED FUSION IS AN UPPER-BOUND CERTIFICATE FOR `f(n,4,5)`**: exactly as in
round 84's `Fusion.EG_le_of_fuseCol`, but the recolouring may be restricted to a region. -/
theorem EG_le_of_localFuseCol {n k : ℕ} {c : Col n k} (hc : Admissible c) {i j : Fin k}
    {A : Finset (Verts n)} (hconf : Confined c j A) (hij : i ≠ j)
    (hi : i ∈ colorsOn c (Finset.univ : Finset (Verts n)))
    (hj : j ∈ colorsOn c (Finset.univ : Finset (Verts n))) (hn : 2 ≤ n)
    (hf : Admissible (localFuseCol c i j A)) :
    EG n ≤ (colorsOn c (Finset.univ : Finset (Verts n))).card - 1 :=
  le_trans (EG_le_used hf hn) (Nat.le_of_eq (card_colorsOn_localFuseCol_univ_eq hconf hij hi hj))

/-! ### §3  The no-go: localisation buys nothing at an optimal colouring -/

/-- **AT AN `EG`-OPTIMAL COLOURING A CONFINED LOCALISED FUSION IS NEVER ADMISSIBLE.**  Round 84's
`optimal_fusion_blocked`, unchanged, for every region `A` of every colouring which already uses
`EG n` colours. -/
theorem optimal_localFuse_blocked {n k : ℕ} {c : Col n k} (hc : Admissible c) (hopt : EG n = k)
    (hk : 2 ≤ k) (hn : 2 ≤ n) {i j : Fin k} (hij : i ≠ j) {A : Finset (Verts n)}
    (hconf : Confined c j A) : ¬ Admissible (localFuseCol c i j A) := by
  rw [localFuseCol_admissible_iff_of_confinement hconf]
  exact (fuseCol_not_admissible_iff hc i j hij).mpr (optimal_fusion_blocked hc hopt hk hn i j hij)

/-- **A LEGAL LOCALISED FUSION AT AN OPTIMAL COLOURING MUST KEEP THE COLOUR ALIVE.**  If
`Admissible (localFuseCol c i j A)` and `c` is `EG`-optimal, then the region `A` does *not*
contain the colour class `j`: some `j`-coloured edge survives outside `A`, so the move is legal
but worthless.  This is the local-search form of round 84's no-go. -/
theorem not_Confined_of_localFuse_admissible {n k : ℕ} {c : Col n k} (hc : Admissible c)
    (hopt : EG n = k) (hk : 2 ≤ k) (hn : 2 ≤ n) {i j : Fin k} (hij : i ≠ j)
    {A : Finset (Verts n)} (hf : Admissible (localFuseCol c i j A)) : ¬ Confined c j A :=
  fun hconf => optimal_localFuse_blocked hc hopt hk hn hij hconf hf

/-- **THE SHARP FORM: AT AN `EG`-OPTIMAL COLOURING A LEGAL LOCALISED FUSION CHANGES NOTHING.**
The number of colours of the localised fusion is *exactly* `EG n`: the move is admissible only
outside the confined regions, and there it keeps `j`. -/
theorem localFuse_is_not_a_move_at_optimal {n k : ℕ} {c : Col n k} (hc : Admissible c)
    (hopt : EG n = k) (hk : 2 ≤ k) (hn : 2 ≤ n) {i j : Fin k} (hij : i ≠ j)
    {A : Finset (Verts n)} (hf : Admissible (localFuseCol c i j A))
    (hi : i ∈ colorsOn c (Finset.univ : Finset (Verts n))) :
    (colorsOn (localFuseCol c i j A) (Finset.univ : Finset (Verts n))).card = k := by
  have hge : EG n ≤ (colorsOn (localFuseCol c i j A) (Finset.univ : Finset (Verts n))).card :=
    EG_le_used hf hn
  have hnot : ¬ Confined c j A := not_Confined_of_localFuse_admissible hc hopt hk hn hij hf
  have heq := card_colorsOn_localFuseCol_univ_eq_of_escaped hij hnot hi
  have hk' : (colorsOn c (Finset.univ : Finset (Verts n))).card ≤ k := by
    calc (colorsOn c (Finset.univ : Finset (Verts n))).card
        ≤ (Finset.univ : Finset (Fin k)).card := Finset.card_le_card (Finset.subset_univ _)
      _ = k := by rw [Finset.card_univ, Fintype.card_fin]
  rw [hopt] at hge
  omega

/-! ### §4  The same three statements for a whole set of colours -/

/-- **THE LOCALISED SET FUSION**: the colours of `I` are collapsed to `r ∈ I` on the edges of
`K_A` only. -/
def localFuseSetCol {n k : ℕ} (c : Col n k) (r : Fin k) (I : Finset (Fin k))
    (A : Finset (Verts n)) : Col n k :=
  fun e => if e ∈ edgeFinset A ∧ c e ∈ I then r else c e

@[simp] theorem localFuseSetCol_apply {n k : ℕ} (c : Col n k) (r : Fin k) (I : Finset (Fin k))
    (A : Finset (Verts n)) (e : Sym2 (Verts n)) :
    localFuseSetCol c r I A e = if e ∈ edgeFinset A ∧ c e ∈ I then r else c e := rfl

theorem localFuseSetCol_univ_of_offDiag {n k : ℕ} {c : Col n k} {r : Fin k}
    {I : Finset (Fin k)} {e : Sym2 (Verts n)} (he : OffDiag e) :
    localFuseSetCol c r I (Finset.univ : Finset (Verts n)) e = fuseSetCol c r I e := by
  have hmem : e ∈ edgeFinset (Finset.univ : Finset (Verts n)) := mem_edgeFinset_univ he
  by_cases hc : c e ∈ I
  · rw [localFuseSetCol_apply, fuseSetCol_apply, if_pos (And.intro hmem hc), if_pos hc]
  · rw [localFuseSetCol_apply, fuseSetCol_apply, if_neg (fun h => hc h.2), if_neg hc]

/-- **CONFINEMENT OF A SET OF COLOURS.** -/
def ConfinedSet {n k : ℕ} (c : Col n k) (I : Finset (Fin k)) (A : Finset (Verts n)) : Prop :=
  ∀ e, OffDiag e → c e ∈ I → e ∈ edgeFinset A

theorem ConfinedSet.univ {n k : ℕ} (c : Col n k) (I : Finset (Fin k)) :
    ConfinedSet c I (Finset.univ : Finset (Verts n)) :=
  fun _ he _ => mem_edgeFinset_univ he

/-- **THE LOCALISATION THEOREM FOR SETS.** -/
theorem colorsOn_localFuseSetCol_eq_colorsOn_fuseSetCol_of_confinement {n k : ℕ} {c : Col n k}
    {r : Fin k} {I : Finset (Fin k)} {A : Finset (Verts n)} (hconf : ConfinedSet c I A)
    (S : Finset (Verts n)) :
    colorsOn (localFuseSetCol c r I A) S = colorsOn (fuseSetCol c r I) S := by
  refine colorsOn_eq_of_eq_on fun e he => ?_
  have hOD : OffDiag e := (mem_edgeFinset.mp he).2
  by_cases hc : c e ∈ I
  · rw [localFuseSetCol_apply, fuseSetCol_apply, if_pos (And.intro (hconf e hOD hc) hc), if_pos hc]
  · rw [localFuseSetCol_apply, fuseSetCol_apply, if_neg (fun h => hc h.2), if_neg hc]

/-- **THE PRICE OF A CONFINED LOCALISED SET FUSION**, `|I| - 1` colours at once — round 86's
`Fusion.card_colorsOn_fuseSetCol_univ_le` with the *used colours* hypothesis (`I ⊆ palette`)
replaced by confinement, which is what a localised move actually guarantees. -/
theorem card_colorsOn_localFuseSetCol_univ_le {n k : ℕ} {c : Col n k} {r : Fin k}
    {I : Finset (Fin k)} {A : Finset (Verts n)} (hr : r ∈ I) (hconf : ConfinedSet c I A)
    (hk : 0 < k) :
    (colorsOn (localFuseSetCol c r I A) (Finset.univ : Finset (Verts n))).card
      ≤ k - I.card + 1 := by
  classical
  have hsub : colorsOn (localFuseSetCol c r I A) (Finset.univ : Finset (Verts n))
      ⊆ ((Finset.univ : Finset (Fin k)) \ I) ∪ {r} := by
    intro x hx
    obtain ⟨e, he, heq⟩ := Finset.mem_image.mp hx
    have hOD : OffDiag e := (mem_edgeFinset.mp he).2
    by_cases h : e ∈ edgeFinset A ∧ c e ∈ I
    · rw [localFuseSetCol_apply, if_pos h] at heq
      exact Finset.mem_union_right _ (Finset.mem_singleton.mpr heq.symm)
    · rw [localFuseSetCol_apply, if_neg h] at heq
      refine Finset.mem_union_left _ ?_
      rw [Finset.mem_sdiff]
      refine ⟨Finset.mem_univ _, fun hxI => ?_⟩
      exact h (And.intro (hconf e hOD (by rw [heq]; exact hxI)) (by rw [heq]; exact hxI))
  have hcard : (((Finset.univ : Finset (Fin k)) \ I) ∪ {r}).card = k - I.card + 1 := by
    have hd : Disjoint ((Finset.univ : Finset (Fin k)) \ I) ({r} : Finset (Fin k)) :=
      Finset.disjoint_left.mpr fun x hx1 hx2 => by
        rw [Finset.mem_singleton] at hx2
        rw [hx2] at hx1
        rw [Finset.mem_sdiff] at hx1
        exact hx1.2 hr
    rw [Finset.card_union_of_disjoint hd, Finset.card_singleton,
      Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin]
  calc (colorsOn (localFuseSetCol c r I A) (Finset.univ : Finset (Verts n))).card
      ≤ (((Finset.univ : Finset (Fin k)) \ I) ∪ {r}).card := Finset.card_le_card hsub
    _ = k - I.card + 1 := hcard

/-- **A CONFINED LOCALISED SET FUSION IS AN UPPER-BOUND CERTIFICATE FOR `f(n,4,5)`** — round 86's
`Fusion.EG_le_of_fuseSetCol` with confinement in place of usedness. -/
theorem EG_le_of_localFuseSetCol {n k : ℕ} {c : Col n k} (hc : Admissible c) {r : Fin k}
    {I : Finset (Fin k)} {A : Finset (Verts n)} (hr : r ∈ I) (hconf : ConfinedSet c I A)
    (hk : 0 < k) (hn : 2 ≤ n) (hc5 : MultiMeet c 5 2 I = ∅) (hc6 : MultiMeet c 6 3 I = ∅) :
    EG n ≤ k - I.card + 1 := by
  have hf : Admissible (localFuseSetCol c r I A) := by
    rw [Admissible]
    intro S hS
    have h := (fuseSetCol_admissible_iff hc hr).mpr ⟨hc5, hc6⟩ S hS
    rwa [← colorsOn_localFuseSetCol_eq_colorsOn_fuseSetCol_of_confinement hconf] at h
  exact le_trans (EG_le_used hf hn) (card_colorsOn_localFuseSetCol_univ_le hr hconf hk)

/-- **AT AN `EG`-OPTIMAL COLOURING NO CONFINED LOCALISED SET FUSION OF SIZE `≥ 2` IS ADMISSIBLE.**
Round 86's `Fusion.optimal_setFusion_blocked`, unchanged, for every region `A`. -/
theorem optimal_localSetFusion_blocked {n k : ℕ} {c : Col n k} (hc : Admissible c)
    (hopt : EG n = k) (hk : 0 < k) (hn : 2 ≤ n) {r : Fin k} {I : Finset (Fin k)}
    {A : Finset (Verts n)} (hr : r ∈ I) (hI2 : 2 ≤ I.card) (hconf : ConfinedSet c I A)
    (hf : Admissible (localFuseSetCol c r I A)) : False := by
  have h1 : EG n ≤ (colorsOn (localFuseSetCol c r I A) (Finset.univ : Finset (Verts n))).card :=
    EG_le_used hf hn
  have h2 := card_colorsOn_localFuseSetCol_univ_le hr hconf hk
  have hIc : I.card ≤ k := by
    have := Finset.card_le_card (Finset.subset_univ (I : Finset (Fin k)))
    rwa [Finset.card_univ, Fintype.card_fin] at this
  have h3 : k - I.card + 1 ≤ k := by omega
  rw [hopt] at h1
  omega

/-! ### §5  Which four-sets a localised fusion breaks -/

/-- **CONFINEMENT ON ONE VERTEX SET**: every `j`-coloured edge of `K_S` lies inside `A`.  This is
the local version of `Local.Confined`, and it is what decides whether colour `j` disappears from
`S`. -/
def JInside {n k : ℕ} (c : Col n k) (j : Fin k) (A S : Finset (Verts n)) : Prop :=
  ∀ e, e ∈ edgeFinset S → c e = j → e ∈ edgeFinset A

/-- **`JInside` IS DECIDABLE** (and computably so: it is a finite check over the edges of `K_S`),
which is what lets the price formula and the criterion `TightAt` be written with `if`. -/
instance jInsideDecidable {n k : ℕ} (c : Col n k) (j : Fin k) (A S : Finset (Verts n)) :
    Decidable (JInside c j A S) := by
  unfold JInside
  infer_instance

theorem JInside.of_univ {n k : ℕ} (c : Col n k) (j : Fin k) (S : Finset (Verts n)) :
    JInside c j (Finset.univ : Finset (Verts n)) S :=
  fun _ he _ => mem_edgeFinset_univ (mem_edgeFinset.mp he).2

/-- `JInside` is monotone in the region. -/
theorem JInside.mono {n k : ℕ} {c : Col n k} {j : Fin k} {A B S : Finset (Verts n)}
    (hJ : JInside c j A S) (hAB : A ⊆ B) : JInside c j B S := by
  intro e he hec
  exact edgeFinset_mono hAB (hJ e he hec)

/-- A failing `JInside` instance is witnessed by a `j`-coloured edge of `K_S` outside `A`. -/
theorem exists_escaped_of_not_JInside {n k : ℕ} {c : Col n k} {j : Fin k}
    {A S : Finset (Verts n)} (hJ : ¬ JInside c j A S) :
    ∃ e : Sym2 (Verts n), e ∈ edgeFinset S ∧ c e = j ∧ e ∉ edgeFinset A := by
  rw [JInside, not_forall] at hJ
  obtain ⟨e, hnot⟩ := hJ
  obtain ⟨he, hnc⟩ := not_imp.mp hnot
  obtain ⟨hcj, hnotA⟩ := not_imp.mp hnc
  exact ⟨e, he, hcj, hnotA⟩

/-- Under `JInside` the colour `j` really does occur on an edge inside `A`. -/
theorem mem_colorsOn_inter_of_JInside {n k : ℕ} {c : Col n k} {j : Fin k}
    {A S : Finset (Verts n)} (hJ : JInside c j A S) (hj : j ∈ colorsOn c S) :
    j ∈ colorsOn c (S ∩ A) := by
  classical
  obtain ⟨e, he, hce⟩ := Finset.mem_image.mp hj
  have heA : e ∈ edgeFinset A := hJ e he hce
  exact Finset.mem_image.mpr
    ⟨e, (mem_edgeFinset_inter (mem_edgeFinset.mp he).2).mpr ⟨he, heA⟩, hce⟩


/-- **NO RECOLOURING**: if colour `j` does not occur on the edges inside `A`, the localised fusion
changes nothing on `S`. -/
theorem colorsOn_localFuseCol_of_absent {n k : ℕ} {c : Col n k} {i j : Fin k}
    {A S : Finset (Verts n)} (hj : j ∉ colorsOn c (S ∩ A)) :
    colorsOn (localFuseCol c i j A) S = colorsOn c S := by
  refine colorsOn_eq_of_eq_on fun e he => ?_
  by_cases h : e ∈ edgeFinset A ∧ c e = j
  · exact absurd (Finset.mem_image.mpr ⟨e, (mem_edgeFinset_inter (mem_edgeFinset.mp he).2).mpr
      ⟨he, h.1⟩, h.2⟩) hj
  · exact localFuseCol_eq h

/-- **CONFINED ON `S`: THE LOCALISED FUSION REPLACES `j` BY `i` AMONG THE COLOURS OF `S`** — exactly
as the global fusion does, whether or not `i` already occurs on `S`. -/
theorem colorsOn_localFuseCol_of_inside {n k : ℕ} {c : Col n k} {i j : Fin k}
    {A S : Finset (Verts n)} (hij : i ≠ j) (hJ : JInside c j A S) (hj : j ∈ colorsOn c S) :
    colorsOn (localFuseCol c i j A) S = insert i ((colorsOn c S).erase j) := by
  classical
  show (edgeFinset S).image (localFuseCol c i j A) = insert i ((colorsOn c S).erase j)
  rw [colorsOn]
  apply Finset.ext
  intro x
  rw [Finset.mem_image, Finset.mem_insert, Finset.mem_erase, Finset.mem_image]
  constructor
  · intro hx
    obtain ⟨e, he, heq⟩ := hx
    by_cases h : e ∈ edgeFinset A ∧ c e = j
    · left
      rw [localFuseCol_apply, if_pos h] at heq
      exact heq.symm
    · right
      have hxc : c e = x := by
        rw [localFuseCol_apply, if_neg h] at heq
        exact heq
      exact ⟨fun hxj => h ⟨hJ e he (hxc.trans hxj), hxc.trans hxj⟩, ⟨e, he, hxc⟩⟩
  · intro hx
    rcases hx with hxi | ⟨hne, ⟨e, he, hxc⟩⟩
    · rw [hxi]
      by_cases hi : i ∈ colorsOn c S
      · obtain ⟨e, he, hce⟩ := Finset.mem_image.mp hi
        refine ⟨e, he, ?_⟩
        rw [localFuseCol_apply]
        by_cases h : e ∈ edgeFinset A ∧ c e = j
        · rw [if_pos h]
        · rw [if_neg h, hce]
      · obtain ⟨e, he, hce⟩ := Finset.mem_image.mp (mem_colorsOn_inter_of_JInside hJ hj)
        have heA := (mem_edgeFinset_inter (mem_edgeFinset.mp he).2).mp he
        refine ⟨e, heA.1, ?_⟩
        rw [localFuseCol_apply, if_pos ⟨heA.2, hce⟩]
    · refine ⟨e, he, ?_⟩
      rw [localFuseCol_apply]
      by_cases h : e ∈ edgeFinset A ∧ c e = j
      · rw [if_pos h]
        exact False.elim (hne (hxc.symm.trans h.2))
      · rw [if_neg h]
        exact hxc

/-- **NOT CONFINED ON `S`, WITH `i` ALREADY PRESENT: NOTHING CHANGES** — `j` is recoloured where
it lies inside `A`, but it survives outside, and `i` was already there. -/
theorem colorsOn_localFuseCol_of_escaped {n k : ℕ} {c : Col n k} {i j : Fin k}
    {A S : Finset (Verts n)} (hJ : ¬ JInside c j A S) (hi : i ∈ colorsOn c S) :
    colorsOn (localFuseCol c i j A) S = colorsOn c S := by
  classical
  show (edgeFinset S).image (localFuseCol c i j A) = (edgeFinset S).image c
  apply Finset.ext
  intro x
  rw [Finset.mem_image, Finset.mem_image]
  obtain ⟨e0, he0, hcj0, hnotA0⟩ := exists_escaped_of_not_JInside hJ
  constructor
  · rintro ⟨e, he, heq⟩
    by_cases h : e ∈ edgeFinset A ∧ c e = j
    · rw [localFuseCol_apply, if_pos h] at heq
      exact Finset.mem_image.mp (heq ▸ hi)
    · rw [localFuseCol_apply, if_neg h] at heq
      exact ⟨e, he, heq⟩
  · rintro ⟨e, he, heq⟩
    by_cases hxc : c e = j
    · refine ⟨e0, he0, ?_⟩
      show localFuseCol c i j A e0 = x
      rw [localFuseCol_apply]
      rw [if_neg (fun hh : e0 ∈ edgeFinset A ∧ c e0 = j => absurd hh.1 hnotA0), hcj0]
      exact (heq.symm.trans hxc).symm
    · refine ⟨e, he, ?_⟩
      show localFuseCol c i j A e = x
      rw [localFuseCol_apply, if_neg (fun hh : e ∈ edgeFinset A ∧ c e = j => hxc hh.2)]
      exact heq

/-- **NOT CONFINED, WITH `i` ABSENT: A NEW COLOUR APPEARS** — the localised fusion recolours one
`j`-edge inside `A` and keeps another one outside, so `j` stays and `i` is added. -/
theorem colorsOn_localFuseCol_of_escaped_fresh {n k : ℕ} {c : Col n k} {i j : Fin k}
    {A S : Finset (Verts n)} (hJ : ¬ JInside c j A S) (hi : i ∉ colorsOn c S)
    (hj : j ∈ colorsOn c (S ∩ A)) :
    colorsOn (localFuseCol c i j A) S = insert i (colorsOn c S) := by
  classical
  obtain ⟨e0, he0, hcj0, hnotA0⟩ := exists_escaped_of_not_JInside hJ
  show (edgeFinset S).image (localFuseCol c i j A) = insert i ((edgeFinset S).image c)
  apply Finset.ext
  intro x
  rw [Finset.mem_image, Finset.mem_insert, Finset.mem_image]
  constructor
  · intro hx
    obtain ⟨e, he, heq⟩ := hx
    by_cases h : e ∈ edgeFinset A ∧ c e = j
    · left
      rw [localFuseCol_apply, if_pos h] at heq
      exact heq.symm
    · right
      rw [localFuseCol_apply, if_neg h] at heq
      exact ⟨e, he, heq⟩
  · intro hx
    rcases hx with hxi | hrest
    · rw [hxi]
      obtain ⟨e, he, hce⟩ := Finset.mem_image.mp hj
      have heA := (mem_edgeFinset_inter (mem_edgeFinset.mp he).2).mp he
      refine ⟨e, heA.1, ?_⟩
      rw [localFuseCol_apply, if_pos ⟨heA.2, hce⟩]
    · obtain ⟨e, he, hxc⟩ := hrest
      by_cases h : e ∈ edgeFinset A ∧ c e = j
      · refine ⟨e0, he0, ?_⟩
        show localFuseCol c i j A e0 = x
        rw [localFuseCol_apply]
        rw [if_neg (fun hh : e0 ∈ edgeFinset A ∧ c e0 = j => absurd hh.1 hnotA0), hcj0]
        exact (hxc.symm.trans h.2).symm
      · refine ⟨e, he, ?_⟩
        show localFuseCol c i j A e = x
        rw [localFuseCol_apply]
        rw [if_neg (fun hh : e ∈ edgeFinset A ∧ c e = j => h ⟨hh.1, hh.2⟩), hxc]

/-- **THE EXACT CARDINALITY PRICE OF A LOCALISED FUSION ON ONE VERTEX SET.**  A localised fusion
loses a colour exactly when colour `i` is present and all `j`-edges of `S` lie inside `A`, and it
gains one exactly when colour `i` is absent, some `j`-edge inside `A` is recoloured *and* some
`j`-edge of `S` survives outside `A`.  For the pair fusion this is round 86's
`Fusion.card_colorsOn_fuseCol'`. -/
theorem card_colorsOn_localFuseCol' {n k : ℕ} {c : Col n k} {i j : Fin k} {A S : Finset (Verts n)}
    (hij : i ≠ j) :
    (colorsOn (localFuseCol c i j A) S).card = (colorsOn c S).card
      - (if JInside c j A S ∧ j ∈ colorsOn c S ∧ i ∈ colorsOn c S then 1 else 0)
      + (if i ∉ colorsOn c S ∧ j ∈ colorsOn c (S ∩ A) ∧ ¬ JInside c j A S then 1 else 0) := by
  classical
  by_cases hA : j ∈ colorsOn c (S ∩ A)
  · have hAtoC : j ∈ colorsOn c S := colorsOn_mono c (fun _ hx => (Finset.mem_inter.mp hx).1) hA
    by_cases hJ : JInside c j A S
    · by_cases hi : i ∈ colorsOn c S
      · rw [if_pos ⟨hJ, hAtoC, hi⟩, if_neg (fun h => h.2.2 hJ),
          colorsOn_localFuseCol_of_inside (S := S) hij hJ hAtoC,
          Finset.card_insert_of_mem (Finset.mem_erase.mpr ⟨hij, hi⟩),
          Finset.card_erase_of_mem hAtoC]
        omega
      · have hpos : 0 < (colorsOn c S).card := Finset.card_pos.mpr ⟨j, hAtoC⟩
        rw [if_neg (fun h => hi h.2.2), if_neg (fun h => h.2.2 hJ),
          colorsOn_localFuseCol_of_inside (S := S) hij hJ hAtoC,
          Finset.card_insert_of_notMem (by
            intro hx
            rw [Finset.mem_erase] at hx
            exact hi hx.2),
          Finset.card_erase_of_mem hAtoC]
        have hsub : (colorsOn c S).card - 1 + 1 = (colorsOn c S).card :=
          Nat.sub_add_cancel (by omega : 1 ≤ (colorsOn c S).card)
        rw [hsub]
        omega
    · by_cases hi : i ∈ colorsOn c S
      · rw [if_neg (fun h => hJ h.1), if_neg (fun h => h.1 hi),
          colorsOn_localFuseCol_of_escaped (S := S) hJ hi]
        omega
      · have hpos : 0 < (colorsOn c S).card := Finset.card_pos.mpr ⟨j, hAtoC⟩
        rw [if_neg (fun h => hi h.2.2), if_pos ⟨hi, hA, hJ⟩,
          colorsOn_localFuseCol_of_escaped_fresh (S := S) hJ hi hA]
        have hcard2 : (insert i (colorsOn c S)).card = (colorsOn c S).card + 1 :=
          Finset.card_insert_of_notMem hi
        rw [hcard2]
        omega
  · rw [if_neg (fun h => hA (mem_colorsOn_inter_of_JInside h.1 h.2.1)),
      if_neg (fun h => hA h.2.1),
      colorsOn_localFuseCol_of_absent (S := S) (j := j) hA]
    omega

/-- **THE BROKEN FOUR-SETS OF A LOCALISED FUSION.**  A four-set of an admissible colouring is broken
by `localFuseCol c i j A` exactly when it is tight, carries colour `i`, and carries a `j`-coloured
edge inside `A` *all* of whose `j`-edges are inside `A`.  This is
`Fusion.not_five_le_of_fuseCol` in the localised language; note that no six-colour four-set can be
broken. -/
theorem not_five_le_of_localFuseCol {n k : ℕ} {c : Col n k} (hc : Admissible c) {i j : Fin k}
    (hij : i ≠ j) {A : Finset (Verts n)} {S : Finset (Verts n)} (hS : S.card = 4) :
    ¬ 5 ≤ (colorsOn (localFuseCol c i j A) S).card ↔
      (colorsOn c S).card = 5 ∧ i ∈ colorsOn c S ∧ j ∈ colorsOn c (S ∩ A) ∧ JInside c j A S := by
  classical
  have h56 : (colorsOn c S).card = 5 ∨ (colorsOn c S).card = 6 :=
    card_colorsOn_four_five_or_six hc hS
  have hcard := card_colorsOn_localFuseCol' (c := c) (A := A) (S := S) hij
  constructor
  · intro hn
    rcases h56 with h5 | h6
    · rw [hcard, h5] at hn
      by_cases hmain : JInside c j A S ∧ j ∈ colorsOn c S ∧ i ∈ colorsOn c S
      · rw [if_pos hmain, if_neg (fun h => absurd hmain.2.2 h.1)] at hn
        exact ⟨h5, hmain.2.2, mem_colorsOn_inter_of_JInside hmain.1 hmain.2.1, hmain.1⟩
      · rw [if_neg hmain] at hn
        by_cases h2 : i ∉ colorsOn c S ∧ j ∈ colorsOn c (S ∩ A) ∧ ¬ JInside c j A S
        · rw [if_pos h2] at hn
          exact absurd (show (5 : ℕ) ≤ 5 - 0 + 1 by norm_num) hn
        · rw [if_neg h2] at hn
          exact absurd (show (5 : ℕ) ≤ 5 - 0 + 0 by norm_num) hn
    · rw [hcard, h6] at hn
      by_cases hmain : JInside c j A S ∧ j ∈ colorsOn c S ∧ i ∈ colorsOn c S
      · rw [if_pos hmain, if_neg (fun h => absurd hmain.2.2 h.1)] at hn
        exact absurd (show (5 : ℕ) ≤ 6 - 1 + 0 by norm_num) hn
      · rw [if_neg hmain] at hn
        by_cases h2 : i ∉ colorsOn c S ∧ j ∈ colorsOn c (S ∩ A) ∧ ¬ JInside c j A S
        · rw [if_pos h2] at hn
          exact absurd (show (5 : ℕ) ≤ 6 - 0 + 1 by norm_num) hn
        · rw [if_neg h2] at hn
          exact absurd (show (5 : ℕ) ≤ 6 - 0 + 0 by norm_num) hn
  · rintro ⟨h5, hi, hjA, hJ⟩
    have hAtoC : j ∈ colorsOn c S := colorsOn_mono c (fun _ hx => (Finset.mem_inter.mp hx).1) hjA
    rw [hcard, h5, if_pos ⟨hJ, hAtoC, hi⟩, if_neg (fun h => h.2.2 hJ)]
    omega

/-- **THE BROKEN FOUR-SETS AS A FINSET**, i.e. the localised fusion criterion in the census
language of rounds 60–86: a tight four-set meeting colour `i` which meets colour `j` inside the
region `A`. -/
def TightAt {n k : ℕ} (c : Col n k) (i j : Fin k) (A : Finset (Verts n)) :
    Finset (Finset (Verts n)) :=
  (fourSets n).filter fun S => (colorsOn c S).card = 5 ∧ i ∈ colorsOn c S ∧
    j ∈ colorsOn c (S ∩ A) ∧ JInside c j A S

@[simp] theorem mem_TightAt {n k : ℕ} {c : Col n k} {i j : Fin k} {A : Finset (Verts n)}
    {S : Finset (Verts n)} :
    S ∈ TightAt c i j A ↔ S.card = 4 ∧ (colorsOn c S).card = 5 ∧ i ∈ colorsOn c S ∧
      j ∈ colorsOn c (S ∩ A) ∧ JInside c j A S := by
  simp only [TightAt, Finset.mem_filter, mem_fourSets]

/-- **THE LOCALISED FUSION CRITERION.**  The localised fusion of `j` into `i` is admissible exactly
when no tight four-set of `c` carries colour `i` *and* a confined `j`-class inside the region `A`:
a decidable statement, one finite comparison per four-set, with no search. -/
theorem localFuseCol_admissible_iff {n k : ℕ} {c : Col n k} (hc : Admissible c) {i j : Fin k}
    (hij : i ≠ j) (A : Finset (Verts n)) :
    Admissible (localFuseCol c i j A) ↔ TightAt c i j A = ∅ := by
  classical
  constructor
  · intro hf
    refine Finset.eq_empty_iff_forall_notMem.mpr fun S hS => ?_
    rw [mem_TightAt] at hS
    exact absurd (hf S hS.1)
      ((not_five_le_of_localFuseCol hc hij hS.1).mpr ⟨hS.2.1, hS.2.2.1, hS.2.2.2.1, hS.2.2.2.2⟩)
  · intro h0 S hS
    by_contra hn
    rw [not_five_le_of_localFuseCol hc hij hS] at hn
    exact (Finset.eq_empty_iff_forall_notMem.mp h0 S
      (mem_TightAt.mpr ⟨hS, hn.1, hn.2.1, hn.2.2.1, hn.2.2.2⟩))

/-- The broken family is contained in the tight four-sets meeting colour `i`. -/
theorem TightAt_subset_Tight {n k : ℕ} (c : Col n k) (i j : Fin k) (A : Finset (Verts n)) :
    TightAt c i j A ⊆ Tight c i := by
  intro S hS
  rw [mem_TightAt] at hS
  exact mem_Tight.mpr ⟨hS.1, hS.2.1, hS.2.2.1⟩

/-- **MONOTONICITY IN THE REGION**: enlarging the region only breaks more four-sets. -/
theorem TightAt_mono {n k : ℕ} (c : Col n k) (i j : Fin k) {A B : Finset (Verts n)}
    (hAB : A ⊆ B) : TightAt c i j A ⊆ TightAt c i j B := by
  intro S hS
  rw [mem_TightAt] at hS ⊢
  have hmono : colorsOn c (S ∩ A) ⊆ colorsOn c (S ∩ B) :=
    colorsOn_mono c (fun x hx => Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hx).1,
      hAB (Finset.mem_inter.mp hx).2⟩)
  exact ⟨hS.1, hS.2.1, hS.2.2.1, hmono hS.2.2.2.1, JInside.mono hS.2.2.2.2 hAB⟩

/-- **AT `A = V` THE BROKEN FAMILY IS `Tight c i ∩ Tight c j`** — round 84's criterion, recovered
from the localised one. -/
theorem mem_TightAt_univ {n k : ℕ} (c : Col n k) (i j : Fin k) {S : Finset (Verts n)} :
    S ∈ TightAt c i j (Finset.univ : Finset (Verts n)) ↔ S ∈ Tight c i ∧ S ∈ Tight c j := by
  have h1 : S ∈ TightAt c i j (Finset.univ : Finset (Verts n)) ↔
      S.card = 4 ∧ (colorsOn c S).card = 5 ∧ i ∈ colorsOn c S ∧
        j ∈ colorsOn c (S ∩ (Finset.univ : Finset (Verts n))) ∧ JInside c j (Finset.univ) S :=
    mem_TightAt
  have h2 : S ∈ Tight c i ↔ S.card = 4 ∧ (colorsOn c S).card = 5 ∧ i ∈ colorsOn c S := mem_Tight
  have h3 : S ∈ Tight c j ↔ S.card = 4 ∧ (colorsOn c S).card = 5 ∧ j ∈ colorsOn c S := mem_Tight
  rw [h1, h2, h3]
  constructor
  · rintro ⟨hS, h5, hi, hj, _⟩
    have hsub : S ∩ (Finset.univ : Finset (Verts n)) ⊆ S := by
      intro x hx
      exact (Finset.mem_inter.mp hx).1
    have hj' : j ∈ colorsOn c S := colorsOn_mono c hsub hj
    exact ⟨⟨hS, h5, hi⟩, ⟨hS, h5, hj'⟩⟩
  · rintro ⟨⟨hS, h5, hi⟩, ⟨_, _, hj⟩⟩
    have hjA : j ∈ colorsOn c (S ∩ (Finset.univ : Finset (Verts n))) := by
      have hsub : S ⊆ S ∩ (Finset.univ : Finset (Verts n)) := by
        intro x hx
        exact Finset.mem_inter.mpr ⟨hx, Finset.mem_univ x⟩
      refine colorsOn_mono c hsub ?_
      obtain ⟨e, he, hce⟩ := Finset.mem_image.mp hj
      exact Finset.mem_image.mpr ⟨e, he, hce⟩
    exact ⟨hS, h5, hi, hjA, JInside.of_univ c j S⟩

/-- **A DISJOINT TIGHT CENSUS MAKES EVERY LOCALISED FUSION ADMISSIBLE** — a localised move can only
ever be *harder* to certify than the global one, so round 84's criterion implies it. -/
theorem localFuseCol_admissible_of_disjoint {n k : ℕ} {c : Col n k} (hc : Admissible c)
    {i j : Fin k} (hij : i ≠ j) {A : Finset (Verts n)}
    (hd : ∀ S, S ∈ Tight c i → S ∉ Tight c j) : Admissible (localFuseCol c i j A) := by
  refine (localFuseCol_admissible_iff hc hij A).mpr ?_
  refine Finset.eq_empty_iff_forall_notMem.mpr fun S hS => ?_
  have hAB : A ⊆ (Finset.univ : Finset (Verts n)) := Finset.subset_univ A
  have h2 := TightAt_mono c i j hAB hS
  rw [mem_TightAt] at h2
  have hsub : S ∩ (Finset.univ : Finset (Verts n)) ⊆ S := by
    intro x hx
    exact (Finset.mem_inter.mp hx).1
  have hj' : j ∈ colorsOn c S := colorsOn_mono c hsub h2.2.2.2.1
  exact hd S (mem_Tight.mpr ⟨h2.1, h2.2.1, h2.2.2.1⟩) (mem_Tight.mpr ⟨h2.1, h2.2.1, hj'⟩)

/-! ### §6  The verified colourings allow no localised fusion either -/

/-- **NO LOCALISED FUSION IMPROVES THE CERTIFIED 5-COLOURING OF `K_6`** — for every pair of colours
and every region of the vertex set.  A consequence of `Tables.EG_six`, i.e. a *theorem* about all
`2⁶` regions, not a finite check. -/
theorem no_localFusion_sixCol : ∀ (i j : Fin 5) (hij : i ≠ j) (A : Finset (Verts 6)),
    Admissible (localFuseCol sixCol i j A) → ¬ Confined sixCol j A :=
  fun i j hij A hf => not_Confined_of_localFuse_admissible (c := sixCol) admissible_sixCol EG_six
    (by norm_num) (by norm_num) hij hf

/-- ... nor the certified 8-colouring of `K_9`. -/
theorem no_localFusion_nineCol : ∀ (i j : Fin 8) (hij : i ≠ j) (A : Finset (Verts 9)),
    Admissible (localFuseCol nineCol i j A) → ¬ Confined nineCol j A :=
  fun i j hij A hf => not_Confined_of_localFuse_admissible (c := nineCol) admissible_nineCol
    EG_nine (by norm_num) (by norm_num) hij hf

/-- ... nor the certified 9-colouring of `K_10`. -/
theorem no_localFusion_tenCol : ∀ (i j : Fin 9) (hij : i ≠ j) (A : Finset (Verts 10)),
    Admissible (localFuseCol tenCol i j A) → ¬ Confined tenCol j A :=
  fun i j hij A hf => not_Confined_of_localFuse_admissible (c := tenCol) admissible_tenCol EG_ten
    (by norm_num) (by norm_num) hij hf

/-- ... nor the certified 10-colouring of `K_11`. -/
theorem no_localFusion_elevenCol : ∀ (i j : Fin 10) (hij : i ≠ j) (A : Finset (Verts 11)),
    Admissible (localFuseCol elevenCol i j A) → ¬ Confined elevenCol j A :=
  fun i j hij A hf => not_Confined_of_localFuse_admissible (c := elevenCol) admissible_elevenCol
    EG_eleven (by norm_num) (by norm_num) hij hf

/-- ... nor the `K₁₂` anchor witness with its eleven colours. -/
theorem no_localFusion_r66Col :
    ∀ (i j : Fin 11) (hij : i ≠ j) (A : Finset (Verts 12)),
      Admissible (localFuseCol (listCol 12 11 (by norm_num) r66Col) i j A) →
        ¬ Confined (listCol 12 11 (by norm_num) r66Col) j A :=
  fun i j hij A hf => not_Confined_of_localFuse_admissible
    (c := listCol 12 11 (by norm_num) r66Col) (by native_decide) EG_twelve (by norm_num)
    (by norm_num) hij hf

/-- **THE WHOLE CLASS AT ONCE.**  For every admissible colouring which already uses `EG n` colours,
no localised fusion of any pair of colours, in any region, saves a colour. -/
theorem no_localFusion_of_optimal {n k : ℕ} {c : Col n k} (hc : Admissible c) (hopt : EG n = k)
    (hk : 2 ≤ k) (hn : 2 ≤ n) : ∀ (i j : Fin k) (hij : i ≠ j) (A : Finset (Verts n))
      (hi : i ∈ colorsOn c (Finset.univ : Finset (Verts n))),
      Admissible (localFuseCol c i j A) →
        (colorsOn (localFuseCol c i j A) (Finset.univ : Finset (Verts n))).card = k :=
  fun i j hij A hi hf => localFuse_is_not_a_move_at_optimal hc hopt hk hn hij hf hi

end JSP140
