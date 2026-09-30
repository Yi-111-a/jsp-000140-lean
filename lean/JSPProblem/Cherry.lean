import JSPProblem.Paths

/-!
# JSP-000140 — the `5/6` lower bound: every two-edge path is paid for by a private edge

`Paths.lean` reduced the lower half of the catalog answer `f(n,4,5) = 5n/6 + o(n)` to **one**
concrete hypothesis about an admissible colouring `c` of `K_n`:

    `Paths c ≤ n * (n-1) / 6`,

i.e. the total number of two-edge paths (monochromatic "cherries") is at most one sixth of `n²`.
This file **proves that hypothesis**.  The ingredients are the structural content of the lower
bound of arXiv:2207.02920 (BCDP22).

* `cherry_four_ne` — **the constraint of the `K₄` through a two-edge path.**  If `a - v - b` is a
  two-edge path of colour `i` and `x` is a fourth vertex, then the *other four* edges of the `K₄`
  on `{v, a, b, x}`, namely `s(a,b), s(a,x), s(b,x), s(v,x)`, carry **four pairwise distinct
  colours, none of them `i`**: the `K₄` carries the colour `i` on the two path edges and must span
  five colours, so the four remaining edges must span four different colours, and none of them can
  carry the colour `i` (that would give three equally coloured edges in a `K₄`).

* `centre_eq_of_leaves` — **a pair of leaves has at most one centre**: two two-edge paths with the
  same two leaves are impossible, since then `s(a, v')` would carry the colour of the path in the
  `K₄` of the first path.

* `nb_eq_singleton_of_cherry` — **the edge joining the two leaves is an isolated single edge**:
  if `a - v - b` is a two-edge path of colour `i`, then with `j = c s(a,b)` we have `j ≠ i` and

      `nb c j a = {b}`   and   `nb c j b = {a}`,

  i.e. `s(a,b)` is the *only* edge of colour `j` at `a` and at `b`, hence an isolated single edge
  of a different colour class.

* `not_two_centres`, `leaf_not_centre` — no edge joins two centres of one colour.

* `three_mul_paths_le_edges` — **THE `5/6` COUNTING LEMMA**: `3 * Paths c ≤ |E(K_n)| = n(n-1)/2`,
  because every two-edge path brings three edges with it — its own two edges and the isolated
  single edge between its leaves — and these triples are pairwise disjoint
  (`cherryEdges_disjoint`).  Equivalently `Paths c ≤ n(n-1)/6`, exactly the hypothesis isolated by
  round 4, which `five_sixth` turns into `5(n-1) ≤ 6k`: the complete lower half of the catalog
  answer.
-/

set_option maxHeartbeats 800000

namespace JSP140

variable {n k : ℕ}

/-! ### The six edges of a `K₄` are pairwise distinct -/

/-- **The six edges of a `K₄` are pairwise distinct.** -/
theorem six_edges_ne {n : ℕ} {v a b x : Verts n} (h4 : FourDistinct v a b x) :
    s(v, a) ≠ s(v, b) ∧ s(v, a) ≠ s(a, b) ∧ s(v, a) ≠ s(a, x) ∧ s(v, a) ≠ s(b, x) ∧
      s(v, a) ≠ s(v, x) ∧ s(v, b) ≠ s(a, b) ∧ s(v, b) ≠ s(a, x) ∧ s(v, b) ≠ s(b, x) ∧
      s(v, b) ≠ s(v, x) ∧ s(a, b) ≠ s(a, x) ∧ s(a, b) ≠ s(b, x) ∧ s(a, b) ≠ s(v, x) ∧
      s(a, x) ≠ s(b, x) ∧ s(a, x) ≠ s(v, x) ∧ s(b, x) ≠ s(v, x) := by
  rcases h4 with ⟨hva, hvb, hvx, hab, hax, hbx⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals
    intro hh
    rcases sym2_inj hh with ⟨h1, h2⟩ | ⟨h1, h2⟩
  all_goals aesop

/-- A two-element finset is determined by any two distinct elements it contains. -/
theorem card_two_eq {α : Type*} [DecidableEq α] {N : Finset α} {a b : α} (h : N.card = 2)
    (ha : a ∈ N) (hb : b ∈ N) (hab : a ≠ b) : N = {a, b} := by
  have hsub : N ⊆ {a, b} := by
    intro x hx
    by_cases h1 : x = a
    · exact Finset.mem_insert.mpr (Or.inl h1)
    · by_cases h2 : x = b
      · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr h2))
      · have h3 := card_ge_three hab (fun hh => h1 hh.symm) (fun hh => h2 hh.symm) ⟨ha, hb, hx⟩
        rw [h] at h3
        omega
  refine Finset.Subset.antisymm hsub ?_
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl <;> assumption

/-- **The constraint of the `K₄` through a two-edge path.**  Let `a - v - b` be a two-edge path of
colour `i` in an admissible colouring of `K_n` (`n ≥ 4`) and let `x ∉ {v, a, b}`.  Then the other
four edges of the `K₄` on `{v, a, b, x}` carry **four pairwise distinct colours, none of them
`i`**: `c s(a,b), c s(a,x), c s(b,x), c s(v,x)` are pairwise different and none of them is `i`. -/
theorem cherry_four_ne {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n) (i : Fin k)
    {v a b x : Verts n} (h4 : FourDistinct v a b x) (hcva : c s(v, a) = i) (hcvb : c s(v, b) = i) :
    c s(a, b) ≠ i ∧ c s(a, x) ≠ i ∧ c s(b, x) ≠ i ∧ c s(v, x) ≠ i ∧
      c s(a, b) ≠ c s(a, x) ∧ c s(a, b) ≠ c s(b, x) ∧ c s(a, b) ≠ c s(v, x) ∧
      c s(a, x) ≠ c s(b, x) ∧ c s(a, x) ≠ c s(v, x) ∧ c s(b, x) ≠ c s(v, x) := by
  set S : Finset (Verts n) := fourSet v a b x with hSdef
  have hS : S.card = 4 := by rw [hSdef]; exact card_fourSet h4
  have h6 : (edgeFinset S).card = 6 := card_edgeFinset_four hS
  set T4 : Finset (Sym2 (Verts n)) := {s(a, b), s(a, x), s(b, x), s(v, x)} with hT4def
  rcases six_edges_ne h4 with ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15⟩
  -- the two edges of the path are the only edges of colour `i` in the `K₄`
  have hpa : s(v, a) ∈ classIn c i S :=
    classIn_fourSet_mem hc i h4 v a hcva (mem_fourSet_a h4) (mem_fourSet_b h4) h4.1
  have hpb : s(v, b) ∈ classIn c i S :=
    classIn_fourSet_mem hc i h4 v b hcvb (mem_fourSet_a h4) (mem_fourSet_d h4) h4.2.1
  have hrest (e : Sym2 (Verts n)) (h1 : e ≠ s(v, a)) (h2 : e ≠ s(v, b)) : e ∉ classIn c i S := by
    intro he
    exact three_of_classIn_fourSet hc i h4 e s(v, a) s(v, b) he hpa hpb ⟨h1, h2, n1⟩
  have hn_ab : s(a, b) ∉ classIn c i S := hrest s(a, b) (fun hh => n2 hh.symm) (fun hh => n6 hh.symm)
  have hn_ax : s(a, x) ∉ classIn c i S := hrest s(a, x) (fun hh => n3 hh.symm) (fun hh => n7 hh.symm)
  have hn_bx : s(b, x) ∉ classIn c i S := hrest s(b, x) (fun hh => n4 hh.symm) (fun hh => n8 hh.symm)
  have hn_vx : s(v, x) ∉ classIn c i S := hrest s(v, x) (fun hh => n5 hh.symm) (fun hh => n9 hh.symm)
  have hcard : (classIn c i S).card = 2 := by
    refine le_antisymm (classIn_card_le_two hc i S hS) ?_
    calc 2 = ({s(v, a), s(v, b)} : Finset (Sym2 (Verts n))).card := by
          rw [Finset.card_insert_of_notMem (by simp [n1])]
          simp
      _ ≤ (classIn c i S).card := Finset.card_le_card (by
          intro e he
          simp only [Finset.mem_insert, Finset.mem_singleton] at he
          rcases he with rfl | rfl
          · exact hpa
          · exact hpb)
  -- the four remaining edges lie in the complement of the colour class
  have memT (e : Sym2 (Verts n))
      (h : e = s(a, b) ∨ e = s(a, x) ∨ e = s(b, x) ∨ e = s(v, x)) :
      e ∈ edgeFinset S \ classIn c i S := by
    rcases h with rfl | rfl | rfl | rfl
    · exact Finset.mem_sdiff.mpr
        ⟨mem_edgeFinset_mk (a := a) (b := b) (mem_fourSet_b h4) (mem_fourSet_d h4) h4.2.2.2.1, hn_ab⟩
    · exact Finset.mem_sdiff.mpr
        ⟨mem_edgeFinset_mk (a := a) (b := x) (mem_fourSet_b h4) (mem_fourSet_e h4) h4.2.2.2.2.1, hn_ax⟩
    · exact Finset.mem_sdiff.mpr
        ⟨mem_edgeFinset_mk (a := b) (b := x) (mem_fourSet_d h4) (mem_fourSet_e h4) h4.2.2.2.2.2, hn_bx⟩
    · exact Finset.mem_sdiff.mpr
        ⟨mem_edgeFinset_mk (a := v) (b := x) (mem_fourSet_a h4) (mem_fourSet_e h4) h4.2.2.1, hn_vx⟩
  have hTcard : (edgeFinset S \ classIn c i S).card = 4 := by
    have hsplit := Finset.card_sdiff_add_card_eq_card (classIn_subset : classIn c i S ⊆ edgeFinset S)
    rw [h6, hcard] at hsplit
    omega
  -- admissibility forces at least four colours outside the class
  have hle : (colorsOn c S).card ≤ 1 + ((edgeFinset S \ classIn c i S).image c).card := by
    have himg' : colorsOn c S ⊆ insert i ((edgeFinset S \ classIn c i S).image c) := by
      intro y hy
      simp only [colorsOn, Finset.mem_image] at hy
      obtain ⟨e, he, hec⟩ := hy
      by_cases hci : e ∈ classIn c i S
      · rw [(mem_classIn.mp hci).2] at hec
        exact Finset.mem_insert.mpr (Or.inl hec.symm)
      · exact Finset.mem_insert_of_mem
          (Finset.mem_image.mpr ⟨e, Finset.mem_sdiff.mpr ⟨he, hci⟩, hec⟩)
    calc (colorsOn c S).card ≤ (insert i ((edgeFinset S \ classIn c i S).image c)).card :=
        Finset.card_le_card himg'
      _ ≤ ((edgeFinset S \ classIn c i S).image c).card + 1 := Finset.card_insert_le _ _
      _ = 1 + ((edgeFinset S \ classIn c i S).image c).card := Nat.add_comm _ _
  have hge : 4 ≤ ((edgeFinset S \ classIn c i S).image c).card := by
    have h := hc S hS
    omega
  -- the complement has exactly four edges, so the colour map is injective on it
  have hleT : ((edgeFinset S \ classIn c i S).image c).card ≤ 4 := by
    calc ((edgeFinset S \ classIn c i S).image c).card ≤ (edgeFinset S \ classIn c i S).card :=
      Finset.card_image_le
      _ = 4 := hTcard
  have himg : ((edgeFinset S \ classIn c i S).image c).card = 4 := le_antisymm hleT hge
  have hinj : Set.InjOn c (↑(edgeFinset S \ classIn c i S) : Set (Sym2 (Verts n))) :=
    Finset.injOn_of_card_image_eq (himg.trans hTcard.symm)
  have memT' (e : Sym2 (Verts n))
      (h : e = s(a, b) ∨ e = s(a, x) ∨ e = s(b, x) ∨ e = s(v, x)) :
      e ∈ (↑(edgeFinset S \ classIn c i S) : Set (Sym2 (Verts n))) := Finset.mem_coe.mpr (memT e h)
  -- hence the four remaining edges carry four pairwise distinct colours
  have d10 : c s(a, b) ≠ c s(a, x) :=
    fun hh => n10 (hinj (memT' _ (Or.inl rfl)) (memT' _ (Or.inr (Or.inl rfl))) hh)
  have d11 : c s(a, b) ≠ c s(b, x) :=
    fun hh => n11 (hinj (memT' _ (Or.inl rfl)) (memT' _ (Or.inr (Or.inr (Or.inl rfl)))) hh)
  have d12 : c s(a, b) ≠ c s(v, x) :=
    fun hh => n12 (hinj (memT' _ (Or.inl rfl)) (memT' _ (Or.inr (Or.inr (Or.inr rfl)))) hh)
  have d13 : c s(a, x) ≠ c s(b, x) :=
    fun hh => n13 (hinj (memT' _ (Or.inr (Or.inl rfl))) (memT' _ (Or.inr (Or.inr (Or.inl rfl)))) hh)
  have d14 : c s(a, x) ≠ c s(v, x) :=
    fun hh => n14 (hinj (memT' _ (Or.inr (Or.inl rfl))) (memT' _ (Or.inr (Or.inr (Or.inr rfl)))) hh)
  have d15 : c s(b, x) ≠ c s(v, x) :=
    fun hh => n15 (hinj (memT' _ (Or.inr (Or.inr (Or.inl rfl))))
      (memT' _ (Or.inr (Or.inr (Or.inr rfl)))) hh)
  exact ⟨fun hh => hn_ab (mem_classIn.mpr
      ⟨mem_edgeFinset_mk (a := a) (b := b) (mem_fourSet_b h4) (mem_fourSet_d h4) h4.2.2.2.1, hh⟩),
    fun hh => hn_ax (mem_classIn.mpr
      ⟨mem_edgeFinset_mk (a := a) (b := x) (mem_fourSet_b h4) (mem_fourSet_e h4) h4.2.2.2.2.1, hh⟩),
    fun hh => hn_bx (mem_classIn.mpr
      ⟨mem_edgeFinset_mk (a := b) (b := x) (mem_fourSet_d h4) (mem_fourSet_e h4) h4.2.2.2.2.2, hh⟩),
    fun hh => hn_vx (mem_classIn.mpr
      ⟨mem_edgeFinset_mk (a := v) (b := x) (mem_fourSet_a h4) (mem_fourSet_e h4) h4.2.2.1, hh⟩),
    d10, d11, d12, d13, d14, d15⟩

/-- **A `K₄` through a two-edge path spans exactly five colours**: the two path edges share a
colour, and the other four edges carry four further, pairwise different, colours. -/
theorem colorsOn_cherry_fourSet {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n) (i : Fin k)
    {v a b x : Verts n} (h4 : FourDistinct v a b x) (hcva : c s(v, a) = i) (hcvb : c s(v, b) = i) :
    (colorsOn c (fourSet v a b x)).card = 5 := by
  set S : Finset (Verts n) := fourSet v a b x with hSdef
  have hS : S.card = 4 := by rw [hSdef]; exact card_fourSet h4
  have h6 : (edgeFinset S).card = 6 := card_edgeFinset_four hS
  have n1 : s(v, a) ≠ s(v, b) := (six_edges_ne h4).1
  have hpa : s(v, a) ∈ classIn c i S :=
    classIn_fourSet_mem hc i h4 v a hcva (mem_fourSet_a h4) (mem_fourSet_b h4) h4.1
  have hpb : s(v, b) ∈ classIn c i S :=
    classIn_fourSet_mem hc i h4 v b hcvb (mem_fourSet_a h4) (mem_fourSet_d h4) h4.2.1
  have hcard : (classIn c i S).card = 2 := by
    refine le_antisymm (classIn_card_le_two hc i S hS) ?_
    calc 2 = ({s(v, a), s(v, b)} : Finset (Sym2 (Verts n))).card := by
          rw [Finset.card_insert_of_notMem (by simp [n1])]
          simp
      _ ≤ (classIn c i S).card := Finset.card_le_card (by
          intro e he
          simp only [Finset.mem_insert, Finset.mem_singleton] at he
          rcases he with rfl | rfl
          · exact hpa
          · exact hpb)
  have hTcard : (edgeFinset S \ classIn c i S).card = 4 := by
    have hsplit := Finset.card_sdiff_add_card_eq_card (classIn_subset : classIn c i S ⊆ edgeFinset S)
    rw [h6, hcard] at hsplit
    omega
  have hle : (colorsOn c S).card ≤ 5 := by
    have himg : colorsOn c S ⊆ insert i ((edgeFinset S \ classIn c i S).image c) := by
      intro y hy
      simp only [colorsOn, Finset.mem_image] at hy
      obtain ⟨e, he, hec⟩ := hy
      by_cases hci : e ∈ classIn c i S
      · rw [(mem_classIn.mp hci).2] at hec
        exact Finset.mem_insert.mpr (Or.inl hec.symm)
      · exact Finset.mem_insert_of_mem
          (Finset.mem_image.mpr ⟨e, Finset.mem_sdiff.mpr ⟨he, hci⟩, hec⟩)
    calc (colorsOn c S).card ≤ (insert i ((edgeFinset S \ classIn c i S).image c)).card :=
        Finset.card_le_card himg
      _ ≤ ((edgeFinset S \ classIn c i S).image c).card + 1 := Finset.card_insert_le _ _
      _ ≤ 1 + (edgeFinset S \ classIn c i S).card := by
        have hle' : ((edgeFinset S \ classIn c i S).image c).card
            ≤ (edgeFinset S \ classIn c i S).card := Finset.card_image_le
        omega
      _ = 5 := by rw [hTcard]
  have hge : 5 ≤ (colorsOn c S).card := hc S hS
  omega

/-! ### A cherry has a unique centre, and its leaves span an isolated edge -/

/-- **A pair of leaves determines the centre.**  Two two-edge paths cannot have the same two
leaves: if `a - v - b` and `a - v' - b` were both of colour `i` with `v ≠ v'`, then the `K₄` on
`{v, a, b, v'}` would carry the colour `i` on the three edges `s(v,a), s(v,b), s(a,v')`, which
`cherry_four_ne` forbids. -/
theorem centre_eq_of_leaves {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n) (i : Fin k)
    {v a b v' : Verts n} (hva : v ≠ a) (hvb : v ≠ b) (hab : a ≠ b)
    (hcva : c s(v, a) = i) (hcvb : c s(v, b) = i)
    (hva' : v' ≠ a) (hvb' : v' ≠ b) (hcva' : c s(v', a) = i) (_hcvb' : c s(v', b) = i) : v = v' := by
  by_contra hvv'
  have hax : a ≠ v' := fun hh => hva' hh.symm
  have hbx' : b ≠ v' := fun hh => hvb' hh.symm
  have h4 : FourDistinct v a b v' := ⟨hva, hvb, hvv', hab, hax, hbx'⟩
  obtain ⟨_, h2, _, _, _, _, _, _, _, _⟩ := cherry_four_ne hc hn i h4 hcva hcvb
  exact h2 (c_swap hcva')

/-- **The edge joining the two leaves of a two-edge path is an isolated single edge.**  If
`a - v - b` is a two-edge path of colour `i` in an admissible colouring of `K_n` (`n ≥ 4`) and
`j = c s(a,b)`, then `j ≠ i` and

    `nb c j a Finset.univ = {b}`   and   `nb c j b Finset.univ = {a}`,

i.e. the edge `s(a,b)` is the only edge of its (necessarily different) colour at `a` and at `b`. -/
theorem nb_eq_singleton_of_cherry {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n) (i : Fin k)
    {v a b : Verts n} (hva : v ≠ a) (hvb : v ≠ b) (hab : a ≠ b)
    (hcva : c s(v, a) = i) (hcvb : c s(v, b) = i) (j : Fin k) (hcab : c s(a, b) = j) :
    j ≠ i ∧ nb c j a Finset.univ = {b} ∧ nb c j b Finset.univ = {a} := by
  have hji : j ≠ i := by
    by_contra hji
    obtain ⟨z, hz⟩ := exists_vertex_outside hn (threeSet v a b)
      (by rw [card_threeSet hva hvb hab]; omega)
    have h4z : FourDistinct v a b z :=
      ⟨hva, hvb, fun hh => hz (hh ▸ Finset.mem_insert_self v _), hab,
        fun hh => hz (hh ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self a _)),
        fun hh => hz (hh ▸ Finset.mem_insert_of_mem
          (Finset.mem_insert_of_mem (Finset.mem_insert_self b _)))⟩
    obtain ⟨h1, _, _, _, _, _, _, _, _, _⟩ := cherry_four_ne hc hn i h4z hcva hcvb
    exact h1 (hcab.trans hji)
  -- the two leaves span an isolated edge
  have key {w : Verts n} (hwab : w ≠ b) (hw : w ∈ nb c j a Finset.univ) : False := by
    have hwa : w ≠ a := (mem_nb.mp hw).1
    have hcjwa : c s(a, w) = j := (mem_nb.mp hw).2.2
    have hcv' : w ≠ v := by
      intro hh
      have h1 : c s(a, w) = i := hh ▸ c_swap hcva
      exact hji (hcjwa.symm.trans h1)
    have h4w : FourDistinct a b w v :=
      ⟨hab, fun hh => hwa hh.symm, fun hh => hva hh.symm, fun hh => hwab hh.symm,
        fun hh => hvb hh.symm, hcv'⟩
    obtain ⟨_, _, _, _, _, _, _, _, h9, _⟩ := cherry_four_ne hc hn j h4w hcab hcjwa
    exact h9 ((c_swap hcvb).trans (c_swap hcva).symm)
  have h1 : nb c j a Finset.univ = {b} := by
    refine Finset.eq_singleton_iff_unique_mem.mpr ⟨?_, ?_⟩
    · exact mem_nb.mpr ⟨hab.symm, Finset.mem_univ b, hcab⟩
    · intro w hw
      by_contra hwb
      exact key hwb hw
  have key' {w : Verts n} (hwab : w ≠ a) (hw : w ∈ nb c j b Finset.univ) : False := by
    have hwb : w ≠ b := (mem_nb.mp hw).1
    have hcjwb : c s(b, w) = j := (mem_nb.mp hw).2.2
    have hcv' : w ≠ v := by
      intro hh
      have h1 : c s(b, w) = i := hh ▸ c_swap hcvb
      exact hji (hcjwb.symm.trans h1)
    have h4w : FourDistinct b a w v :=
      ⟨fun hh => hab hh.symm, fun hh => hwb hh.symm, fun hh => hvb hh.symm,
        fun hh => hwab hh.symm, fun hh => hva hh.symm, hcv'⟩
    obtain ⟨_, _, _, _, _, _, _, _, h9, _⟩ := cherry_four_ne hc hn j h4w (c_swap hcab) hcjwb
    exact h9 ((c_swap hcva).trans (c_swap hcvb).symm)
  have h2 : nb c j b Finset.univ = {a} := by
    refine Finset.eq_singleton_iff_unique_mem.mpr ⟨?_, ?_⟩
    · exact mem_nb.mpr ⟨hab, Finset.mem_univ a, c_swap hcab⟩
    · intro w hw
      by_contra hwa
      exact key' hwa hw
  exact ⟨hji, h1, h2⟩

/-- **No edge of `K_n` joins two centres of the same colour.**  If `a` and `b` both have two
colour-`i` neighbours and `c s(a,b) = i`, the `K₄` on the other two neighbours carries three edges
of colour `i` (or, if the two "other" neighbours coincide, a monochromatic triangle). -/
theorem not_two_centres {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n) (i : Fin k) {a b : Verts n}
    (hab : a ≠ b) (hca : (nb c i a Finset.univ).card = 2) (hcb : (nb c i b Finset.univ).card = 2)
    (hcol : c s(a, b) = i) : False := by
  have hba : b ∈ nb c i a Finset.univ := mem_nb.mpr ⟨hab.symm, Finset.mem_univ b, hcol⟩
  obtain ⟨x, hx⟩ := (nb c i a Finset.univ).erase b |>.card_pos.mp (by
    rw [Finset.card_erase_of_mem hba, hca]; omega)
  have hxa : x ∈ nb c i a Finset.univ := (Finset.mem_erase.mp hx).2
  have hxb : x ≠ b := (Finset.mem_erase.mp hx).1
  have hxa' : x ≠ a := (mem_nb.mp hxa).1
  have hab' : a ∈ nb c i b Finset.univ := mem_nb.mpr ⟨hab, Finset.mem_univ a, c_swap hcol⟩
  obtain ⟨y, hy⟩ := (nb c i b Finset.univ).erase a |>.card_pos.mp (by
    rw [Finset.card_erase_of_mem hab', hcb]; omega)
  have hyb : y ∈ nb c i b Finset.univ := (Finset.mem_erase.mp hy).2
  have hya : y ≠ a := (Finset.mem_erase.mp hy).1
  have hyb' : y ≠ b := (mem_nb.mp hyb).1
  by_cases hxy : x = y
  · exact no_mono_triangle hc hn i hab (fun hh => hxa' hh.symm) (fun hh => hxb hh.symm)
      ⟨hcol, (mem_nb.mp hxa).2.2, hxy ▸ (mem_nb.mp hyb).2.2⟩
  · have h4 : FourDistinct a b x y :=
      ⟨hab, fun hh => hxa' hh.symm, fun hh => hya hh.symm, fun hh => hxb hh.symm,
        fun hh => hyb' hh.symm, hxy⟩
    have h1 : s(a, b) ≠ s(a, x) := by
      intro hh
      rcases sym2_inj hh with ⟨h1, h2⟩ | ⟨h1, h2⟩
      all_goals aesop
    have h2 : s(a, b) ≠ s(b, y) := by
      intro hh
      rcases sym2_inj hh with ⟨h1, h2⟩ | ⟨h1, h2⟩
      all_goals aesop
    have h3 : s(a, x) ≠ s(b, y) := by
      intro hh
      rcases sym2_inj hh with ⟨h1, h2⟩ | ⟨h1, h2⟩
      all_goals aesop
    exact three_of_classIn_fourSet hc i h4 s(a, b) s(a, x) s(b, y)
      (classIn_fourSet_mem hc i h4 a b hcol (mem_fourSet_a h4) (mem_fourSet_b h4) hab)
      (classIn_fourSet_mem hc i h4 a x (mem_nb.mp hxa).2.2 (mem_fourSet_a h4) (mem_fourSet_d h4)
        (fun hh => hxa' hh.symm))
      (classIn_fourSet_mem hc i h4 b y (mem_nb.mp hyb).2.2 (mem_fourSet_b h4) (mem_fourSet_e h4)
        (fun hh => hyb' hh.symm))
      ⟨h1, h2, h3⟩

/-- **The leaves of a two-edge path are never centres of its colour.** -/
theorem leaf_not_centre {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n) (i : Fin k) {v a : Verts n}
    (hva : v ≠ a) (hav : a ∈ nb c i v Finset.univ) (hcv : (nb c i v Finset.univ).card = 2)
    (hca : (nb c i a Finset.univ).card = 2) : False :=
  not_two_centres hc hn i hva hcv hca (mem_nb.mp hav).2.2

/-! ### Each two-edge path brings three private edges -/

/-- **Two two-edge paths with the same two leaves coincide.**  If `a - v - b` is a two-edge path of
colour `i` and `a - v' - b` is a two-edge path of *any* colour, then `v = v'` (and the two paths
have the same colour): otherwise the `K₄` on `{v, a, b, v'}` seen from the second path carries the
same colour on the two distinct edges `s(a,v)` and `s(b,v)`. -/
theorem centre_eq_of_leaves' {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n) (i : Fin k)
    {v a b v' : Verts n} (hva : v ≠ a) (hvb : v ≠ b) (hab : a ≠ b)
    (hcva : c s(v, a) = i) (hcvb : c s(v, b) = i) (hva' : v' ≠ a) (hvb' : v' ≠ b)
    (hcva' : ∃ (i' : Fin k), c s(v', a) = i' ∧ c s(v', b) = i') : v = v' := by
  obtain ⟨i', hcva', hcvb'⟩ := hcva'
  by_contra hvv'
  have h4 : FourDistinct v' a b v := ⟨hva', hvb', fun hh => hvv' hh.symm, hab,
    fun hh => hva hh.symm, fun hh => hvb hh.symm⟩
  obtain ⟨_, _, _, _, _, _, _, h8, _, _⟩ := cherry_four_ne hc hn i' h4 hcva' hcvb'
  exact h8 ((c_swap hcva).trans (c_swap hcvb).symm)

/-- The image of the ordered pairs of *distinct* elements of a two-element finset under
`(x, y) ↦ s(x, y)` is the single edge `{x, y}`. -/
theorem image_pairs_two {N : Finset (Verts n)} {a b : Verts n} (hN : N.card = 2) (hNab : N = {a, b})
    (hab : a ≠ b) :
    ((N ×ˢ N).filter (fun p : Verts n × Verts n => p.1 ≠ p.2)).image (fun p => s(p.1, p.2))
      = {s(a, b)} := by
  ext e
  constructor
  · intro he
    obtain ⟨p, hp, he⟩ := Finset.mem_image.mp he
    obtain ⟨hp, hne⟩ := Finset.mem_filter.mp hp
    have h1 := Finset.mem_product.mp hp
    simp only [hNab, Finset.mem_insert, Finset.mem_singleton] at h1
    refine Finset.mem_singleton.mpr ?_
    rcases h1.1 with hp1 | hp1 <;> rcases h1.2 with hp2 | hp2
    · exact absurd (hp1.trans hp2.symm) hne
    · exact he.symm.trans (by rw [hp1, hp2])
    · exact he.symm.trans (by rw [hp1, hp2, Sym2.eq_swap])
    · exact absurd (hp1.trans hp2.symm) hne
  · intro he
    rw [Finset.mem_singleton.mp he]
    have haN : a ∈ N := hNab.symm ▸ Finset.mem_insert_self a _
    have hbN : b ∈ N := hNab.symm ▸ Finset.mem_insert_of_mem (Finset.mem_singleton.mpr rfl)
    exact Finset.mem_image.mpr ⟨(a, b), Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨haN, hbN⟩, hab⟩, rfl⟩

/-- The colour-`i` neighbours of a vertex `v` (the two-element set of leaves of a two-edge path,
when `v` is a centre of colour `i`). -/
def Nbrs (c : Col n k) (i : Fin k) (v : Verts n) : Finset (Verts n) :=
  nb c i v (Finset.univ : Finset (Verts n))

theorem mem_Nbrs {c : Col n k} {i : Fin k} {v a : Verts n} : a ∈ Nbrs c i v ↔ a ≠ v ∧ c s(v, a) = i := by
  rw [Nbrs, mem_nb]
  simp

theorem card_Nbrs {c : Col n k} (i : Fin k) (v : Verts n) : (Nbrs c i v).card = (nb c i v Finset.univ).card := rfl

/-- The **leaf edge** of the two-edge path centred at `v` in colour `i`: the edge joining the two
colour-`i` neighbours of `v`. -/
def leafEdge (c : Col n k) (i : Fin k) (v : Verts n) : Finset (Sym2 (Verts n)) :=
  Finset.image (fun p : Verts n × Verts n => s(p.1, p.2))
    (Finset.filter (fun p : Verts n × Verts n => p.1 ≠ p.2) ((Nbrs c i v) ×ˢ Nbrs c i v))

/-- **The three edges of a two-edge path**: the two edges of the path itself, and the edge joining
its two leaves.  For a centre `v` of colour `i` (i.e. `v ∈ twoA c i`) this is a three-element set
of edges of `K_n`, and different two-edge paths give *disjoint* such sets
(`cherryEdges_disjoint`), so `3 * Paths c ≤ |E(K_n)|`. -/
def cherryEdges (c : Col n k) (i : Fin k) (v : Verts n) : Finset (Sym2 (Verts n)) :=
  (Nbrs c i v).image (fun a => s(v, a)) ∪ leafEdge c i v

/-- The two kinds of edges of `cherryEdges`. -/
theorem mem_cherryEdges {c : Col n k} (i : Fin k) {v : Verts n} {e : Sym2 (Verts n)}
    (he : e ∈ cherryEdges c i v) :
    (∃ a ∈ Nbrs c i v, e = s(v, a)) ∨
      (∃ p ∈ (Nbrs c i v) ×ˢ Nbrs c i v, p.1 ≠ p.2 ∧ e = s(p.1, p.2)) := by
  rw [cherryEdges, leafEdge] at he
  rcases Finset.mem_union.mp he with he | he
  · obtain ⟨a, ha, he⟩ := Finset.mem_image.mp he
    exact Or.inl ⟨a, ha, he.symm⟩
  · obtain ⟨p, hp, he⟩ := Finset.mem_image.mp he
    obtain ⟨hp, hne⟩ := Finset.mem_filter.mp hp
    exact Or.inr ⟨p, hp, hne, he.symm⟩

/-- A vertex is a centre of colour `i` exactly when it has two colour-`i` neighbours. -/
theorem card_twoA {c : Col n k} (i : Fin k) {v : Verts n} (hv : v ∈ twoA c i) : (Nbrs c i v).card = 2 := by
  rw [twoA, Finset.mem_filter] at hv
  exact hv.2

/-- A vertex is never its own colour-`i` neighbour. -/
theorem not_mem_Nbrs_self {c : Col n k} (i : Fin k) (v : Verts n) : v ∉ Nbrs c i v :=
  fun h => (mem_Nbrs.mp h).1 rfl

/-- **A two-edge path brings three distinct edges of `K_n`.** -/
theorem card_cherryEdges {c : Col n k} (i : Fin k) {v : Verts n} (hv : v ∈ twoA c i) :
    (cherryEdges c i v).card = 3 := by
  obtain ⟨a, b, hab, hN⟩ := Finset.card_eq_two.mp (card_twoA i hv)
  have hNab : Nbrs c i v = {a, b} := hN
  have haN : a ∈ Nbrs c i v := hNab.symm ▸ Finset.mem_insert_self a _
  have hbN : b ∈ Nbrs c i v := hNab.symm ▸ Finset.mem_insert_of_mem (Finset.mem_singleton.mpr rfl)
  have hA : (Nbrs c i v).image (fun a => s(v, a)) = {s(v, a), s(v, b)} := by
    ext e
    constructor
    · intro he
      obtain ⟨x, hx, he⟩ := Finset.mem_image.mp he
      rw [hNab] at hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with hx | hx
      · exact Finset.mem_insert.mpr (Or.inl (hx ▸ he.symm))
      · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr (hx ▸ he.symm)))
    · intro he
      rcases Finset.mem_insert.mp he with he | he
      · rw [he]; exact Finset.mem_image.mpr ⟨a, haN, rfl⟩
      · rw [Finset.mem_singleton.mp he]; exact Finset.mem_image.mpr ⟨b, hbN, rfl⟩
  have hB : leafEdge c i v = {s(a, b)} := image_pairs_two (card_twoA i hv) hNab hab
  have hdisj : Disjoint ((Nbrs c i v).image (fun a => s(v, a))) (leafEdge c i v) := by
    rw [hA, hB]
    refine Finset.disjoint_left.mpr fun e he1 he2 => ?_
    have he2' : e = s(a, b) := Finset.mem_singleton.mp he2
    subst he2'
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at he1
    rcases he1 with he1 | he1
    · -- `s(v, a) = s(a, b)`: either `a = b` (excluded) or `v = b`, but `b` is a colour-`i`
      -- neighbour of `v`, so `v` is not
      rcases sym2_inj he1 with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact hab h2.symm
      · exact not_mem_Nbrs_self i v (h2 ▸ hbN)
    · -- `s(v, b) = s(a, b)`: either `a = v` (excluded) or `a = b`
      rcases sym2_inj he1 with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact not_mem_Nbrs_self i v (h1 ▸ haN)
      · exact hab h1
  have hne1 : s(v, a) ∉ ({s(v, b)} : Finset (Sym2 (Verts n))) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    refine fun hh => ?_
    rcases sym2_inj hh with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact hab h2
    · exact hab (h2.trans h1)
  rw [cherryEdges, (Finset.card_union_of_disjoint hdisj), hA, hB, Finset.card_insert_of_notMem hne1,
    Finset.card_singleton]
  simp

/-- The three edges of a two-edge path are edges of `K_n`. -/
theorem cherryEdges_subset_edgeFinset {c : Col n k} (i : Fin k) {v : Verts n} :
    cherryEdges c i v ⊆ edgeFinset (Finset.univ : Finset (Verts n)) := by
  intro e he
  rcases mem_cherryEdges i he with ⟨a, ha, h1⟩ | ⟨p, hp, hne, h2⟩
  · rw [h1]
    exact mem_edgeFinset_mk (Finset.mem_univ v) (Finset.mem_univ a) (mem_Nbrs.mp ha).1.symm
  · rw [h2]
    have h1 := Finset.mem_product.mp hp
    exact mem_edgeFinset_mk (Finset.mem_univ p.1) (Finset.mem_univ p.2) hne

/-- An edge of `K_n` is a **single edge** of its own colour class if it is the only edge of that
colour at each of its two endpoints. -/
def Single (c : Col n k) (e : Sym2 (Verts n)) : Prop :=
  ∃ a b, e = s(a, b) ∧ a ≠ b ∧ (Nbrs c (c e) a).card = 1 ∧ (Nbrs c (c e) b).card = 1

/-- **The edge joining the leaves of a two-edge path is a single edge** of its own (necessarily
different) colour class. -/
theorem Single_of_leaf {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n) (i : Fin k)
    (v a b : Verts n) (hv : v ∈ twoA c i) (hab : a ≠ b) (hav : a ∈ Nbrs c i v)
    (hbv : b ∈ Nbrs c i v) (j : Fin k) (hcab : c s(a, b) = j) : Single c s(a, b) := by
  obtain ⟨hji, h1, h2⟩ := nb_eq_singleton_of_cherry hc hn i
    (fun hh => (mem_Nbrs.mp hav).1 hh.symm) (fun hh => (mem_Nbrs.mp hbv).1 hh.symm) hab
    (mem_Nbrs.mp hav).2 (mem_Nbrs.mp hbv).2 j hcab
  have h3a : (nb c j a Finset.univ).card = 1 := by rw [h1]; simp
  have h3b : (nb c j b Finset.univ).card = 1 := by rw [h2]; simp
  refine ⟨a, b, rfl, hab, ?_, ?_⟩
  · simpa only [Nbrs, hcab] using h3a
  · simpa only [Nbrs, hcab] using h3b

/-- **A path edge is not a single edge**: at its centre there are two edges of the colour. -/
theorem not_Single_of_path_edge {c : Col n k} (i : Fin k) {v a : Verts n} (hv : v ∈ twoA c i)
    (hav : a ∈ Nbrs c i v) : ¬ Single c s(v, a) := by
  intro h
  obtain ⟨x, y, hxy, hne, hc1, hc2⟩ := h
  have hcol : c s(v, a) = i := (mem_Nbrs.mp hav).2
  rcases sym2_inj hxy with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [hcol, h1.symm] at hc1
    rw [card_twoA i hv] at hc1
    omega
  · rw [hcol, h1.symm] at hc2
    rw [card_twoA i hv] at hc2
    omega

/-- **The three edges of two different two-edge paths are disjoint.** -/
theorem cherryEdges_disjoint {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n)
    {i : Fin k} {v : Verts n} {i' : Fin k} {v' : Verts n} (hvi : v ∈ twoA c i)
    (hvi' : v' ∈ twoA c i') (hne : (i, v) ≠ (i', v')) :
    Disjoint (cherryEdges c i v) (cherryEdges c i' v') := by
  refine Finset.disjoint_left.mpr fun e he1 he2 => ?_
  rcases mem_cherryEdges i he1 with ⟨a, ha, h1⟩ | ⟨x, hx, hxy, h1⟩
  · obtain ⟨hva, hia⟩ : v ≠ a ∧ c s(v, a) = i := ⟨(mem_Nbrs.mp ha).1.symm, (mem_Nbrs.mp ha).2⟩
    rcases mem_cherryEdges i' he2 with ⟨a', ha', h2⟩ | ⟨x', hx', hxy', h2⟩
    · have hii : i = i' := hia.symm.trans (congrArg c (h1.symm.trans h2))
          |>.trans ((mem_Nbrs.mp ha').2)
      have hvv' : s(v, a) = s(v', a') := h1.symm.trans h2
      rcases sym2_inj hvv' with ⟨hA, hB⟩ | ⟨hA, hB⟩
      · exact hne (Prod.ext hii hA)
      · exact not_two_centres (a := v) (b := v') hc hn i
          (fun hh => (mem_Nbrs.mp ha).1 (hB.trans hh.symm)) (card_twoA i hvi)
          (hii.symm ▸ card_twoA i' hvi') ((mem_Nbrs.mp (hB ▸ ha)).2)
    · obtain ⟨hx1, hx2⟩ := Finset.mem_product.mp hx'
      have hee : s(x'.1, x'.2) = s(v, a) := h2.symm.trans h1
      exact (not_Single_of_path_edge i hvi ha)
        (hee ▸ Single_of_leaf hc hn i' v' x'.1 x'.2 hvi' hxy' hx1 hx2 (c s(x'.1, x'.2)) rfl)
  · obtain ⟨hx1, hx2⟩ := Finset.mem_product.mp hx
    have hx' : x.1 ≠ v := (mem_Nbrs.mp hx1).1
    have hy' : x.2 ≠ v := (mem_Nbrs.mp hx2).1
    have hxa : c s(v, x.1) = i := (mem_Nbrs.mp hx1).2
    have hxb : c s(v, x.2) = i := (mem_Nbrs.mp hx2).2
    rcases mem_cherryEdges i' he2 with ⟨a', ha', he2⟩ | ⟨x'', hx'', hxy'', he2⟩
    · have hee : s(x.1, x.2) = s(v', a') := h1.symm.trans he2
      exact (not_Single_of_path_edge i' hvi' ha')
        (hee ▸ Single_of_leaf hc hn i v x.1 x.2 hvi hxy hx1 hx2 (c s(x.1, x.2)) rfl)
    · obtain ⟨hy1, hy2⟩ := Finset.mem_product.mp hx''
      have hy1' : x''.1 ≠ v' := (mem_Nbrs.mp hy1).1
      have hy2' : x''.2 ≠ v' := (mem_Nbrs.mp hy2).1
      have hyj1 : c s(v', x''.1) = i' := (mem_Nbrs.mp hy1).2
      have hyj2 : c s(v', x''.2) = i' := (mem_Nbrs.mp hy2).2
      have hee : s(x.1, x.2) = s(x''.1, x''.2) := h1.symm.trans he2
      have hcent : v = v' := by
        rcases sym2_inj hee with ⟨hA, hB⟩ | ⟨hA, hB⟩
        · exact centre_eq_of_leaves' (a := x.1) (b := x.2) hc hn i (fun hh => hx' hh.symm) (fun hh => hy' hh.symm) hxy hxa hxb
            (fun hh => hy1' (hh.trans hA).symm) (fun hh => hy2' (hh.trans hB).symm)
            ⟨i', hA ▸ hyj1, hB ▸ hyj2⟩
        · exact centre_eq_of_leaves' (a := x.1) (b := x.2) hc hn i (fun hh => hx' hh.symm) (fun hh => hy' hh.symm) hxy hxa hxb
            (fun hh => hy2' (hh.trans hA).symm) (fun hh => hy1' (hh.trans hB).symm)
            ⟨i', hA ▸ hyj2, hB ▸ hyj1⟩
      have hxy'' : c s(v', x.1) = i' := by
        rcases sym2_inj hee with ⟨hA, _⟩ | ⟨hA, _⟩
        · exact hA ▸ hyj1
        · exact hA ▸ hyj2
      exact absurd hcent (fun h => hne (Prod.ext (hxa.symm.trans
        ((congrArg (fun t => c s(t, x.1)) h).trans hxy'')) h))

/-! ### The `5/6` counting lemma -/

/-- The **two-edge paths** of a colouring, as a finset of pairs of a colour and a centre vertex.
Its cardinality is `Paths c`. -/
def cherryFinset (c : Col n k) : Finset (Fin k × Verts n) :=
  Finset.univ.biUnion fun i => (twoA c i).image fun v => (i, v)

theorem twoA_of_mem_cherryFinset {c : Col n k} {p : Fin k × Verts n} (hp : p ∈ cherryFinset c) :
    p.2 ∈ twoA c p.1 := by
  rw [cherryFinset, Finset.mem_biUnion] at hp
  obtain ⟨i, _, hp⟩ := hp
  rw [Finset.mem_image] at hp
  have he : (i, hp.choose) = p := hp.choose_spec.2
  rw [← he]
  exact hp.choose_spec.1

theorem card_cherryFinset (c : Col n k) : (cherryFinset c).card = Paths c := by
  have hinj : ∀ i : Fin k, Function.Injective (fun v : Verts n => (i, v)) :=
    fun _ _ i h => congrArg Prod.snd h
  have hdisc : (↑(Finset.univ : Finset (Fin k)) : Set (Fin k)).PairwiseDisjoint
      (fun i => (twoA c i).image fun v => (i, v)) := by
    intro i _ j _ hij
    refine Finset.disjoint_left.mpr fun p hp1 hp2 => ?_
    have h1 := Finset.mem_image.mp hp1
    have h2 := Finset.mem_image.mp hp2
    exact hij (congrArg Prod.fst (h1.choose_spec.2.trans h2.choose_spec.2.symm))
  calc (cherryFinset c).card = ∑ i : Fin k, ((twoA c i).image fun v => (i, v)).card :=
        Finset.card_biUnion hdisc
    _ = ∑ i : Fin k, (twoA c i).card :=
        Finset.sum_congr rfl fun i _ => Finset.card_image_of_injective _ (hinj i)
    _ = Paths c := by rw [Paths]

/-- **THE `5/6` COUNTING LEMMA.**  For every admissible colouring `c` of `K_n` (`n ≥ 4`),
`3 * Paths c ≤ |E(K_n)| = n(n-1)/2`: every two-edge path brings three edges with it — its own two
edges and the isolated single edge between its leaves — and the triples belonging to different
two-edge paths are disjoint.  Equivalently `Paths c ≤ n(n-1)/6`, the hypothesis isolated by
`Paths.lean`, or: **at least two thirds of the edges of `K_n` lie in single-edge components of
their colour class**. -/
theorem three_mul_paths_le_edges {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n) :
    3 * Paths c ≤ (edgeFinset (Finset.univ : Finset (Verts n))).card := by
  have hcard : ∀ p ∈ cherryFinset c, (cherryEdges c p.1 p.2).card = 3 :=
    fun p hp => card_cherryEdges p.1 (twoA_of_mem_cherryFinset hp)
  have hsub : ∀ p ∈ cherryFinset c,
      cherryEdges c p.1 p.2 ⊆ edgeFinset (Finset.univ : Finset (Verts n)) :=
    fun p _ => cherryEdges_subset_edgeFinset p.1
  have hdisc : (↑(cherryFinset c) : Set (Fin k × Verts n)).PairwiseDisjoint
      (fun p => cherryEdges c p.1 p.2) := by
    intro p hp q hq hpq
    exact cherryEdges_disjoint hc hn (twoA_of_mem_cherryFinset (Finset.mem_coe.mp hp))
      (twoA_of_mem_cherryFinset (Finset.mem_coe.mp hq)) hpq
  have h1 : ((cherryFinset c).biUnion fun p => cherryEdges c p.1 p.2).card
      = ∑ p ∈ cherryFinset c, (cherryEdges c p.1 p.2).card := Finset.card_biUnion hdisc
  have h2 : (∑ p ∈ cherryFinset c, (cherryEdges c p.1 p.2).card) = 3 * (cherryFinset c).card := by
    calc (∑ p ∈ cherryFinset c, (cherryEdges c p.1 p.2).card) = ∑ p ∈ cherryFinset c, (3 : ℕ) := by
          refine Finset.sum_congr rfl fun p hp => hcard p (Finset.mem_coe.mpr hp)
      _ = (cherryFinset c).card • (3 : ℕ) := Finset.sum_const _
      _ = 3 * (cherryFinset c).card := by rw [nsmul_eq_mul]; exact Nat.mul_comm _ _
  have h3 : (cherryFinset c).biUnion (fun p => cherryEdges c p.1 p.2)
      ⊆ edgeFinset (Finset.univ : Finset (Verts n)) := by
    intro e he
    obtain ⟨p, hp, he'⟩ := Finset.mem_biUnion.mp he
    exact hsub p (Finset.mem_coe.mpr hp) he'
  have h4 : ((cherryFinset c).biUnion (fun p => cherryEdges c p.1 p.2)).card
      ≤ (edgeFinset (Finset.univ : Finset (Verts n))).card := Finset.card_le_card h3
  have h5 : 3 * (cherryFinset c).card = 3 * Paths c := by rw [card_cherryFinset]
  omega

/-- `6 * Paths c ≤ n * (n - 1)`, the form of `three_mul_paths_le_edges` used below. -/
theorem six_mul_paths_le {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n) :
    6 * Paths c ≤ n * (n - 1) := by
  have h1 := three_mul_paths_le_edges hc hn
  have h2 := card_edgeFinset_univ_two n
  have h3 : 6 * Paths c ≤ 2 * (edgeFinset (Finset.univ : Finset (Verts n))).card := by omega
  omega

/-- **At least two thirds of the edges are isolated single edges**: the number of two-edge paths is
at most `n(n-1)/6`.  This is the hypothesis of `Paths.five_sixth_of_paths`, now *proved*. -/
theorem paths_le {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n) : Paths c ≤ n * (n - 1) / 6 := by
  have h1 := six_mul_paths_le hc hn
  exact (Nat.le_div_iff_mul_le (by omega)).2 (by simpa [Nat.mul_comm] using h1)

/-- **THE LOWER BOUND `f(n,4,5) ≥ 5n/6 - 5/6`.**  Every admissible `k`-colouring of `K_n` uses at
least `5(n-1)/6` colours: `5 * (n-1) ≤ 6 * k`.  This is the lower half of the catalog answer
`f(n,4,5) = 5n/6 + o(n)`, with the sharp constant `5/6` and no `o(n)` loss. -/
theorem five_sixth_lower {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n) : 5 * (n - 1) ≤ 6 * k :=
  five_sixth_of_paths hc (by omega) (paths_le hc hn)

/-- **The lower bound for `f(n,4,5)`.** -/
theorem EG_ge_five_sixth (n : ℕ) (hn : 4 ≤ n) : 5 * (n - 1) ≤ 6 * EG n := by
  obtain ⟨c, hc⟩ := EG_admissible n
  exact five_sixth_lower hc hn

/-- The lower bound in real form. -/
theorem EG_ge_five_sixth_real (n : ℕ) (hn : 4 ≤ n) : (5 : ℝ) * ((n - 1 : ℕ) : ℝ) / 6 ≤ (EG n : ℝ) := by
  have h := EG_ge_five_sixth n hn
  have h' : (5 : ℝ) * ((n - 1 : ℕ) : ℝ) ≤ 6 * (EG n : ℝ) := by exact_mod_cast h
  linarith

/-- **THE LOWER HALF OF THE HEADLINE STATEMENT.**  For every `ε > 0` and all `n` with
`n ≥ ⌈5/(6ε)⌉`,

    5n/6 - ε n ≤ f(n, 4, 5),

i.e. `FiveSixthLower EG` — the lower half of the solved catalog answer
`f(n,4,5) = 5n/6 + o(n)` (BCDP22).  Before round 10 this was only known for `ε ≥ 1/8`, with the
constant `3/4` of Erdős–Gyárfás (1977). -/
theorem fiveSixthLower_eps (ε : ℝ) (hε : 0 < ε) : ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    5 * (n : ℝ) / 6 - ε * n ≤ (EG n : ℝ) := by
  refine ⟨max (Nat.ceil (5 / (6 * ε))) 4, fun n hn => ?_⟩
  have h0 : Nat.ceil (5 / (6 * ε)) ≤ n := le_trans (le_max_left _ _) hn
  have h1 := EG_ge_five_sixth_real n (le_trans (le_max_right _ _) hn)
  have h2 : (5 : ℝ) * ((n - 1 : ℕ) : ℝ) = 5 * (n : ℝ) - 5 := by
    rw [Nat.cast_sub (by omega : (1 : ℕ) ≤ n)]
    ring
  have h3 : (5 / (6 * ε)) ≤ (n : ℝ) := by
    have h' : (5 / (6 * ε) : ℝ) ≤ ⌈5 / (6 * ε)⌉₊ := Nat.le_ceil _
    exact h'.trans (by exact_mod_cast h0)
  have h4 : (0 : ℝ) ≤ n := by positivity
  have h5 : (0 : ℝ) < 6 * ε := by linarith
  have h6 : (5 : ℝ) ≤ (n : ℝ) * (6 * ε) := (div_le_iff₀ h5).mp h3
  linarith

end JSP140
