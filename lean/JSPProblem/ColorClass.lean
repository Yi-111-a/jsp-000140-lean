import JSPProblem.Definitions

/-!
# JSP-000140: the structure of the colour classes

This file contains the *structural* half of the theory of admissible colourings of `K_n`
(colourings in which every `K₄` spans at least five colours):

* `classIn_card_le_two` (from `Definitions.lean`): no four vertices carry three edges of one
  colour;
* `nbrsIn_card_le_two`: a vertex has at most two neighbours in a given colour;
* `classIn_avoid`: if `v` has two colour-`i` neighbours `a, b` inside a vertex set not
  containing `v`, then no colour-`i` edge is incident to `a` or `b`;
* `three_mul_classIn_le`: **every colour class of an admissible colouring is a disjoint union
  of edges and two-edge paths**, hence `3 * |E_i| ≤ 2 * |V|`;
* `four_mul_k_ge`: the classical bound `3 * (n - 1) ≤ 4 * k`, i.e. every admissible
  `k`-colouring of `K_n` uses at least `3(n-1)/4` colours.
-/

namespace JSP140

variable {n k : ℕ}

/-- The neighbours of `v` in the colour class `i` inside `S`. -/
def nbrsIn (c : Col n k) (i : Fin k) (v : Verts n) (S : Finset (Verts n)) : Finset (Verts n) :=
  S.filter fun a => c s(v, a) = i

theorem mem_nbrsIn {c : Col n k} {i : Fin k} {v : Verts n} {S : Finset (Verts n)} {a : Verts n} :
    a ∈ nbrsIn c i v S ↔ a ∈ S ∧ c s(v, a) = i := Finset.mem_filter

theorem edgeFinset_mono {n : ℕ} {S T : Finset (Verts n)} (hST : S ⊆ T) :
    edgeFinset S ⊆ edgeFinset T := by
  intro e he
  obtain ⟨h1, h2⟩ := mem_edgeFinset.mp he
  exact mem_edgeFinset.mpr ⟨Finset.sym2_mono hST h1, h2⟩

theorem ne_of_mem_of_notMem {n : ℕ} {S : Finset (Verts n)} {a b : Verts n} (ha : a ∈ S) (hb : b ∉ S) :
    a ≠ b := fun h => hb (h ▸ ha)

theorem ne_of_notMem_of_mem {n : ℕ} {S : Finset (Verts n)} {a b : Verts n} (hb : b ∉ S) (ha : a ∈ S) :
    b ≠ a := fun h => hb (h ▸ ha)

/-- A three-element vertex set. -/
def threeSet {n : ℕ} (a b d : Verts n) : Finset (Verts n) := insert a (insert b (insert d ∅))

theorem card_threeSet {n : ℕ} {a b d : Verts n} (hab : a ≠ b) (had : a ≠ d) (hbd : b ≠ d) :
    (threeSet a b d).card = 3 := by
  rw [threeSet, Finset.card_insert_of_notMem (by simp [hab, had]),
    Finset.card_insert_of_notMem (by simp [hab, hbd]),
    Finset.card_insert_of_notMem (by simp [had])]
  simp

theorem threeSet_subset_fourSet {n : ℕ} (a b d e : Verts n) : threeSet a b d ⊆ fourSet a b d e := by
  intro x hx
  simp only [threeSet, fourSet] at hx ⊢
  rcases Finset.mem_insert.mp hx with rfl | hx
  · exact Finset.mem_insert_self x _
  · rcases Finset.mem_insert.mp hx with rfl | hx
    · exact Finset.mem_insert_of_mem (Finset.mem_insert_self x _)
    · rcases Finset.mem_insert.mp hx with rfl | hx
      · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_self x _))
      · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
          (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hx)))

/-- Two elements of a set of cardinality at least `2`. -/
private theorem exists_two_mem {α : Type*} [DecidableEq α] [LinearOrder α] {s : Finset α}
    (h : 2 ≤ s.card) : ∃ a b : α, a ∈ s ∧ b ∈ s ∧ a ≠ b := by
  obtain ⟨a, ha⟩ := s.card_pos.mp (by omega)
  obtain ⟨b, hb⟩ := (s.erase a).card_pos.mp (by rw [Finset.card_erase_of_mem ha]; omega)
  have hbmem : b ∈ s := (Finset.mem_erase.mp hb).2
  have hab' : b ≠ a := (Finset.mem_erase.mp hb).1
  exact ⟨a, b, ha, hbmem, hab'.symm⟩

/-- Three pairwise distinct elements of a set of cardinality at least `3`. -/
private theorem exists_three_mem {α : Type*} [DecidableEq α] [LinearOrder α] {s : Finset α}
    (h : 3 ≤ s.card) :
    ∃ a b c : α, a ∈ s ∧ b ∈ s ∧ c ∈ s ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c := by
  obtain ⟨a, b, ha, hb, hab⟩ := exists_two_mem (s := s) (h := by omega)
  have hbm : b ∈ s.erase a := Finset.mem_erase_of_ne_of_mem hab.symm hb
  have h1 : (s.erase a).card = s.card - 1 := Finset.card_erase_of_mem ha
  have h2 : ((s.erase a).erase b).card = (s.erase a).card - 1 := Finset.card_erase_of_mem hbm
  have hpos2 : 0 < s.card - 2 := by omega
  have hcard : ((s.erase a).erase b).card = s.card - 2 := by
    rw [Finset.card_erase_of_mem hbm, Finset.card_erase_of_mem ha, Nat.sub_sub]
  obtain ⟨c, hc⟩ := ((s.erase a).erase b).card_pos.mp (by rw [hcard]; exact hpos2)
  have hc1 : c ∈ s.erase a := (Finset.mem_erase.mp hc).2
  have hcb : c ≠ b := (Finset.mem_erase.mp hc).1
  have hcS : c ∈ s := (Finset.mem_erase.mp hc1).2
  have hca : c ≠ a := (Finset.mem_erase.mp hc1).1
  exact ⟨a, b, c, ha, hb, hcS, hab, hca.symm, hcb.symm⟩

theorem mem_fourSet_of {n : ℕ} {a b d e : Verts n} (h : FourDistinct a b d e) {x : Verts n}
    (hx : x = a ∨ x = b ∨ x = d ∨ x = e) : x ∈ fourSet a b d e := (mem_fourSet h).2 hx

theorem mem_fourSet_a {n : ℕ} {a b d e : Verts n} (h : FourDistinct a b d e) :
    a ∈ fourSet a b d e := by rw [mem_fourSet h]; exact Or.inl rfl

theorem mem_fourSet_b {n : ℕ} {a b d e : Verts n} (h : FourDistinct a b d e) :
    b ∈ fourSet a b d e := by rw [mem_fourSet h]; exact Or.inr (Or.inl rfl)

theorem mem_fourSet_d {n : ℕ} {a b d e : Verts n} (h : FourDistinct a b d e) :
    d ∈ fourSet a b d e := by rw [mem_fourSet h]; exact Or.inr (Or.inr (Or.inl rfl))

theorem mem_fourSet_e {n : ℕ} {a b d e : Verts n} (h : FourDistinct a b d e) :
    e ∈ fourSet a b d e := by rw [mem_fourSet h]; exact Or.inr (Or.inr (Or.inr rfl))

/-- Three pairwise distinct edges of one colour inside a four-element set: impossible for an
admissible colouring. -/
theorem three_of_classIn_fourSet {c : Col n k} (hc : Admissible c) (i : Fin k)
    {u v w x : Verts n} (h4 : FourDistinct u v w x) (e₁ e₂ e₃ : Sym2 (Verts n))
    (h1 : e₁ ∈ classIn c i (fourSet u v w x)) (h2 : e₂ ∈ classIn c i (fourSet u v w x))
    (h3 : e₃ ∈ classIn c i (fourSet u v w x)) (hd : e₁ ≠ e₂ ∧ e₁ ≠ e₃ ∧ e₂ ≠ e₃) : False := by
  have hge : 3 ≤ (classIn c i (fourSet u v w x)).card := card_ge_three hd.1 hd.2.1 hd.2.2 ⟨h1, h2, h3⟩
  have hle : (classIn c i (fourSet u v w x)).card ≤ 2 := classIn_card_le_two hc i _ (card_fourSet h4)
  omega

/-- An edge of colour `i` between two vertices of a `K₄` is a colour-`i` edge of that `K₄`. -/
theorem classIn_fourSet_mem {c : Col n k} (hc : Admissible c) (i : Fin k) {u v w x : Verts n}
    (h4 : FourDistinct u v w x) (p q : Verts n) (he : c s(p, q) = i)
    (hp : p ∈ fourSet u v w x) (hq : q ∈ fourSet u v w x) (hpq : p ≠ q) :
    s(p, q) ∈ classIn c i (fourSet u v w x) :=
  mem_classIn.mpr ⟨mem_edgeFinset_mk hp hq hpq, he⟩

/-- A vertex set with fewer than `n` vertices misses a vertex of `K_n`. -/
theorem exists_vertex_outside {n : ℕ} (hn : 4 ≤ n) (S : Finset (Verts n)) (hS : S.card < n) :
    ∃ x, x ∉ S := by
  set t := (Finset.univ : Finset (Verts n)) \ S with ht
  have hcard : t.card = (Finset.univ : Finset (Verts n)).card - S.card :=
    Finset.card_sdiff_of_subset (Finset.subset_univ S)
  obtain ⟨x, hx⟩ := t.card_pos.mp (by rw [ht, hcard]; simp; omega)
  exact ⟨x, fun hxS => (Finset.mem_sdiff.mp hx).2 hxS⟩

/-- A vertex has at most two neighbours in any one colour class. -/
theorem nbrsIn_card_le_two {c : Col n k} (hc : Admissible c) (i : Fin k) {v : Verts n}
    (S : Finset (Verts n)) (hv : v ∉ S) : (nbrsIn c i v S).card ≤ 2 := by
  by_contra h
  have h3 : 3 ≤ (nbrsIn c i v S).card := by omega
  obtain ⟨a, b, x, ha, hb, hx, hab, hax, hbx⟩ := exists_three_mem h3
  have h4 : FourDistinct v a b x :=
    ⟨ne_of_notMem_of_mem hv (mem_nbrsIn.mp ha).1, ne_of_notMem_of_mem hv (mem_nbrsIn.mp hb).1,
      ne_of_notMem_of_mem hv (mem_nbrsIn.mp hx).1, hab, hax, hbx⟩
  exact three_of_classIn_fourSet hc i h4 s(v, a) s(v, b) s(v, x)
    (classIn_fourSet_mem hc i h4 v a (mem_nbrsIn.mp ha).2 (mem_fourSet_a h4) (mem_fourSet_b h4)
      (ne_of_notMem_of_mem hv (mem_nbrsIn.mp ha).1))
    (classIn_fourSet_mem hc i h4 v b (mem_nbrsIn.mp hb).2 (mem_fourSet_a h4) (mem_fourSet_d h4)
      (ne_of_notMem_of_mem hv (mem_nbrsIn.mp hb).1))
    (classIn_fourSet_mem hc i h4 v x (mem_nbrsIn.mp hx).2 (mem_fourSet_a h4) (mem_fourSet_e h4)
      (ne_of_notMem_of_mem hv (mem_nbrsIn.mp hx).1))
    ⟨fun hh => hab (sym2_inj_right hh), fun hh => hax (sym2_inj_right hh),
      fun hh => hbx (sym2_inj_right hh)⟩

/-- If `v` has two colour-`i` neighbours `a, b` inside `S`, with `v ∉ S` and `a ≠ b`, then no
colour-`i` edge inside `S` is incident to `a` or `b`: the path `a - v - b` is an isolated
two-edge path of the colour class. -/
theorem classIn_avoid {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n) (i : Fin k) {v a b : Verts n}
    {S : Finset (Verts n)} (hv : v ∉ S) (ha : a ∈ S) (hb : b ∈ S) (hab : a ≠ b)
    (hva : c s(v, a) = i) (hvb : c s(v, b) = i) : classIn c i S ⊆ classIn c i (S \ {a, b}) := by
  intro e he
  obtain ⟨h1, hec⟩ := mem_classIn.mp he
  have hmem : ∀ z, z ∈ e → z ∈ S := Finset.mem_sym2_iff.mp (mem_edgeFinset.mp h1).1
  obtain ⟨p, q, hpq⟩ : ∃ p q : Verts n, e = s(p, q) := Sym2.exists.mp ⟨e, rfl⟩
  rw [hpq] at he h1 hmem hec ⊢
  have hoff : OffDiag s(p, q) := (mem_edgeFinset.mp h1).2
  have hva_ne : v ≠ a := fun hh => hv (hh ▸ ha)
  have hvb_ne : v ≠ b := fun hh => hv (hh ▸ hb)
  have hpS : p ∈ S := hmem p (by rw [Sym2.mem_iff]; exact Or.inl rfl)
  have hvp : v ≠ p := ne_of_notMem_of_mem hv hpS
  have hqS : q ∈ S := hmem q (by rw [Sym2.mem_iff]; exact Or.inr rfl)
  have hqv : q ≠ v := fun hh => hv (hh ▸ hqS)
  have h3d : v ≠ a ∧ v ≠ b ∧ a ≠ b := ⟨hva_ne, hvb_ne, hab⟩
  obtain ⟨z, hz⟩ := exists_vertex_outside hn (threeSet v a b)
    (by rw [card_threeSet h3d.1 h3d.2.1 h3d.2.2]; omega)
  have hzv : z ≠ v := ne_of_notMem_of_mem hz (Finset.mem_insert_self _ _)
  have hza : z ≠ a := ne_of_notMem_of_mem hz (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
  have hzb : z ≠ b := ne_of_notMem_of_mem hz
    (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)))
  have h4z : FourDistinct v a b z :=
    ⟨hva_ne, hvb_ne, fun hh => hzv hh.symm, hab, fun hh => hza hh.symm, fun hh => hzb hh.symm⟩
  -- a monochromatic triangle on `v, a, b` is impossible
  have hno_tri : ¬ c s(a, b) = i := by
    intro htri
    exact three_of_classIn_fourSet hc i h4z s(v, a) s(v, b) s(a, b)
      (classIn_fourSet_mem hc i h4z v a hva (mem_fourSet_a h4z) (mem_fourSet_b h4z) hva_ne)
      (classIn_fourSet_mem hc i h4z v b hvb (mem_fourSet_a h4z) (mem_fourSet_d h4z) hvb_ne)
      (classIn_fourSet_mem hc i h4z a b htri (mem_fourSet_b h4z) (mem_fourSet_d h4z) hab)
      ⟨fun hh => hab (sym2_inj_right hh),
        fun hh => (sym2_inj hh).elim (fun ⟨_, h2⟩ => hab h2) (fun ⟨h1, _⟩ => hvb_ne h1),
        fun hh => (sym2_inj hh).elim (fun ⟨h1, _⟩ => hva_ne h1) (fun ⟨_, h2⟩ => hab h2.symm)⟩
  have hpa : p ≠ a := by
    intro hh
    rw [hh] at hoff hec
    have hqa : q ≠ a := fun h2 => hoff a a (by rw [h2]) rfl
    by_cases hqb' : q = b
    · rw [hqb'] at hec
      exact hno_tri hec
    · have h4q : FourDistinct v a b q :=
        ⟨hva_ne, hvb_ne, fun hh => hqv hh.symm, hab, fun hh => hqa hh.symm, fun hh => hqb' hh.symm⟩
      exact three_of_classIn_fourSet hc i h4q s(v, a) s(v, b) s(a, q)
        (classIn_fourSet_mem hc i h4q v a hva (mem_fourSet_a h4q) (mem_fourSet_b h4q) hva_ne)
        (classIn_fourSet_mem hc i h4q v b hvb (mem_fourSet_a h4q) (mem_fourSet_d h4q) hvb_ne)
        (classIn_fourSet_mem hc i h4q a q hec (mem_fourSet_b h4q) (mem_fourSet_e h4q)
          (fun hh => hqa hh.symm))
        ⟨fun hh => hab (sym2_inj_right hh),
          fun hh => (sym2_inj hh).elim (fun ⟨h1, _⟩ => hva_ne h1) (fun ⟨h1, _⟩ => hqv h1.symm),
          fun hh => (sym2_inj hh).elim (fun ⟨h1, _⟩ => hva_ne h1) (fun ⟨h1, _⟩ => hqv h1.symm)⟩
  have hpb : p ≠ b := by
    intro hh
    rw [hh] at hoff hec
    have hqb : q ≠ b := fun h2 => hoff b b (by rw [h2]) rfl
    by_cases hqa' : q = a
    · rw [hqa'] at hec
      rw [Sym2.eq_swap] at hec
      exact hno_tri hec
    · have h4q : FourDistinct v a b q :=
        ⟨hva_ne, hvb_ne, fun hh => hqv hh.symm, hab, fun hh => hqa' hh.symm, fun hh => hqb hh.symm⟩
      exact three_of_classIn_fourSet hc i h4q s(v, a) s(v, b) s(b, q)
        (classIn_fourSet_mem hc i h4q v a hva (mem_fourSet_a h4q) (mem_fourSet_b h4q) hva_ne)
        (classIn_fourSet_mem hc i h4q v b hvb (mem_fourSet_a h4q) (mem_fourSet_d h4q) hvb_ne)
        (classIn_fourSet_mem hc i h4q b q hec (mem_fourSet_d h4q) (mem_fourSet_e h4q)
          (fun hh => hqb hh.symm))
        ⟨fun hh => hab (sym2_inj_right hh),
          fun hh => (sym2_inj hh).elim (fun ⟨h1, _⟩ => hvb_ne h1) (fun ⟨h1, _⟩ => hqv h1.symm),
          fun hh => (sym2_inj hh).elim (fun ⟨h1, _⟩ => hvb_ne h1) (fun ⟨h1, _⟩ => hqv h1.symm)⟩
  have hqa : q ≠ a := by
    intro h2
    rw [h2] at hec
    have h4 : FourDistinct v p a b := ⟨hvp, hva_ne, hvb_ne, hpa, hpb, hab⟩
    exact three_of_classIn_fourSet hc i h4 s(v, a) s(v, b) s(p, a)
      (classIn_fourSet_mem hc i h4 v a hva (mem_fourSet_a h4) (mem_fourSet_d h4) hva_ne)
      (classIn_fourSet_mem hc i h4 v b hvb (mem_fourSet_a h4) (mem_fourSet_e h4) hvb_ne)
      (classIn_fourSet_mem hc i h4 p a hec (mem_fourSet_b h4) (mem_fourSet_d h4) hpa)
      ⟨fun hh => hab (sym2_inj_right hh),
        fun hh => (sym2_inj hh).elim (fun ⟨h1, _⟩ => hvp h1) (fun ⟨h1, _⟩ => hva_ne h1),
        fun hh => (sym2_inj hh).elim (fun ⟨h1, _⟩ => hvp h1) (fun ⟨h1, _⟩ => hva_ne h1)⟩
  have hqb : q ≠ b := by
    intro h2
    rw [h2] at hec
    have h4 : FourDistinct v p a b := ⟨hvp, hva_ne, hvb_ne, hpa, hpb, hab⟩
    exact three_of_classIn_fourSet hc i h4 s(v, a) s(v, b) s(p, b)
      (classIn_fourSet_mem hc i h4 v a hva (mem_fourSet_a h4) (mem_fourSet_d h4) hva_ne)
      (classIn_fourSet_mem hc i h4 v b hvb (mem_fourSet_a h4) (mem_fourSet_e h4) hvb_ne)
      (classIn_fourSet_mem hc i h4 p b hec (mem_fourSet_b h4) (mem_fourSet_e h4) hpb)
      ⟨fun hh => hab (sym2_inj_right hh),
        fun hh => (sym2_inj hh).elim (fun ⟨h1, _⟩ => hvp h1) (fun ⟨h1, _⟩ => hvb_ne h1),
        fun hh => (sym2_inj hh).elim (fun ⟨h1, _⟩ => hvp h1) (fun ⟨h1, _⟩ => hvb_ne h1)⟩
  have hpS' : p ∈ S \ {a, b} := by
    refine Finset.mem_sdiff.mpr ⟨hpS, ?_⟩
    intro h
    rcases Finset.mem_insert.mp h with h' | h'
    · exact hpa h'
    · exact hpb (Finset.mem_singleton.mp h')
  have hqS' : q ∈ S \ {a, b} := by
    refine Finset.mem_sdiff.mpr ⟨hqS, ?_⟩
    intro h
    rcases Finset.mem_insert.mp h with h' | h'
    · exact hqa h'
    · exact hqb (Finset.mem_singleton.mp h')
  exact mem_classIn.mpr ⟨mem_edgeFinset_mk hpS' hqS' (fun hh => hoff p q rfl hh), hec⟩

end JSP140
