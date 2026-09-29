import JSPProblem.ColorClass

/-!
# JSP-000140: the counting argument — the classical bound `f(n,4,5) ≥ 3(n-1)/4`

This file contains the **classical** half of the theory, i.e. the counting argument of
Erdős–Gyárfás (1977) for `p = 4`, `q = 5`:

* `nb` — the colour-`i` neighbours of a vertex `v` (excluding `v` itself);
* `nb_card_le_two` — a vertex has at most two neighbours in a colour class;
* `nb_eq_singleton` — **the structural core**: if `v` has two colour-`i` neighbours `a, b`,
  then the *only* colour-`i` edge at `a` is `s(a, v)`.  Together with `classIn_avoid_in`
  this says that every colour class of an admissible colouring is a disjoint union of single
  edges and two-edge paths;
* `degree_sum` — the degree sum identity `∑_v deg(v) = 2 * |E_i|`;
* `two_mul_cardA_le_cardB` — the two vertices of a two-edge path are pairwise disjoint over
  all paths of a colour class, i.e. `2 * |A| ≤ |B|`;
* `three_mul_classIn_le` — **the counting lemma** `3 * |E_i| ≤ 2 * n`;
* `sum_card_classIn` — the colour classes partition the edges;
* `classical_lower_bound` — **the classical bound** `3 * (n-1) ≤ 4 * k`, i.e. every
  admissible `k`-colouring of `K_n` uses at least `3(n-1)/4` colours, so
  `f(n,4,5) ≥ 3(n-1)/4`; this is the bound which the paper of Banerjee–Bradshaw–Letzter–
  Pokrovskiy sharpens from `3/4` to `5/6`.
-/

namespace JSP140

variable {n k : ℕ}

/-! ### Neighbours of a vertex in a colour class -/

/-- The colour-`i` neighbours of `v` inside `S`, with `v` itself removed. -/
def nb (c : Col n k) (i : Fin k) (v : Verts n) (S : Finset (Verts n)) : Finset (Verts n) :=
  (nbrsIn c i v S).erase v

theorem mem_nb {c : Col n k} {i : Fin k} {v : Verts n} {S : Finset (Verts n)} {a : Verts n} :
    a ∈ nb c i v S ↔ a ≠ v ∧ a ∈ S ∧ c s(v, a) = i := by
  simp only [nb, mem_nbrsIn, Finset.mem_erase]

/-- Symmetry of an edge: `c s(x, y) = i` is the same as `c s(y, x) = i`. -/
theorem c_swap {c : Col n k} {i : Fin k} {x y : Verts n} (h : c s(x, y) = i) : c s(y, x) = i := by
  rw [← Sym2.eq_swap]; exact h

/-- The endpoints of an edge of `edgeFinset S` are two distinct elements of `S`. -/
theorem exists_offDiag_mem {n : ℕ} {S : Finset (Verts n)} {e : Sym2 (Verts n)}
    (he : e ∈ edgeFinset S) : ∃ p q : Verts n, p ∈ S ∧ q ∈ S ∧ p ≠ q ∧ e = s(p, q) := by
  obtain ⟨p, q, hpq⟩ : ∃ p q : Verts n, e = s(p, q) := Sym2.exists.mp ⟨e, rfl⟩
  refine ⟨p, q, ?_, ?_, ?_, hpq⟩
  · exact Finset.mem_sym2_iff.mp (mem_edgeFinset.mp he).1 p
      (by rw [hpq]; exact Sym2.mem_mk_left p q)
  · exact Finset.mem_sym2_iff.mp (mem_edgeFinset.mp he).1 q
      (by rw [hpq]; exact Sym2.mem_mk_right p q)
  · exact (mem_edgeFinset.mp he).2 p q hpq

/-! ### A small splitting tool for sums -/

/-- A sum over `s` split by two disjoint predicates. -/
private lemma sum_split_two {α : Type*} [DecidableEq α] (s : Finset α) (P Q : α → Prop)
    [DecidablePred P] [DecidablePred Q] (hPQ : ∀ x, ¬ (P x ∧ Q x)) (p q : ℕ) :
    ∑ x ∈ s, (if P x then p else if Q x then q else 0) = p * (s.filter P).card
      + q * (s.filter Q).card := by
  have hsplit : ∀ x ∈ s, (if P x then p else if Q x then q else 0)
      = (if P x then p else 0) + (if Q x then q else 0) := by
    intro x hx
    by_cases hP : P x
    · have hQ : ¬ Q x := fun hQ => hPQ x ⟨hP, hQ⟩
      simp [hP, hQ]
    · by_cases hQ : Q x <;> simp [hP, hQ]
  calc ∑ x ∈ s, (if P x then p else if Q x then q else 0)
      = ∑ x ∈ s, ((if P x then p else 0) + (if Q x then q else 0)) :=
        Finset.sum_congr rfl fun x hx => hsplit x hx
    _ = (∑ x ∈ s, (if P x then p else 0)) + ∑ x ∈ s, (if Q x then q else 0) :=
        Finset.sum_add_distrib
    _ = p * (s.filter P).card + q * (s.filter Q).card := by
      have hP : (∑ x ∈ s, (if P x then p else 0 : ℕ)) = p * (s.filter P).card := by
        calc (∑ x ∈ s, (if P x then p else 0 : ℕ)) = ∑ x ∈ s.filter P, p :=
              (Finset.sum_filter P fun _ => p).symm
          _ = (s.filter P).card • p := Finset.sum_const _
          _ = p * (s.filter P).card := by rw [nsmul_eq_mul]; exact Nat.mul_comm _ _
      have hQ : (∑ x ∈ s, (if Q x then q else 0 : ℕ)) = q * (s.filter Q).card := by
        calc (∑ x ∈ s, (if Q x then q else 0 : ℕ)) = ∑ x ∈ s.filter Q, q :=
              (Finset.sum_filter Q fun _ => q).symm
          _ = (s.filter Q).card • q := Finset.sum_const _
          _ = q * (s.filter Q).card := by rw [nsmul_eq_mul]; exact Nat.mul_comm _ _
      rw [hP, hQ]

/-! ### The degree sum -/

/-- A vertex has at most two colour-`i` neighbours (besides itself), for **any** vertex set:
three such neighbours together with `v` would be a `K₄` carrying three edges of colour `i`. -/
theorem nb_card_le_two {c : Col n k} (hc : Admissible c) (i : Fin k) (v : Verts n)
    (S : Finset (Verts n)) : (nb c i v S).card ≤ 2 := by
  by_contra h
  have h3 : 3 ≤ (nb c i v S).card := by omega
  obtain ⟨a, b, x, ha, hb, hx, hab, hax, hbx⟩ := exists_three_mem h3
  have hva : v ≠ a := fun hh => (mem_nb.mp ha).1 hh.symm
  have hvb : v ≠ b := fun hh => (mem_nb.mp hb).1 hh.symm
  have hvx : v ≠ x := fun hh => (mem_nb.mp hx).1 hh.symm
  have h4 : FourDistinct v a b x := ⟨hva, hvb, hvx, hab, hax, hbx⟩
  exact three_of_classIn_fourSet hc i h4 s(v, a) s(v, b) s(v, x)
    (classIn_fourSet_mem hc i h4 v a (mem_nb.mp ha).2.2 (mem_fourSet_a h4) (mem_fourSet_b h4) hva)
    (classIn_fourSet_mem hc i h4 v b (mem_nb.mp hb).2.2 (mem_fourSet_a h4) (mem_fourSet_d h4) hvb)
    (classIn_fourSet_mem hc i h4 v x (mem_nb.mp hx).2.2 (mem_fourSet_a h4) (mem_fourSet_e h4) hvx)
    ⟨fun hh => hab (sym2_inj_right hh), fun hh => hax (sym2_inj_right hh),
      fun hh => hbx (sym2_inj_right hh)⟩

/-- **The structural core.**  If `v` has two colour-`i` neighbours `a ≠ b` inside `S`, then the
only colour-`i` edge of `S` at `a` is `s(a, v)`: the two-edge path `a - v - b` is isolated. -/
theorem nb_mem_eq {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n) (i : Fin k)
    {v a b : Verts n} {S : Finset (Verts n)} (hv : v ∈ S) (ha : a ∈ nb c i v S)
    (hb : b ∈ nb c i v S) (hab : a ≠ b) (w : Verts n) (hw : w ∈ nb c i a S) : w = v := by
  have hva : v ≠ a := (mem_nb.mp ha).1.symm
  have hvb : v ≠ b := (mem_nb.mp hb).1.symm
  have hvcva : c s(v, a) = i := (mem_nb.mp ha).2.2
  have hcvb : c s(v, b) = i := (mem_nb.mp hb).2.2
  have haS : a ∈ S := (mem_nb.mp ha).2.1
  have hbS : b ∈ S := (mem_nb.mp hb).2.1
  have hwa : w ≠ a := (mem_nb.mp hw).1
  have hwS : w ∈ S := (mem_nb.mp hw).2.1
  have hwc : c s(a, w) = i := (mem_nb.mp hw).2.2
  by_cases hvw : w = v
  · exact hvw
  · -- `s(a, w)` is a colour-`i` edge of `S` different from the two path edges
    have hed : s(a, w) ∈ classIn c i S := mem_classIn.mpr
      ⟨mem_edgeFinset_mk (a := a) (b := w) haS hwS hwa.symm, hwc⟩
    have hne1 : s(a, w) ≠ s(v, a) := by
      intro hh
      rcases sym2_inj hh with ⟨h1, _⟩ | ⟨_, h2⟩
      · exact hva h1.symm
      · exact hvw h2
    have hne2 : s(a, w) ≠ s(v, b) := by
      intro hh
      rcases sym2_inj hh with ⟨h1, _⟩ | ⟨h1, _⟩
      · exact hva h1.symm
      · exact hab h1
    have hne : s(a, w) ∉ {s(v, a), s(v, b)} := fun hh =>
      (Finset.mem_insert.mp hh).elim hne1 (fun h => hne2 (Finset.mem_singleton.mp h))
    have himg : s(a, w) ∈ classIn c i (S \ {a, b}) :=
      classIn_avoid_in hc hn i haS hbS hab hva hvb hvcva hcvb (Finset.mem_sdiff.mpr ⟨hed, hne⟩)
    obtain ⟨p, q, hp, hq, _, heq⟩ := exists_offDiag_mem (mem_classIn.mp himg).1
    have hwb : w ≠ b := by
      intro hh
      rcases sym2_inj heq with h | h
      · exact (Finset.mem_sdiff.mp hq).2
          (Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr (h.2.symm.trans hh))))
      · exact (Finset.mem_sdiff.mp hp).2
          (Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr (h.2.symm.trans hh))))
    have h4 : FourDistinct v a b w :=
      ⟨hva, hvb, fun h => hvw h.symm, hab, fun h => hwa h.symm, fun h => hwb h.symm⟩
    exact (three_of_classIn_fourSet hc i h4 s(v, a) s(v, b) s(a, w)
      (classIn_fourSet_mem hc i h4 v a hvcva (mem_fourSet_a h4) (mem_fourSet_b h4) hva)
      (classIn_fourSet_mem hc i h4 v b hcvb (mem_fourSet_a h4) (mem_fourSet_d h4) hvb)
      (classIn_fourSet_mem hc i h4 a w hwc (mem_fourSet_b h4) (mem_fourSet_e h4)
        (fun h => hwa h.symm))
      ⟨fun hh => hab (sym2_inj_right hh),
        (fun hh => by
          have hmem : w ∈ s(v, a) := by
            have hmem' : w ∈ s(a, w) := Sym2.mem_iff.mpr (Or.inr rfl)
            rw [← hh] at hmem'
            exact hmem'
          rcases Sym2.mem_iff.mp hmem with h1 | h1
          · exact hvw h1
          · exact hwa h1),
        (fun hh => by
          have hmem : w ∈ s(v, b) := by
            have hmem' : w ∈ s(a, w) := Sym2.mem_iff.mpr (Or.inr rfl)
            rw [← hh] at hmem'
            exact hmem'
          rcases Sym2.mem_iff.mp hmem with h1 | h1
          · exact hvw h1
          · exact hwb h1)⟩).elim

/-- **The structural core, as a set equality.** -/
theorem nb_eq_singleton {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n) (i : Fin k)
    {v a b : Verts n} {S : Finset (Verts n)} (hv : v ∈ S) (ha : a ∈ nb c i v S)
    (hb : b ∈ nb c i v S) (hab : a ≠ b) : nb c i a S = {v} := by
  ext w
  constructor
  · intro hw
    exact Finset.mem_singleton.mpr (nb_mem_eq hc hn i hv ha hb hab w hw)
  · intro hw
    have hwv : w = v := Finset.mem_singleton.mp hw
    subst hwv
    exact mem_nb.mpr ⟨(mem_nb.mp ha).1.symm, hv, c_swap (mem_nb.mp ha).2.2⟩

/-- The vertices of `S` lying in the edge `s(x, y)` are exactly `{x, y}`. -/
theorem filter_mem_edge {n : ℕ} {S : Finset (Verts n)} {x y : Verts n} (hx : x ∈ S) (hy : y ∈ S) :
    S.filter (fun v : Verts n => v ∈ s(x, y)) = insert x (insert y ∅) := by
  ext w
  constructor
  · intro hw
    have hwy : w ∈ s(x, y) := (Finset.mem_filter.mp hw).2
    rcases Sym2.mem_iff.mp hwy with h | h
    · exact Finset.mem_insert.mpr
        (show w = x ∨ w ∈ (insert y ∅ : Finset (Verts n)) from Or.inl h)
    · exact Finset.mem_insert.mpr (show w = x ∨ w ∈ (insert y ∅ : Finset (Verts n)) from
        Or.inr (Finset.mem_insert.mpr
          (show w = y ∨ w ∈ (∅ : Finset (Verts n)) from Or.inl h)))
  · intro hw
    by_cases h1 : w = x
    · exact Finset.mem_filter.mpr ⟨h1 ▸ hx, Sym2.mem_iff.mpr (Or.inl h1)⟩
    by_cases h2 : w = y
    · exact Finset.mem_filter.mpr ⟨h2 ▸ hy, Sym2.mem_iff.mpr (Or.inr h2)⟩
    exact absurd hw (by simp [h1, h2])

/-- Counting over the vertices: the colour-`i` edges at `v` are in bijection with the colour-`i`
neighbours of `v`. -/
theorem card_nb_eq_filter {c : Col n k} {i : Fin k} (S : Finset (Verts n)) {v : Verts n}
    (hv : v ∈ S) : (nb c i v S).card = ((classIn c i S).filter (fun e => v ∈ e)).card := by
  refine Finset.card_bij (fun a (_h : a ∈ nb c i v S) => s(v, a)) ?_ ?_ ?_
  · intro a ha
    have h1 := mem_nb.mp ha
    exact Finset.mem_filter.mpr ⟨mem_classIn.mpr
      ⟨mem_edgeFinset_mk (a := v) (b := a) hv h1.2.1 h1.1.symm, h1.2.2⟩,
      Sym2.mem_iff.mpr (Or.inl rfl)⟩
  · intro a₁ ha₁ a₂ ha₂ heq
    exact sym2_inj_right heq
  · intro e he
    obtain ⟨hep, hceq⟩ := mem_classIn.mp (Finset.mem_filter.mp he).1
    obtain ⟨x, y, hxS, hyS, hxy, hxe⟩ := exists_offDiag_mem hep
    subst hxe
    have hcv : v = x ∨ v = y := Sym2.mem_iff.mp (Finset.mem_filter.mp he).2
    rcases hcv with hcv | hcv
    · refine ⟨y, mem_nb.mpr ⟨?_, hyS, ?_⟩, ?_⟩
      · exact fun h : y = v => hxy (h.trans hcv).symm
      · rw [hcv]; exact hceq
      · rw [hcv]
    · refine ⟨x, mem_nb.mpr ⟨?_, hxS, ?_⟩, ?_⟩
      · exact fun h : x = v => hxy (h.trans hcv)
      · rw [hcv]; exact c_swap hceq
      · rw [hcv]; exact Sym2.eq_swap

/-- **The degree sum identity**: each colour-`i` edge is counted at both of its endpoints. -/
theorem degree_sum {c : Col n k} {i : Fin k} (S : Finset (Verts n)) :
    ∑ v ∈ S, (nb c i v S).card = 2 * (classIn c i S).card := by
  have h1 : ∑ v ∈ S, (nb c i v S).card
      = ∑ v ∈ S, ((classIn c i S).filter (fun e => v ∈ e)).card :=
    Finset.sum_congr rfl fun v hv => card_nb_eq_filter S hv
  have h2 : ∑ v ∈ S, ((classIn c i S).filter (fun e => v ∈ e)).card
      = ∑ v ∈ S, ∑ e ∈ classIn c i S, (if v ∈ e then 1 else 0 : ℕ) := by
    refine Finset.sum_congr rfl fun v _ => ?_
    show ((classIn c i S).filter (fun e => v ∈ e)).card = ∑ e ∈ classIn c i S, (if v ∈ e then 1 else 0)
    rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  have h3 : ∑ v ∈ S, ∑ e ∈ classIn c i S, (if v ∈ e then 1 else 0 : ℕ)
      = ∑ e ∈ classIn c i S, ∑ v ∈ S, (if v ∈ e then 1 else 0 : ℕ) := Finset.sum_comm
  have h4 : ∀ e ∈ classIn c i S, ∑ v ∈ S, (if v ∈ e then 1 else 0 : ℕ) = 2 := by
    intro e he
    obtain ⟨x, y, hxS, hyS, hxy, hxe⟩ := exists_offDiag_mem (mem_classIn.mp he).1
    subst hxe
    have hcard : ∑ v ∈ S, (if v ∈ s(x, y) then 1 else 0 : ℕ)
        = (S.filter (fun v : Verts n => v ∈ s(x, y))).card := by
      calc ∑ v ∈ S, (if v ∈ s(x, y) then 1 else 0 : ℕ)
          = ∑ v ∈ S.filter (fun v : Verts n => v ∈ s(x, y)), 1 :=
            (Finset.sum_filter (s := S) (fun v : Verts n => v ∈ s(x, y)) fun _ => (1 : ℕ)).symm
        _ = (S.filter (fun v : Verts n => v ∈ s(x, y))).card := (Finset.card_eq_sum_ones _).symm
    rw [hcard, filter_mem_edge hxS hyS]
    have h1 : y ∉ (∅ : Finset (Verts n)) := by simp
    have h2 : x ∉ (insert y ∅ : Finset (Verts n)) := by simp [h1, hxy]
    rw [Finset.card_insert_of_notMem h2, Finset.card_insert_of_notMem h1]
    simp
  have h7 : (∑ e ∈ classIn c i S, 2) = (classIn c i S).card * 2 := by
    simp [Finset.sum_const]
  calc ∑ v ∈ S, (nb c i v S).card = ∑ e ∈ classIn c i S, 2 := by
        rw [h1, h2, h3]
        exact Finset.sum_congr rfl fun e he => (h4 e he).symm ▸ rfl
    _ = 2 * (classIn c i S).card := h7.trans (Nat.mul_comm (classIn c i S).card 2)

/-! ### Splitting a finset by three predicates -/

/-- The card of a finset split by a predicate, written as a sum of indicator functions. -/
private lemma sum_ite_card {α : Type*} [DecidableEq α] (s : Finset α) (P : α → Prop)
    [DecidablePred P] : ∑ x ∈ s, (if P x then (1 : ℕ) else 0) = (s.filter P).card := by
  calc ∑ x ∈ s, (if P x then (1 : ℕ) else 0) = ∑ x ∈ s.filter P, 1 :=
        (Finset.sum_filter P fun _ => (1 : ℕ)).symm
    _ = (s.filter P).card := (Finset.card_eq_sum_ones _).symm

/-- If `P`, `Q`, `R` cover `s` and are pairwise disjoint, then `s.card` is the sum of the cards
of the three filters. -/
private lemma card_split_three {α : Type*} [DecidableEq α] (s : Finset α) (P Q R : α → Prop)
    [DecidablePred P] [DecidablePred Q] [DecidablePred R] (hcov : ∀ x ∈ s, P x ∨ Q x ∨ R x)
    (hdisj : ∀ x, (P x ∧ Q x) ∨ (P x ∧ R x) ∨ (Q x ∧ R x) → False) :
    s.card = (s.filter P).card + (s.filter Q).card + (s.filter R).card := by
  have hsplit : ∀ x ∈ s, (1 : ℕ)
      = (if P x then 1 else 0) + (if Q x then 1 else 0) + (if R x then 1 else 0) := by
    intro x hx
    have h := hcov x hx
    rcases h with h | h | h
    · have h1 : ¬ Q x := fun hQ => hdisj x (Or.inl ⟨h, hQ⟩)
      have h2 : ¬ R x := fun hR => hdisj x (Or.inr (Or.inl ⟨h, hR⟩))
      simp [h, h1, h2]
    · have h1 : ¬ P x := fun hP => hdisj x (Or.inl ⟨hP, h⟩)
      have h2 : ¬ R x := fun hR => hdisj x (Or.inr (Or.inr ⟨h, hR⟩))
      simp [h1, h, h2]
    · have h1 : ¬ P x := fun hP => hdisj x (Or.inr (Or.inl ⟨hP, h⟩))
      have h2 : ¬ Q x := fun hQ => hdisj x (Or.inr (Or.inr ⟨hQ, h⟩))
      simp [h1, h2, h]
  calc s.card = ∑ x ∈ s, (1 : ℕ) := Finset.card_eq_sum_ones s
    _ = ∑ x ∈ s, ((if P x then 1 else 0) + (if Q x then 1 else 0) + (if R x then 1 else 0)) :=
        Finset.sum_congr rfl fun x hx => hsplit x hx
    _ = ((∑ x ∈ s, (if P x then 1 else 0)) + ∑ x ∈ s, (if Q x then 1 else 0))
        + ∑ x ∈ s, (if R x then 1 else 0) := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    _ = (s.filter P).card + (s.filter Q).card + (s.filter R).card := by
        rw [sum_ite_card, sum_ite_card, sum_ite_card]

/-! ### The counting lemma `3 * |E_i| ≤ 2 * n` -/

/-- The vertices with two colour-`i` neighbours. -/
def twoA (c : Col n k) (i : Fin k) : Finset (Verts n) :=
  Finset.univ.filter fun v => (nb c i v Finset.univ).card = 2

/-- The vertices with exactly one colour-`i` neighbour. -/
def oneB (c : Col n k) (i : Fin k) : Finset (Verts n) :=
  Finset.univ.filter fun v => (nb c i v Finset.univ).card = 1

/-- **The pairs of the two-edge paths are disjoint.**  The colour-`i` neighbourhoods
`nb c i v` of the degree-two vertices are pairwise disjoint, so `2 * |A| ≤ |B|`: every two-edge
path `a - v - b` of a colour class uses two distinct degree-one vertices, and no vertex is used
by two different paths. -/
theorem two_mul_cardA_le_cardB {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n) (i : Fin k) :
    2 * (twoA c i).card ≤ (oneB c i).card := by
  have hdisc : (↑(twoA c i) : Set (Verts n)).PairwiseDisjoint (fun v => nb c i v Finset.univ) := by
    intro v hv w hw hvw
    refine Finset.disjoint_left.mpr fun x hx1 hx2 => ?_
    have hv' : (nb c i v Finset.univ).card = 2 := (Finset.mem_filter.mp hv).2
    obtain ⟨b, hb⟩ := (nb c i v Finset.univ).erase x |>.card_pos.mp (by
      rw [Finset.card_erase_of_mem hx1, hv']
      omega)
    have hb1 : b ∈ nb c i v Finset.univ := (Finset.mem_erase.mp hb).2
    have hb2 : b ≠ x := (Finset.mem_erase.mp hb).1
    have hsingle : nb c i x Finset.univ = {v} :=
      nb_eq_singleton hc hn i (Finset.mem_univ v) hx1 hb1 hb2.symm
    have hw : w ∈ nb c i x Finset.univ := mem_nb.mpr
      ⟨(mem_nb.mp hx2).1.symm, Finset.mem_univ w, c_swap (mem_nb.mp hx2).2.2⟩
    have hw' : w = v := by
      have hw2 : w ∈ ({v} : Finset (Verts n)) := by rw [← hsingle]; exact hw
      exact Finset.mem_singleton.mp hw2
    exact hvw hw'.symm
  have hsub : (twoA c i).biUnion (fun v => nb c i v Finset.univ) ⊆ oneB c i := by
    intro x hx
    obtain ⟨v, hv, hxv⟩ := Finset.mem_biUnion.mp hx
    have hv' : (nb c i v Finset.univ).card = 2 := (Finset.mem_filter.mp hv).2
    obtain ⟨b, hb⟩ := (nb c i v Finset.univ).erase x |>.card_pos.mp (by
      rw [Finset.card_erase_of_mem hxv, hv']
      omega)
    have hb1 : b ∈ nb c i v Finset.univ := (Finset.mem_erase.mp hb).2
    have hb2 : b ≠ x := (Finset.mem_erase.mp hb).1
    have hsingle : nb c i x Finset.univ = {v} :=
      nb_eq_singleton hc hn i (Finset.mem_univ v) hxv hb1 hb2.symm
    rw [oneB, Finset.mem_filter]
    refine ⟨Finset.mem_univ x, ?_⟩
    rw [hsingle]
    simp
  have hsum : (∑ v ∈ twoA c i, (nb c i v Finset.univ).card) = 2 * (twoA c i).card := by
    calc (∑ v ∈ twoA c i, (nb c i v Finset.univ).card) = ∑ v ∈ twoA c i, 2 := by
          refine Finset.sum_congr rfl fun v hv => ?_
          exact (Finset.mem_filter.mp hv).2
      _ = 2 * (twoA c i).card := by simp [Finset.sum_const, Nat.mul_comm]
  calc 2 * (twoA c i).card = ((twoA c i).biUnion (fun v => nb c i v Finset.univ)).card :=
      hsum.symm.trans
        (Finset.card_biUnion (s := twoA c i) (t := fun v => nb c i v Finset.univ) hdisc).symm
    _ ≤ (oneB c i).card := Finset.card_le_card hsub

/-- **The counting lemma.**  In an admissible colouring of `K_n` (with `n ≥ 4`) every colour
class has at most `2n/3` edges: a colour class is a disjoint union of single edges (two
vertices each) and two-edge paths (three vertices each), and `3 * 1 ≤ 2 * 2` resp.
`3 * 2 ≤ 2 * 3`. -/
theorem three_mul_classIn_le {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n) (i : Fin k) :
    3 * (classIn c i (Finset.univ : Finset (Verts n))).card ≤ 2 * n := by
  set U := (Finset.univ : Finset (Verts n)) with hU
  set E := classIn c i U with hE
  set A := twoA c i with hA
  set B := oneB c i with hB
  have hsplit : ∑ v ∈ U, (nb c i v U).card = 2 * A.card + B.card := by
    have key : ∀ v ∈ U, (nb c i v U).card
        = if (nb c i v U).card = 2 then 2 else if (nb c i v U).card = 1 then 1 else 0 := by
      intro v hv
      by_cases h2 : (nb c i v U).card = 2
      · rw [if_pos h2]; exact h2
      · rw [if_neg h2]
        by_cases h1 : (nb c i v U).card = 1
        · rw [if_pos h1]; exact h1
        · rw [if_neg h1]
          have hle := nb_card_le_two hc i v U
          omega
    calc ∑ v ∈ U, (nb c i v U).card = ∑ v ∈ U,
          (if (nb c i v U).card = 2 then 2 else if (nb c i v U).card = 1 then 1 else 0) :=
          Finset.sum_congr rfl fun v hv => key v hv
      _ = 2 * (U.filter (fun v => (nb c i v U).card = 2)).card
          + 1 * (U.filter (fun v => (nb c i v U).card = 1)).card :=
          sum_split_two U (fun v => (nb c i v U).card = 2) (fun v => (nb c i v U).card = 1)
            (fun x hx => by have := hx.1; have := hx.2; omega) 2 1
      _ = 2 * A.card + B.card := by
        rw [hA, hB, Nat.one_mul, hU]
        simp only [twoA, oneB]
  set C := U.filter (fun v => (nb c i v U).card = 0) with hC
  have hcov : ∀ v ∈ U, (nb c i v U).card = 2 ∨ (nb c i v U).card = 1
      ∨ (nb c i v U).card = 0 := by
    intro v _
    have hle := nb_card_le_two hc i v U
    by_cases h2 : (nb c i v U).card = 2
    · exact Or.inl h2
    by_cases h1 : (nb c i v U).card = 1
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr (by omega))
  have hpart' := card_split_three U (fun v => (nb c i v U).card = 2)
    (fun v => (nb c i v U).card = 1) (fun v => (nb c i v U).card = 0) hcov (fun x hz => by
      rcases hz with ⟨p, q⟩ | ⟨p, q⟩ | ⟨p, q⟩
      · have hp := p; have hq := q; omega
      · have hp := p; have hq := q; omega
      · have hp := p; have hq := q; omega)
  have hpart : A.card + B.card + C.card = U.card := by
    rw [hpart', hC, hA, hB, hU]
    simp only [twoA, oneB]
  have hdeg := degree_sum (c := c) (i := i) (S := U)
  have hAB : 2 * A.card ≤ B.card := two_mul_cardA_le_cardB hc hn i
  have hcardU : U.card = n := Fintype.card_fin n
  rw [← hE] at hdeg
  omega

/-! ### The colour classes partition the edges -/

/-- The colour classes partition the edges of `S`. -/
theorem sum_card_classIn (c : Col n k) (S : Finset (Verts n)) :
    ∑ i : Fin k, (classIn c i S).card = (edgeFinset S).card := by
  have h1 : ∑ i : Fin k, (classIn c i S).card
      = ∑ i : Fin k, ∑ e ∈ edgeFinset S, (if c e = i then 1 else 0) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    calc (classIn c i S).card = ∑ x ∈ classIn c i S, (1 : ℕ) := Finset.card_eq_sum_ones _
      _ = ∑ e ∈ edgeFinset S, (if c e = i then 1 else 0) :=
          Finset.sum_filter (s := edgeFinset S) (fun e => c e = i) fun _ => (1 : ℕ)
  have h2 : ∑ i : Fin k, ∑ e ∈ edgeFinset S, (if c e = i then 1 else 0)
      = ∑ e ∈ edgeFinset S, ∑ i : Fin k, (if c e = i then 1 else 0) := Finset.sum_comm
  have h3 : ∀ e ∈ edgeFinset S, ∑ i : Fin k, (if c e = i then 1 else 0 : ℕ) = 1 := by
    intro e _
    calc ∑ i : Fin k, (if c e = i then 1 else 0) = ∑ i : Fin k, (if i = c e then 1 else 0) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          by_cases h : i = c e
          · rw [if_pos h, if_pos h.symm]
          · rw [if_neg h, if_neg (Ne.symm h)]
      _ = 1 := Fintype.sum_ite_eq' (c e) fun _ => 1
  calc ∑ i : Fin k, (classIn c i S).card = ∑ e ∈ edgeFinset S, 1 := by
        rw [h1, h2]
        exact Finset.sum_congr rfl fun e he => (h3 e he).symm ▸ rfl
    _ = (edgeFinset S).card := (Finset.card_eq_sum_ones _).symm

/-! ### The classical bound `f(n,4,5) ≥ 3(n-1)/4` -/

/-- `n * (n + 1) = n * (n - 1) + 2 * n`, the rearrangement used to remove the division by `2`
in the number of edges of `K_n`. -/
private lemma mul_succ_pred (m : ℕ) : m * (m + 1) = m * (m - 1) + 2 * m := by
  have h2 : m * (m - 1) = m * m - m := by
    have hsub := Nat.sub_mul (n := m) (m := 1) (k := m)
    rw [Nat.mul_comm m (m - 1)]
    omega
  have h3 : m * m + m = m * m - m + 2 * m := by
    rcases m with _ | m
    · simp
    · have hle : m + 1 ≤ (m + 1) * (m + 1) :=
        Nat.le_mul_of_pos_left (m + 1) (n := m + 1) (by omega)
      omega
  calc m * (m + 1) = m * m + m := Nat.mul_succ m m
    _ = m * (m - 1) + 2 * m := by rw [h2]; exact h3

/-- The number of edges of `K_n`, without division: `2 * |E(K_n)| = n * (n - 1)`. -/
theorem card_edgeFinset_univ_two (n : ℕ) :
    2 * (edgeFinset (Finset.univ : Finset (Verts n))).card = n * (n - 1) := by
  have h1 := card_edgeFinset (S := (Finset.univ : Finset (Verts n)))
  rw [Finset.card_univ, Fintype.card_fin, Nat.choose_two_right, Nat.mul_comm] at h1
  have h4 : n * (n + 1) / 2 = n * (n - 1) / 2 + n := by
    have key : n * (n + 1) = n * (n - 1) + 2 * n := mul_succ_pred n
    rw [key, Nat.add_mul_div_left _ _ (by omega)]
  have h1' : (edgeFinset (Finset.univ : Finset (Verts n))).card = n * (n + 1) / 2 - n := by
    have hn : (n + 1 - 1) * (n + 1) / 2 = n * (n + 1) / 2 := by
      rw [show n + 1 - 1 = n by omega, Nat.mul_comm n (n + 1)]
    rw [hn] at h1
    exact h1
  rw [h4, Nat.add_sub_cancel] at h1'
  have heven : 2 ∣ n * (n - 1) := by
    rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
    · refine ⟨k * (n - 1), ?_⟩
      rw [hk, Nat.add_mul]
      omega
    · refine ⟨n * k, ?_⟩
      have hkn : n - 1 = k + k := by omega
      rw [hkn, Nat.mul_add]
      omega
  have h2 := Nat.mul_div_cancel' heven
  rw [h1', h2]

/-- **The classical bound** (Erdős–Gyárfás 1977): every admissible `k`-colouring of `K_n`, for
`n ≥ 4`, uses at least `3(n-1)/4` colours. -/
theorem classical_lower_bound {n k : ℕ} {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n) :
    3 * (n - 1) ≤ 4 * k := by
  set U := (Finset.univ : Finset (Verts n)) with hU
  have hle : ∀ i : Fin k, 3 * (classIn c i U).card ≤ 2 * n := fun i => three_mul_classIn_le hc hn i
  have h1 : (∑ i : Fin k, 3 * (classIn c i U).card) ≤ ∑ i : Fin k, 2 * n :=
    Finset.sum_le_sum fun i _ => hle i
  have hL : (∑ i : Fin k, 3 * (classIn c i U).card) = 3 * (edgeFinset U).card := by
    calc (∑ i : Fin k, 3 * (classIn c i U).card) = 3 * ∑ i : Fin k, (classIn c i U).card := by
          rw [← Finset.mul_sum (Finset.univ : Finset (Fin k)) (fun i => (classIn c i U).card) 3]
      _ = 3 * (edgeFinset U).card := by rw [sum_card_classIn]
  have hR : (∑ i : Fin k, 2 * n) = 2 * (n * k) := by
    calc (∑ i : Fin k, 2 * n) = 2 * ∑ i : Fin k, n := by
          rw [← Finset.mul_sum (Finset.univ : Finset (Fin k)) (fun _ => (n : ℕ)) 2]
      _ = 2 * (Fintype.card (Fin k) * n) := by
        rw [Finset.sum_const, Finset.card_univ]
        simp [Nat.mul_comm]
      _ = 2 * (n * k) := by
        calc 2 * (Fintype.card (Fin k) * n) = 2 * (k * n) := by rw [Fintype.card_fin]
          _ = 2 * (n * k) := by rw [Nat.mul_comm k n]
  have h2 : 3 * (edgeFinset U).card ≤ 2 * (n * k) := by rw [← hL, ← hR]; exact h1
  have h3 := card_edgeFinset_univ_two n
  have h6 : 6 * (edgeFinset U).card ≤ 4 * (n * k) := by
    have h : 2 * (2 * (n * k)) = 4 * (n * k) := by omega
    omega
  have h7 : 3 * (n * (n - 1)) ≤ 4 * (n * k) := by
    rw [← h3, ← Nat.mul_assoc (3 : ℕ) 2]
    exact h6
  have h7' : 3 * n * (n - 1) ≤ 4 * n * k := by
    have h := h7
    rw [← Nat.mul_assoc, ← Nat.mul_assoc] at h
    exact h
  have hl : n * (3 * (n - 1)) = 3 * n * (n - 1) :=
    (Nat.mul_assoc n 3 (n - 1)).symm.trans (by rw [Nat.mul_comm n 3])
  have hr : n * (4 * k) = 4 * n * k := by
    calc n * (4 * k) = n * 4 * k := (Nat.mul_assoc n 4 k).symm
      _ = 4 * n * k := by rw [Nat.mul_comm n 4]
  exact Nat.le_of_mul_le_mul_left (by rw [hl, hr]; exact h7') (by omega)

/-- **The classical bound for `EG`**: `f(n,4,5) ≥ 3(n-1)/4` for `n ≥ 4`. -/
theorem EG_ge_classical (n : ℕ) (hn : 4 ≤ n) : 3 * (n - 1) ≤ 4 * EG n := by
  obtain ⟨c, hc⟩ := EG_admissible n
  exact classical_lower_bound hc hn

end JSP140
