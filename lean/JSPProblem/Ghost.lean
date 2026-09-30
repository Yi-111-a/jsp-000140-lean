import JSPProblem.Construction

/-!
# JSP-000140 — a second construction: the "ghost vertex" colouring, `f(n,4,5) ≤ n - 1`

`Construction.lean` gives the round-robin (sum) colouring, i.e. `f(n,4,5) ≤ n` for odd `n` and
`f(n,4,5) ≤ n + 1` in general.  This file gives a second, genuinely different colouring, which
removes the `+ 1` for two thirds of the even `n`:

    c({a, b}) = a + b    for a, b < m,          (the sum colouring on the first m vertices)
    c({∞, a}) = 2a                            (the *ghost* vertex ∞ = m)

for `m` odd and `3 ∤ m`, on the vertex set `Fin (m+1)`.  The idea is that `K_m` is coloured
properly by the sum colouring (so a `K₄` of `Fin m` spans at least five colours), and a `K₄`
containing `∞` spans the six colours

    2x, 2y, 2z, x+y, x+z, y+z     (mod m).

Of these, the only possible coincidences are the three "cross" equalities
`2x = y+z`, `2y = x+z`, `2z = x+y` (each of `2x = x+y` would give `x = y`): if two of them hold,
say `2x = y+z` and `2y = x+z`, then `3x = 3y` in `ZMod m`, and `3` is a unit in `ZMod m` when
`3 ∤ m` (`three_mul_inj`), contradicting the distinctness of `x, y`.  So there is at most one
coincidence, hence at least five distinct colours.  Consequently

* `admissible_ghost` — **the ghost colouring of `K_{m+1}` with `m` colours is admissible** for every
  odd `m` with `3 ∤ m`;
* `EG_le_ghost` — `f(m+1, 4, 5) ≤ m = (m+1) - 1`, so **`f(n,4,5) ≤ n - 1` for every even `n` with
  `3 ∤ (n-1)`**, i.e. for `n ≡ 0, 2 (mod 6)`.

In `Main.lean` this yields `EG_le_sixth_residue` and the upper half of the headline statement at the
sharp value `ε = 1/6` for all `n ≢ 4 (mod 6)`, not only for odd `n`.
-/

set_option maxHeartbeats 800000

namespace JSP140

variable {m n k : ℕ}

/-! ### The ghost vertex -/

/-- A vertex of `Fin (m+1)` is the last one exactly when its value is `m`. -/
theorem val_eq_last {a : Verts (m + 1)} : a.val = m ↔ a = Fin.last m := by
  constructor
  · intro h
    exact Fin.ext h
  · intro h
    rw [h, Fin.val_last]

/-- The colour of the edge `{a, b}` of the ghost colouring, as a residue: `a + b` if both endpoints
are base vertices, and `2` times the base endpoint if one of them is the ghost vertex
`Fin.last m`. -/
def ghostEdge (m : ℕ) (a b : Verts (m + 1)) : ℕ :=
  if a = Fin.last m then 2 * b.val else if b = Fin.last m then 2 * a.val else a.val + b.val

theorem ghostEdge_comm (m : ℕ) (a b : Verts (m + 1)) : ghostEdge m a b = ghostEdge m b a := by
  by_cases h1 : a = Fin.last m
  · by_cases h2 : b = Fin.last m
    · rw [h1, h2]
    · simp [ghostEdge, h1, h2]
  · by_cases h2 : b = Fin.last m
    · simp [ghostEdge, h1, h2]
    · simp [ghostEdge, h1, h2, Nat.add_comm]

/-- The colour of an edge between two base vertices. -/
theorem ghostEdge_base {m : ℕ} {a b : Verts (m + 1)} (hal : a ≠ Fin.last m) (hbl : b ≠ Fin.last m) :
    ghostEdge m a b = a.val + b.val := by simp [ghostEdge, hal, hbl]

/-- The colour of an edge from the ghost vertex to a base vertex `x`. -/
theorem ghostEdge_last (m : ℕ) (x : Verts (m + 1)) : ghostEdge m (Fin.last m) x = 2 * x.val := by
  simp [ghostEdge]

def modFin (m : ℕ) (hm0 : 0 < m) (t : ℕ) : Fin m := ⟨t % m, Nat.mod_lt _ hm0⟩

/-- **The ghost colouring.**  The edge `{a, b}` of `K_{m+1}` receives the colour
`(ghostEdge m a b) mod m`: the sum colouring `a + b` on the base vertices `0, …, m-1`, and `2a` on
the edges from the ghost vertex `Fin.last m`.  It uses `m` colours. -/
def ghostCol (m : ℕ) (hm0 : 0 < m) : Col (m + 1) m :=
  Sym2.hrec (motive := fun _ => Fin m)
    (fun a b => modFin m hm0 (ghostEdge m a b))
    (fun a b => by
      have h : ghostEdge m a b = ghostEdge m b a := ghostEdge_comm m a b
      rw [h])

@[simp] theorem ghostCol_val_mk (m : ℕ) (hm0 : 0 < m) (a b : Verts (m + 1)) :
    (ghostCol m hm0 s(a, b)).val = ghostEdge m a b % m := rfl

/-- The ghost colouring does not depend on the order of the two endpoints of an edge. -/
theorem ghostCol_swap (m : ℕ) (hm0 : 0 < m) (x y : Verts (m + 1)) :
    ghostCol m hm0 s(x, y) = ghostCol m hm0 s(y, x) :=
  congrArg _ (Sym2.sound (Sym2.rel_iff.mpr (Or.inr ⟨rfl, rfl⟩)))

/-! ### The colour arithmetic in `ZMod m` -/

/-- Two edges of the ghost colouring have the same colour exactly when the corresponding
`ghostEdge` residues agree in `ZMod m`. -/
theorem ghostCol_eq_iff (m : ℕ) (hm0 : 0 < m) (a b c d : Verts (m + 1)) :
    ghostCol m hm0 s(a, b) = ghostCol m hm0 s(c, d) ↔
      (ghostEdge m a b : ZMod m) = (ghostEdge m c d : ZMod m) := by
  constructor
  · intro he
    have h' := congrArg (fun t : Fin m => (t.val : ZMod m)) he
    simpa only [ghostCol_val_mk, ZMod.natCast_mod] using h'
  · intro hz
    refine Fin.ext ?_
    have hz' : ((ghostEdge m a b : ℕ) : ZMod m) = ((ghostEdge m c d : ℕ) : ZMod m) := by
      simpa only [ZMod.natCast_mod] using hz
    exact (natCast_zmod_eq_iff hm0).mp hz'

/-- The colour equality of two edges follows from the corresponding congruence in `ZMod m`. -/
theorem ghostCol_eq_of_zmod {m : ℕ} (hm0 : 0 < m) {a b c d : Verts (m + 1)}
    (h : (ghostEdge m a b : ZMod m) = (ghostEdge m c d : ZMod m)) :
    ghostCol m hm0 s(a, b) = ghostCol m hm0 s(c, d) :=
  (ghostCol_eq_iff m hm0 a b c d).mpr h

/-- In `ZMod m`, the colour of an edge between two base vertices is the sum of their residues. -/
theorem ghostZ_base {m : ℕ} {a b : Verts (m + 1)} (hal : a ≠ Fin.last m) (hbl : b ≠ Fin.last m) :
    (ghostEdge m a b : ZMod m) = (a.val : ZMod m) + (b.val : ZMod m) := by
  rw [ghostEdge_base hal hbl, Nat.cast_add]

/-- In `ZMod m`, the colour of an edge from the ghost vertex to a base vertex `x` is `2x`. -/
theorem ghostZ_last (m : ℕ) (x : Verts (m + 1)) :
    (ghostEdge m (Fin.last m) x : ZMod m) = 2 * (x.val : ZMod m) := by
  rw [ghostEdge_last]
  norm_num

/-- Two *base* vertices of `Fin (m+1)` with the same residue in `ZMod m` are equal: their values
are `< m`, so the injectivity of the `ℕ`-to-`ZMod m` map applies. -/
theorem fin_zmod_base_inj {m : ℕ} (hm0 : 0 < m) {u w : Verts (m + 1)} (hul : u ≠ Fin.last m)
    (hwl : w ≠ Fin.last m) (hab : (u.val : ZMod m) = (w.val : ZMod m)) : u = w := by
  refine Fin.ext ?_
  have hu : u.val < m := by
    have h2 : u.val ≠ m := fun hh => hul ((val_eq_last (a := u)).mp hh)
    omega
  have hw : w.val < m := by
    have h2 : w.val ≠ m := fun hh => hwl ((val_eq_last (a := w)).mp hh)
    omega
  exact natCast_zmod_inj hm0 hu hw hab

/-! ### The two structural facts: properness, and "at most one collision" -/

/-- **Properness on the base vertices (common second endpoint).**  If `u ≠ w` are base vertices,
then the edges `s(u, v)` and `s(w, v)` get different colours.  This is the properness of the sum
colouring `a + b`, and it is the reason why the only possible coincidences among the six colours
of a `K₄` are the "opposite edge" and "ghost edge" ones. -/
theorem ghostCol_ne_last {m : ℕ} (hm0 : 0 < m) {u v w : Verts (m + 1)}
    (hlast : u ≠ Fin.last m ∧ v ≠ Fin.last m ∧ w ≠ Fin.last m) (huw : u ≠ w) :
    ghostCol m hm0 s(u, v) ≠ ghostCol m hm0 s(w, v) := by
  intro he
  have h := (ghostCol_eq_iff m hm0 u v w v).mp he
  have h' : (u.val : ZMod m) = (w.val : ZMod m) := by
    rw [ghostZ_base hlast.1 hlast.2.1, ghostZ_base hlast.2.2 hlast.2.1] at h
    exact add_right_cancel h
  exact huw (fin_zmod_base_inj hm0 hlast.1 hlast.2.2 h')

/-- **Properness on the base vertices (common first endpoint).** -/
theorem ghostCol_ne_first {m : ℕ} (hm0 : 0 < m) {u v w : Verts (m + 1)}
    (hlast : u ≠ Fin.last m ∧ v ≠ Fin.last m ∧ w ≠ Fin.last m) (hvw : v ≠ w) :
    ghostCol m hm0 s(u, v) ≠ ghostCol m hm0 s(u, w) := by
  intro he
  have h := (ghostCol_eq_iff m hm0 u v u w).mp he
  have h' : (v.val : ZMod m) = (w.val : ZMod m) := by
    rw [ghostZ_base hlast.1 hlast.2.1, ghostZ_base hlast.1 hlast.2.2] at h
    exact add_left_cancel h
  exact hvw (fin_zmod_base_inj hm0 hlast.2.1 hlast.2.2 h')

/-- **Properness of the ghost edges.**  If `m` is odd and `x ≠ y` are base vertices, then the two
ghost edges `s(∞, x)` and `s(∞, y)` get different colours, because `2x = 2y` forces `x = y`. -/
theorem ghostCol_last_ne {m : ℕ} (hm0 : 0 < m) (hm : m % 2 = 1) {x y : Verts (m + 1)}
    (hxl : x ≠ Fin.last m) (hyl : y ≠ Fin.last m) (hxy : x ≠ y) :
    ghostCol m hm0 s(Fin.last m, x) ≠ ghostCol m hm0 s(Fin.last m, y) := by
  intro he
  have h := (ghostCol_eq_iff m hm0 _ _ _ _).mp he
  have h' : 2 * (x.val : ZMod m) = 2 * (y.val : ZMod m) := by
    simpa only [ghostZ_last m, ghostZ_last m] using h
  exact hxy (fin_zmod_base_inj hm0 hxl hyl (two_mul_inj hm h'))

/-- **No prime `3`.**  If `3 ∤ m` then multiplication by `3` in `ZMod m` is injective: `3` is a unit.
This is the step that fails when `3 ∣ m` (and it is the reason why the construction needs
`3 ∤ m`). -/
theorem three_mul_inj (h3 : ¬ 3 ∣ m) {x y : ZMod m} (h : (3 : ZMod m) * x = (3 : ZMod m) * y) :
    x = y := by
  have hu : IsUnit (3 : ZMod m) := ZMod.isUnit_prime_of_not_dvd Nat.prime_three h3
  have h3i : (3 : ZMod m) * (3 : ZMod m)⁻¹ = 1 := ZMod.mul_inv_of_unit _ hu
  have h3i' : (3 : ZMod m)⁻¹ * (3 : ZMod m) = 1 := by rw [mul_comm]; exact h3i
  have h' := congrArg (fun t : ZMod m => (3 : ZMod m)⁻¹ * t) h
  rwa [← mul_assoc, h3i', one_mul, ← mul_assoc, h3i', one_mul] at h'

/-- **Two "opposite edge" collisions of the sum colouring force two equal vertices.**  In `ZMod m`
with `m` odd, `a + b = c + d` and `a + c = b + d` give `2a = 2d`, i.e. `a = d`.  (The two
congruences are added: `2a + b + c = b + c + 2d`.) -/
theorem collision_12 (hm : m % 2 = 1) {a b c d : ZMod m} {e1 : a + b = c + d} {e2 : a + c = b + d} :
    a = d := by
  have h : (2 : ZMod m) * a = (2 : ZMod m) * d := by
    calc (2 : ZMod m) * a = a + a := by ring
      _ = ((a + b) + (a + c)) - (b + c) := by ring
      _ = ((c + d) + (b + d)) - (b + c) := by rw [e1, e2]
      _ = d + d := by ring
      _ = (2 : ZMod m) * d := by rw [two_mul]
  exact two_mul_inj hm h

/-- As `collision_12`, for the pair of equalities `a + b = c + d` and `a + d = b + c`: these give
`a = c`. -/
theorem collision_13 (hm : m % 2 = 1) {a b c d : ZMod m} {e1 : a + b = c + d} {e3 : a + d = b + c} :
    a = c := by
  have h : (2 : ZMod m) * a = (2 : ZMod m) * c := by
    calc (2 : ZMod m) * a = a + a := by ring
      _ = ((a + b) + (a + d)) - (b + d) := by ring
      _ = ((c + d) + (b + c)) - (b + d) := by rw [e1, e3]
      _ = c + c := by ring
      _ = (2 : ZMod m) * c := by rw [two_mul]
  exact two_mul_inj hm h

/-- As `collision_12`, for the pair of equalities `a + c = b + d` and `a + d = b + c`: these give
`a = b`. -/
theorem collision_23 (hm : m % 2 = 1) {a b c d : ZMod m} {e2 : a + c = b + d} {e3 : a + d = b + c} :
    a = b := by
  have h : (2 : ZMod m) * a = (2 : ZMod m) * b := by
    calc (2 : ZMod m) * a = a + a := by ring
      _ = ((a + c) + (a + d)) - (c + d) := by ring
      _ = ((b + d) + (b + c)) - (c + d) := by rw [e2, e3]
      _ = b + b := by ring
      _ = (2 : ZMod m) * b := by rw [two_mul]
  exact two_mul_inj hm h

/-- **At most one "cross" collision.**  If `3 ∤ m`, then `2x = y + z` and `2y = x + z` cannot both
hold: adding gives `3x = 3y`, and `3` is a unit in `ZMod m`. -/
theorem cross_12 (h3 : ¬ 3 ∣ m) {x y z : ZMod m} {e1 : (2 : ZMod m) * x = y + z}
    {e2 : (2 : ZMod m) * y = x + z} : x = y := by
  have h : (3 : ZMod m) * x = (3 : ZMod m) * y := by
    calc (3 : ZMod m) * x = 2 * x + x := by ring
      _ = (y + z) + x := by rw [e1]
      _ = (x + z) + y := by ring
      _ = (2 * y) + y := by rw [e2]
      _ = (3 : ZMod m) * y := by ring
  exact three_mul_inj h3 h

/-- As `cross_12`, for the pair `2x = y + z` and `2z = x + y`: these give `x = z`. -/
theorem cross_13 (h3 : ¬ 3 ∣ m) {x y z : ZMod m} {e1 : (2 : ZMod m) * x = y + z}
    {e3 : (2 : ZMod m) * z = x + y} : x = z := by
  have h : (3 : ZMod m) * x = (3 : ZMod m) * z := by
    calc (3 : ZMod m) * x = 2 * x + x := by ring
      _ = (y + z) + x := by rw [e1]
      _ = (x + y) + z := by ring
      _ = 2 * z + z := by rw [e3]
      _ = (3 : ZMod m) * z := by ring
  exact three_mul_inj h3 h

/-- As `cross_12`, for the pair `2y = x + z` and `2z = x + y`: these give `y = z`. -/
theorem cross_23 (h3 : ¬ 3 ∣ m) {x y z : ZMod m} {e2 : (2 : ZMod m) * y = x + z}
    {e3 : (2 : ZMod m) * z = x + y} : y = z := by
  have h : (3 : ZMod m) * y = (3 : ZMod m) * z := by
    calc (3 : ZMod m) * y = 2 * y + y := by ring
      _ = (x + z) + y := by rw [e2]
      _ = (x + y) + z := by ring
      _ = 2 * z + z := by rw [e3]
      _ = (3 : ZMod m) * z := by ring
  exact three_mul_inj h3 h

/-! ### Small finset tools -/

/-- Membership in a three-element finset. -/
private lemma mem_three {α : Type*} [DecidableEq α] {A : Finset α} {p₁ p₂ p₃ w : α}
    (hA : A = {p₁, p₂, p₃}) (hw : w ∈ A) : w = p₁ ∨ w = p₂ ∨ w = p₃ := by
  rw [hA] at hw
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  exact hw

/-- Two finsets of card `≥ 3` whose intersection has at most one element have a union of card
`≥ 5`. -/
private lemma card_union_ge_five {α : Type*} [DecidableEq α] {A B : Finset α} (hA : 3 ≤ A.card)
    (hB : 3 ≤ B.card) (hI : (A ∩ B).card ≤ 1) : 5 ≤ (A ∪ B).card := by
  have h := Finset.card_union_add_card_inter A B
  omega

/-- If every element of `A ∩ B` is one of `p₁, p₂, p₃` and at most one of `p₁, p₂, p₃` lies in
`B`, then `|A ∩ B| ≤ 1`.  This is the counting step behind both `K₄` lemmas: among the three
"star" colours and the three "far" colours of a `K₄` at most one can coincide. -/
private lemma card_inter_le_one {α : Type*} [DecidableEq α] {A B : Finset α} {p₁ p₂ p₃ : α}
    (hmem : A ∩ B ⊆ {p₁, p₂, p₃}) (h1 : ¬ (p₁ ∈ B ∧ p₂ ∈ B)) (h2 : ¬ (p₁ ∈ B ∧ p₃ ∈ B))
    (h3 : ¬ (p₂ ∈ B ∧ p₃ ∈ B)) : (A ∩ B).card ≤ 1 := by
  have key : ∀ x : α, x ∈ A ∩ B → (x = p₁ ∧ x ∈ B) ∨ (x = p₂ ∧ x ∈ B) ∨ (x = p₃ ∧ x ∈ B) := by
    intro x hx
    have hxb : x ∈ B := (Finset.mem_inter.mp hx).2
    have hm := hmem hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with rfl | rfl | rfl
    · exact Or.inl ⟨rfl, hxb⟩
    · exact Or.inr (Or.inl ⟨rfl, hxb⟩)
    · exact Or.inr (Or.inr ⟨rfl, hxb⟩)
  by_cases hp1 : p₁ ∈ B
  · have e2 : p₂ ∉ B := fun hh => h1 ⟨hp1, hh⟩
    have e3 : p₃ ∉ B := fun hh => h2 ⟨hp1, hh⟩
    calc (A ∩ B).card ≤ ({p₁} : Finset α).card := Finset.card_le_card (by
          intro x hx
          rcases key x hx with ⟨rfl, hxb⟩ | ⟨rfl, hxb⟩ | ⟨rfl, hxb⟩
          · simp
          · exact absurd hxb e2
          · exact absurd hxb e3)
      _ = 1 := by simp
  by_cases hp2 : p₂ ∈ B
  · have e3 : p₃ ∉ B := fun hh => h3 ⟨hp2, hh⟩
    calc (A ∩ B).card ≤ ({p₂} : Finset α).card := Finset.card_le_card (by
          intro x hx
          rcases key x hx with ⟨rfl, hxb⟩ | ⟨rfl, hxb⟩ | ⟨rfl, hxb⟩
          · exact absurd hxb hp1
          · simp
          · exact absurd hxb e3)
      _ = 1 := by simp
  · calc (A ∩ B).card ≤ ({p₃} : Finset α).card := Finset.card_le_card (by
        intro x hx
        rcases key x hx with ⟨rfl, hxb⟩ | ⟨rfl, hxb⟩ | ⟨rfl, hxb⟩
        · exact absurd hxb hp1
        · exact absurd hxb hp2
        · simp)
      _ = 1 := by simp

/-! ### The shape of the two kinds of `K₄` -/

/-- The shape of a `K₄` of *base* vertices: four pairwise distinct vertices, none of them the ghost
vertex `Fin.last m`. -/
abbrev FourBase {m : ℕ} (a b c d : Verts (m + 1)) : Prop :=
  a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
    a ≠ Fin.last m ∧ b ≠ Fin.last m ∧ c ≠ Fin.last m ∧ d ≠ Fin.last m

/-- **The colours of the three "far" edges of a `K₄` of base vertices.**  The colour of `s(a, b)`
lies in `{c s(b,c), c s(b,d), c s(c,d)}` exactly when `a + b = c + d` in `ZMod m`; the two other
possibilities are excluded by the distinctness of the four vertices (they would give `a = c` resp.
`a = d`). -/
theorem mem_B_base_ab {m : ℕ} (hm0 : 0 < m) {a b c d : Verts (m + 1)} (hbase : FourBase a b c d) :
    (ghostCol m hm0 s(a, b) ∈ ({ghostCol m hm0 s(b, c), ghostCol m hm0 s(b, d),
      ghostCol m hm0 s(c, d)} : Finset (Fin m)))
      ↔ (a.val : ZMod m) + (b.val : ZMod m) = (c.val : ZMod m) + (d.val : ZMod m) := by
  have hb : a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
      a ≠ Fin.last m ∧ b ≠ Fin.last m ∧ c ≠ Fin.last m ∧ d ≠ Fin.last m := hbase
  obtain ⟨hab, hac, had, hbc, hbd, hcd, hal, hbl, hcl, hdl⟩ := hb
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro h
    rcases h with h | h | h
    · exact (ghostCol_ne_last hm0 ⟨hal, hbl, hcl⟩ hac
        (h.trans (ghostCol_swap m hm0 c b).symm)).elim
    · exact (ghostCol_ne_last hm0 ⟨hal, hbl, hdl⟩ had
        (h.trans (ghostCol_swap m hm0 d b).symm)).elim
    · have hz := (ghostCol_eq_iff m hm0 a b c d).mp h
      rw [ghostZ_base hal hbl, ghostZ_base hcl hdl] at hz
      exact hz
  · intro hz
    exact Or.inr (Or.inr (ghostCol_eq_of_zmod hm0
      (by rw [ghostZ_base hal hbl, ghostZ_base hcl hdl]; exact hz)))

/-- As `mem_B_base_ab`, for the colour of `s(a, c)`. -/
theorem mem_B_base_ac {m : ℕ} (hm0 : 0 < m) {a b c d : Verts (m + 1)} (hbase : FourBase a b c d) :
    (ghostCol m hm0 s(a, c) ∈ ({ghostCol m hm0 s(b, c), ghostCol m hm0 s(b, d),
      ghostCol m hm0 s(c, d)} : Finset (Fin m)))
      ↔ (a.val : ZMod m) + (c.val : ZMod m) = (b.val : ZMod m) + (d.val : ZMod m) := by
  have hb : a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
      a ≠ Fin.last m ∧ b ≠ Fin.last m ∧ c ≠ Fin.last m ∧ d ≠ Fin.last m := hbase
  obtain ⟨hab, hac, had, hbc, hbd, hcd, hal, hbl, hcl, hdl⟩ := hb
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro h
    rcases h with h | h | h
    · exact (ghostCol_ne_last hm0 ⟨hal, hcl, hbl⟩ hab h).elim
    · have hz := (ghostCol_eq_iff m hm0 a c b d).mp h
      rw [ghostZ_base hal hcl, ghostZ_base hbl hdl] at hz
      exact hz
    · exact (ghostCol_ne_last hm0 ⟨hal, hcl, hdl⟩ had
        (h.trans (ghostCol_swap m hm0 d c).symm)).elim
  · intro hz
    exact Or.inr (Or.inl (ghostCol_eq_of_zmod hm0
      (by rw [ghostZ_base hal hcl, ghostZ_base hbl hdl]; exact hz)))

/-- As `mem_B_base_ab`, for the colour of `s(a, d)`. -/
theorem mem_B_base_ad {m : ℕ} (hm0 : 0 < m) {a b c d : Verts (m + 1)} (hbase : FourBase a b c d) :
    (ghostCol m hm0 s(a, d) ∈ ({ghostCol m hm0 s(b, c), ghostCol m hm0 s(b, d),
      ghostCol m hm0 s(c, d)} : Finset (Fin m)))
      ↔ (a.val : ZMod m) + (d.val : ZMod m) = (b.val : ZMod m) + (c.val : ZMod m) := by
  have hb : a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
      a ≠ Fin.last m ∧ b ≠ Fin.last m ∧ c ≠ Fin.last m ∧ d ≠ Fin.last m := hbase
  obtain ⟨hab, hac, had, hbc, hbd, hcd, hal, hbl, hcl, hdl⟩ := hb
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro h
    rcases h with h | h | h
    · have hz := (ghostCol_eq_iff m hm0 a d b c).mp h
      rw [ghostZ_base hal hdl, ghostZ_base hbl hcl] at hz
      exact hz
    · exact (ghostCol_ne_last hm0 ⟨hal, hdl, hbl⟩ hab h).elim
    · exact (ghostCol_ne_last hm0 ⟨hal, hdl, hcl⟩ hac h).elim
  · intro hz
    exact Or.inl (ghostCol_eq_of_zmod hm0
      (by rw [ghostZ_base hal hdl, ghostZ_base hbl hcl]; exact hz))

/-- **The ghost edges of a `K₄` containing `∞`.**  The colour of `s(∞, x)` lies in
`{c s(x,y), c s(x,z), c s(y,z)}` exactly when `2x = y + z` in `ZMod m`: the coincidence with
`s(x, y)` would give `2x = x + y`, i.e. `x = y`, and similarly for `s(x, z)`. -/
theorem mem_B_last {m : ℕ} (hm0 : 0 < m) {x y z : Verts (m + 1)} (hxy : x ≠ y) (hxz : x ≠ z)
    (hxl : x ≠ Fin.last m) (hyl : y ≠ Fin.last m) (hzl : z ≠ Fin.last m) :
    (ghostCol m hm0 s(Fin.last m, x) ∈ ({ghostCol m hm0 s(x, y), ghostCol m hm0 s(x, z),
      ghostCol m hm0 s(y, z)} : Finset (Fin m)))
      ↔ (2 : ZMod m) * (x.val : ZMod m) = (y.val : ZMod m) + (z.val : ZMod m) := by
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro h
    rcases h with h | h | h
    · have hz := (ghostCol_eq_iff m hm0 _ _ x y).mp h
      rw [ghostZ_last m, ghostZ_base hxl hyl] at hz
      exact absurd (fin_zmod_base_inj hm0 hxl hyl
        (add_left_cancel (by simpa only [two_mul] using hz))) hxy
    · have hz := (ghostCol_eq_iff m hm0 _ _ x z).mp h
      rw [ghostZ_last m, ghostZ_base hxl hzl] at hz
      exact absurd (fin_zmod_base_inj hm0 hxl hzl
        (add_left_cancel (by simpa only [two_mul] using hz))) hxz
    · have hz := (ghostCol_eq_iff m hm0 _ _ y z).mp h
      rwa [ghostZ_last m, ghostZ_base hyl hzl] at hz
  · intro hz
    exact Or.inr (Or.inr (ghostCol_eq_of_zmod hm0
      (by rw [ghostZ_last m, ghostZ_base hyl hzl]; exact hz)))

/-- The union of two three-element finsets is the corresponding six-element finset. -/
private lemma union_three {α : Type*} [DecidableEq α] (a b c d e f : α) :
    ({a, b, c} : Finset α) ∪ ({d, e, f} : Finset α) = {a, b, c, d, e, f} := by
  ext w
  simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, or_false]
  tauto

/-! ### A `K₄` of base vertices: at least five colours -/

/-- **A `K₄` avoiding the ghost vertex spans at least five colours** in the ghost colouring (it is
the sum colouring there, and `m` is odd).  The proof splits the six colours into the "star" at `a`
and the "triangle" on `{b, c, d}`; each of the two triples has three distinct colours, and at most
one colour of the first triple can coincide with a colour of the second (two coincidences would
force two of the vertices to be equal, `collision_12` / `collision_13` / `collision_23`). -/
theorem ghost_four_base {m : ℕ} (hm0 : 0 < m) (hm : m % 2 = 1) {a b c d : Verts (m + 1)}
    (hbase : FourBase a b c d) :
    5 ≤ ({ghostCol m hm0 s(a, b), ghostCol m hm0 s(a, c), ghostCol m hm0 s(a, d),
      ghostCol m hm0 s(b, c), ghostCol m hm0 s(b, d), ghostCol m hm0 s(c, d)} : Finset (Fin m)).card := by
  have hb : a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
      a ≠ Fin.last m ∧ b ≠ Fin.last m ∧ c ≠ Fin.last m ∧ d ≠ Fin.last m := hbase
  obtain ⟨hab, hac, had, hbc, hbd, hcd, hal, hbl, hcl, hdl⟩ := hb
  set A : Finset (Fin m) := {ghostCol m hm0 s(a, b), ghostCol m hm0 s(a, c),
    ghostCol m hm0 s(a, d)} with hA
  set B : Finset (Fin m) := {ghostCol m hm0 s(b, c), ghostCol m hm0 s(b, d),
    ghostCol m hm0 s(c, d)} with hB
  have hA1 : ghostCol m hm0 s(a, b) ≠ ghostCol m hm0 s(a, c) :=
    ghostCol_ne_first hm0 ⟨hal, hbl, hcl⟩ hbc
  have hA2 : ghostCol m hm0 s(a, b) ≠ ghostCol m hm0 s(a, d) :=
    ghostCol_ne_first hm0 ⟨hal, hbl, hdl⟩ hbd
  have hA3 : ghostCol m hm0 s(a, c) ≠ ghostCol m hm0 s(a, d) :=
    ghostCol_ne_first hm0 ⟨hal, hcl, hdl⟩ hcd
  have hB1 : ghostCol m hm0 s(b, c) ≠ ghostCol m hm0 s(b, d) :=
    ghostCol_ne_first hm0 ⟨hbl, hcl, hdl⟩ hcd
  have hB2 : ghostCol m hm0 s(b, c) ≠ ghostCol m hm0 s(c, d) := by
    intro he
    exact ghostCol_ne_last hm0 ⟨hbl, hcl, hdl⟩ hbd
      (he.trans (ghostCol_swap m hm0 d c).symm)
  have hB3 : ghostCol m hm0 s(b, d) ≠ ghostCol m hm0 s(c, d) :=
    ghostCol_ne_last hm0 ⟨hbl, hdl, hcl⟩ hbc
  have hcardA : 3 ≤ A.card := by
    refine card_ge_three hA1 hA2 hA3 ⟨?_, ?_, ?_⟩
    · rw [hA]; exact Finset.mem_insert.mpr (Or.inl rfl)
    · rw [hA]; exact Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inl rfl)))
    · rw [hA]
      exact Finset.mem_insert.mpr
        (Or.inr (Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr rfl))))
  have hcardB : 3 ≤ B.card := by
    refine card_ge_three hB1 hB2 hB3 ⟨?_, ?_, ?_⟩
    · rw [hB]; exact Finset.mem_insert.mpr (Or.inl rfl)
    · rw [hB]; exact Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inl rfl)))
    · rw [hB]
      exact Finset.mem_insert.mpr
        (Or.inr (Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr rfl))))
  have hmem : A ∩ B ⊆
      {ghostCol m hm0 s(a, b), ghostCol m hm0 s(a, c), ghostCol m hm0 s(a, d)} := by
    intro w hw
    have hw' := Finset.mem_inter.mp hw
    rcases mem_three hA hw'.1 with h | h | h
    · exact Finset.mem_insert.mpr (Or.inl h)
    · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inl h)))
    · exact Finset.mem_insert.mpr
        (Or.inr (Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr h))))
  have h12 : ¬ ((ghostCol m hm0 s(a, b) ∈ B) ∧ (ghostCol m hm0 s(a, c) ∈ B)) := by
    rintro ⟨h1, h2⟩
    have h1' : ghostCol m hm0 s(a, b) ∈
        ({ghostCol m hm0 s(b, c), ghostCol m hm0 s(b, d), ghostCol m hm0 s(c, d)} :
          Finset (Fin m)) := h1
    have h2' : ghostCol m hm0 s(a, c) ∈
        ({ghostCol m hm0 s(b, c), ghostCol m hm0 s(b, d), ghostCol m hm0 s(c, d)} :
          Finset (Fin m)) := h2
    have e1 : (a.val : ZMod m) + (b.val : ZMod m) = (c.val : ZMod m) + (d.val : ZMod m) :=
      (mem_B_base_ab hm0 hbase).mp h1'
    have e2 : (a.val : ZMod m) + (c.val : ZMod m) = (b.val : ZMod m) + (d.val : ZMod m) :=
      (mem_B_base_ac hm0 hbase).mp h2'
    exact had (fin_zmod_base_inj hm0 hal hdl (collision_12 (e1 := e1) (e2 := e2) hm))
  have h13 : ¬ ((ghostCol m hm0 s(a, b) ∈ B) ∧ (ghostCol m hm0 s(a, d) ∈ B)) := by
    rintro ⟨h1, h2⟩
    have h1' : ghostCol m hm0 s(a, b) ∈
        ({ghostCol m hm0 s(b, c), ghostCol m hm0 s(b, d), ghostCol m hm0 s(c, d)} :
          Finset (Fin m)) := h1
    have h2' : ghostCol m hm0 s(a, d) ∈
        ({ghostCol m hm0 s(b, c), ghostCol m hm0 s(b, d), ghostCol m hm0 s(c, d)} :
          Finset (Fin m)) := h2
    have e1 : (a.val : ZMod m) + (b.val : ZMod m) = (c.val : ZMod m) + (d.val : ZMod m) :=
      (mem_B_base_ab hm0 hbase).mp h1'
    have e3 : (a.val : ZMod m) + (d.val : ZMod m) = (b.val : ZMod m) + (c.val : ZMod m) :=
      (mem_B_base_ad hm0 hbase).mp h2'
    exact hac (fin_zmod_base_inj hm0 hal hcl (collision_13 (e1 := e1) (e3 := e3) hm))
  have h23 : ¬ ((ghostCol m hm0 s(a, c) ∈ B) ∧ (ghostCol m hm0 s(a, d) ∈ B)) := by
    rintro ⟨h1, h2⟩
    have h1' : ghostCol m hm0 s(a, c) ∈
        ({ghostCol m hm0 s(b, c), ghostCol m hm0 s(b, d), ghostCol m hm0 s(c, d)} :
          Finset (Fin m)) := h1
    have h2' : ghostCol m hm0 s(a, d) ∈
        ({ghostCol m hm0 s(b, c), ghostCol m hm0 s(b, d), ghostCol m hm0 s(c, d)} :
          Finset (Fin m)) := h2
    have e2 : (a.val : ZMod m) + (c.val : ZMod m) = (b.val : ZMod m) + (d.val : ZMod m) :=
      (mem_B_base_ac hm0 hbase).mp h1'
    have e3 : (a.val : ZMod m) + (d.val : ZMod m) = (b.val : ZMod m) + (c.val : ZMod m) :=
      (mem_B_base_ad hm0 hbase).mp h2'
    exact hab (fin_zmod_base_inj hm0 hal hbl (collision_23 (e2 := e2) (e3 := e3) hm))
  have h5 : 5 ≤ (A ∪ B).card :=
    card_union_ge_five hcardA hcardB (card_inter_le_one hmem h12 h13 h23)
  rw [hA, hB, union_three] at h5
  exact h5

/-- Membership in a three-element finset, read in a prescribed order. -/
private lemma mem_cons3 {α : Type*} [DecidableEq α] {p q r w : α} :
    w ∈ ({p, q, r} : Finset α) ↔ w = p ∨ w = q ∨ w = r := by
  simp only [Finset.mem_insert, Finset.mem_singleton]

/-- Membership in a three-element finset, transferred along an equality of the finsets (used to
read the three "far" colours in the order needed by `ghost_col_mem`). -/
private lemma mem_cons3_of {α : Type*} [DecidableEq α] {p q r p' q' r' w : α}
    (hset : ({p, q, r} : Finset α) = ({p', q', r'} : Finset α)) (hw : w ∈ ({p, q, r} : Finset α)) :
    w = p' ∨ w = q' ∨ w = r' := by
  rw [hset] at hw
  exact (mem_cons3).mp hw

/-- Any permutation of three elements gives the same finset. -/
private lemma finset_three_comm {α : Type*} [DecidableEq α] (p q r : α) :
    ({p, q, r} : Finset α) = ({q, r, p} : Finset α) ∧ ({p, q, r} : Finset α) = ({r, p, q} : Finset α) :=
  ⟨by ext w; simp [or_comm, or_left_comm, or_assoc], by
      ext w; simp [or_comm, or_left_comm, or_assoc]⟩

/-- **A ghost colour can only coincide with the opposite edge.**  If the colour of the ghost edge
`s(∞, u)` is one of the three "far" colours `{c s(u,v), c s(u,w), c s(v,w)}` of the `K₄`
`{∞, u, v, w}`, then it is the colour of the *opposite* edge `s(v, w)`, i.e. `2u = v + w` in
`ZMod m`; the two other possibilities would give `u = v` resp. `u = w`. -/
private lemma ghost_col_mem {m : ℕ} (hm0 : 0 < m) {u v w₀ : Verts (m + 1)}
    (huv : u ≠ v) (huw : u ≠ w₀) (hvw : v ≠ w₀) (hul : u ≠ Fin.last m) (hvl : v ≠ Fin.last m)
    (hwl : w₀ ≠ Fin.last m) {c₀ : Fin m} (h0 : c₀ = ghostCol m hm0 s(Fin.last m, u))
    (h1 : c₀ = ghostCol m hm0 s(u, v) ∨ c₀ = ghostCol m hm0 s(u, w₀) ∨
      c₀ = ghostCol m hm0 s(v, w₀)) :
    (2 : ZMod m) * (u.val : ZMod m) = (v.val : ZMod m) + (w₀.val : ZMod m) := by
  subst h0
  rcases h1 with h1 | h1 | h1
  · exfalso
    have hz := (ghostCol_eq_iff m hm0 _ _ u v).mp h1
    rw [ghostZ_last m, ghostZ_base hul hvl] at hz
    exact huv (fin_zmod_base_inj hm0 hul hvl
      (add_left_cancel (by simpa only [two_mul] using hz)))
  · exfalso
    have hz := (ghostCol_eq_iff m hm0 _ _ u w₀).mp h1
    rw [ghostZ_last m, ghostZ_base hul hwl] at hz
    exact huw (fin_zmod_base_inj hm0 hul hwl
      (add_left_cancel (by simpa only [two_mul] using hz)))
  · have hz := (ghostCol_eq_iff m hm0 _ _ v w₀).mp h1
    rwa [ghostZ_last m, ghostZ_base hvl hwl] at hz

/-! ### A `K₄` containing the ghost vertex: at least five colours -/

/-- **A `K₄` containing the ghost vertex spans at least five colours** in the ghost colouring, for
`m` odd and `3 ∤ m`.  The six colours are `2x, 2y, 2z, x+y, x+z, y+z`; the first triple and the
second are each three distinct colours, and at most one colour of the first triple can coincide
with a colour of the second, because two such "cross" coincidences would give `3x = 3y` in
`ZMod m` (`cross_12`, `cross_13`, `cross_23`). -/
theorem ghost_four_last {m : ℕ} (hm0 : 0 < m) (hm : m % 2 = 1) (h3 : ¬ 3 ∣ m)
    {x y z : Verts (m + 1)} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hxl : x ≠ Fin.last m) (hyl : y ≠ Fin.last m) (hzl : z ≠ Fin.last m) :
    5 ≤ ({ghostCol m hm0 s(Fin.last m, x), ghostCol m hm0 s(Fin.last m, y),
      ghostCol m hm0 s(Fin.last m, z), ghostCol m hm0 s(x, y), ghostCol m hm0 s(x, z),
      ghostCol m hm0 s(y, z)} : Finset (Fin m)).card := by
  set A : Finset (Fin m) := {ghostCol m hm0 s(Fin.last m, x), ghostCol m hm0 s(Fin.last m, y),
    ghostCol m hm0 s(Fin.last m, z)} with hA
  set B : Finset (Fin m) := {ghostCol m hm0 s(x, y), ghostCol m hm0 s(x, z),
    ghostCol m hm0 s(y, z)} with hB
  have hA1 : ghostCol m hm0 s(Fin.last m, x) ≠ ghostCol m hm0 s(Fin.last m, y) :=
    ghostCol_last_ne hm0 hm hxl hyl hxy
  have hA2 : ghostCol m hm0 s(Fin.last m, x) ≠ ghostCol m hm0 s(Fin.last m, z) :=
    ghostCol_last_ne hm0 hm hxl hzl hxz
  have hA3 : ghostCol m hm0 s(Fin.last m, y) ≠ ghostCol m hm0 s(Fin.last m, z) :=
    ghostCol_last_ne hm0 hm hyl hzl hyz
  have hB1 : ghostCol m hm0 s(x, y) ≠ ghostCol m hm0 s(x, z) :=
    ghostCol_ne_first hm0 ⟨hxl, hyl, hzl⟩ hyz
  have hB2 : ghostCol m hm0 s(x, y) ≠ ghostCol m hm0 s(y, z) := by
    intro he
    exact ghostCol_ne_last hm0 ⟨hxl, hyl, hzl⟩ hxz
      (he.trans (ghostCol_swap m hm0 z y).symm)
  have hB3 : ghostCol m hm0 s(x, z) ≠ ghostCol m hm0 s(y, z) :=
    ghostCol_ne_last hm0 ⟨hxl, hzl, hyl⟩ hxy
  have hcardA : 3 ≤ A.card := by
    refine card_ge_three hA1 hA2 hA3 ⟨?_, ?_, ?_⟩
    · rw [hA]; exact Finset.mem_insert.mpr (Or.inl rfl)
    · rw [hA]; exact Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inl rfl)))
    · rw [hA]
      exact Finset.mem_insert.mpr
        (Or.inr (Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr rfl))))
  have hcardB : 3 ≤ B.card := by
    refine card_ge_three hB1 hB2 hB3 ⟨?_, ?_, ?_⟩
    · rw [hB]; exact Finset.mem_insert.mpr (Or.inl rfl)
    · rw [hB]; exact Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inl rfl)))
    · rw [hB]
      exact Finset.mem_insert.mpr
        (Or.inr (Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr rfl))))
  have hmem : A ∩ B ⊆ {ghostCol m hm0 s(Fin.last m, x), ghostCol m hm0 s(Fin.last m, y),
      ghostCol m hm0 s(Fin.last m, z)} := by
    intro w hw
    have hw' := Finset.mem_inter.mp hw
    rcases mem_three hA hw'.1 with h | h | h
    · exact Finset.mem_insert.mpr (Or.inl h)
    · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inl h)))
    · exact Finset.mem_insert.mpr
        (Or.inr (Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr h))))
  have far1 : ∀ w : Fin m, w ∈ B →
      w = ghostCol m hm0 s(x, y) ∨ w = ghostCol m hm0 s(x, z) ∨ w = ghostCol m hm0 s(y, z) := by
    intro w hw
    rcases (mem_three hB hw) with rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  have far2 : ∀ w : Fin m, w ∈ B →
      w = ghostCol m hm0 s(y, x) ∨ w = ghostCol m hm0 s(y, z) ∨ w = ghostCol m hm0 s(x, z) := by
    intro w hw
    rcases (far1 w hw) with rfl | rfl | rfl
    · exact Or.inl ((ghostCol_swap m hm0 y x).symm)
    · exact Or.inr (Or.inr rfl)
    · exact Or.inr (Or.inl rfl)
  have far3 : ∀ w : Fin m, w ∈ B →
      w = ghostCol m hm0 s(z, x) ∨ w = ghostCol m hm0 s(z, y) ∨ w = ghostCol m hm0 s(x, y) := by
    intro w hw
    rcases (far1 w hw) with rfl | rfl | rfl
    · exact Or.inr (Or.inr rfl)
    · exact Or.inl ((ghostCol_swap m hm0 z x).symm)
    · exact Or.inr (Or.inl ((ghostCol_swap m hm0 z y).symm))
  have h12 : ¬ ((ghostCol m hm0 s(Fin.last m, x) ∈ B)
      ∧ (ghostCol m hm0 s(Fin.last m, y) ∈ B)) := by
    rintro ⟨h1, h2⟩
    have e1 := ghost_col_mem hm0 hxy hxz hyz hxl hyl hzl rfl (far1 _ h1)
    have e2 := ghost_col_mem hm0 hxy.symm hyz hxz hyl hxl hzl rfl (far2 _ h2)
    exact hxy (fin_zmod_base_inj hm0 hxl hyl (cross_12 (e1 := e1) (e2 := e2) h3))
  have h13 : ¬ ((ghostCol m hm0 s(Fin.last m, x) ∈ B)
      ∧ (ghostCol m hm0 s(Fin.last m, z) ∈ B)) := by
    rintro ⟨h1, h2⟩
    have e1 := ghost_col_mem hm0 hxy hxz hyz hxl hyl hzl rfl (far1 _ h1)
    have e3 := ghost_col_mem hm0 hxz.symm hyz.symm hxy hzl hxl hyl rfl (far3 _ h2)
    exact hxz (fin_zmod_base_inj hm0 hxl hzl (cross_13 (e1 := e1) (e3 := e3) h3))
  have h23 : ¬ ((ghostCol m hm0 s(Fin.last m, y) ∈ B)
      ∧ (ghostCol m hm0 s(Fin.last m, z) ∈ B)) := by
    rintro ⟨h1, h2⟩
    have e2 := ghost_col_mem hm0 hxy.symm hyz hxz hyl hxl hzl rfl (far2 _ h1)
    have e3 := ghost_col_mem hm0 hxz.symm hyz.symm hxy hzl hxl hyl rfl (far3 _ h2)
    exact hyz (fin_zmod_base_inj hm0 hyl hzl (cross_23 (e2 := e2) (e3 := e3) h3))
  have h5 : 5 ≤ (A ∪ B).card :=
    card_union_ge_five hcardA hcardB (card_inter_le_one hmem h12 h13 h23)
  rw [hA, hB, union_three] at h5
  exact h5

/-! ### The ghost colouring is admissible -/

/-- The colour of an edge between two vertices of a clique occurs in `colorsOn` of the clique. -/
private lemma col_mem {n k : ℕ} (c : Col n k) {S : Finset (Verts n)} {x y : Verts n}
    (hx : x ∈ S) (hy : y ∈ S) (hxy : x ≠ y) : c s(x, y) ∈ colorsOn c S :=
  Finset.mem_image.mpr ⟨s(x, y), mem_edgeFinset_mk hx hy hxy, rfl⟩

/-- **The ghost colouring of `K_{m+1}` with `m` colours is admissible** whenever `m` is odd and
`3 ∤ m`: every four-vertex clique spans at least five colours, which is exactly the catalog
condition of `JSP-000140`. -/
theorem admissible_ghost (m : ℕ) (hm0 : 0 < m) (hm : m % 2 = 1) (h3 : ¬ 3 ∣ m) :
    Admissible (ghostCol m hm0) := by
  intro S hS
  obtain ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, hS'⟩ := Finset.card_eq_four.mp hS
  have haS : a ∈ S := by rw [hS']; simp
  have hbS : b ∈ S := by rw [hS']; simp
  have hcS : c ∈ S := by rw [hS']; simp
  have hdS : d ∈ S := by rw [hS']; simp
  by_cases haL : a = Fin.last m
  · have hbl : b ≠ Fin.last m := fun h => (Ne.symm hab) (h.trans haL.symm)
    have hcl : c ≠ Fin.last m := fun h => (Ne.symm hac) (h.trans haL.symm)
    have hdl : d ≠ Fin.last m := fun h => (Ne.symm had) (h.trans haL.symm)
    refine le_trans (ghost_four_last hm0 hm h3 (x := b) (y := c) (z := d) hbc hbd hcd hbl hcl
      hdl) ?_
    refine Finset.card_le_card ?_
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [← haL]; exact col_mem _ haS hbS hab
    · rw [← haL]; exact col_mem _ haS hcS hac
    · rw [← haL]; exact col_mem _ haS hdS had
    · exact col_mem _ hbS hcS hbc
    · exact col_mem _ hbS hdS hbd
    · exact col_mem _ hcS hdS hcd
  by_cases hbL : b = Fin.last m
  · have hal : a ≠ Fin.last m := fun h => hab (h.trans hbL.symm)
    have hcl : c ≠ Fin.last m := fun h => hbc.symm (h.trans hbL.symm)
    have hdl : d ≠ Fin.last m := fun h => hbd.symm (h.trans hbL.symm)
    refine le_trans (ghost_four_last hm0 hm h3 (x := a) (y := c) (z := d) hac had hcd hal hcl
      hdl) ?_
    refine Finset.card_le_card ?_
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [← hbL]; exact col_mem _ hbS haS hab.symm
    · rw [← hbL]; exact col_mem _ hbS hcS hbc
    · rw [← hbL]; exact col_mem _ hbS hdS hbd
    · exact col_mem _ haS hcS hac
    · exact col_mem _ haS hdS had
    · exact col_mem _ hcS hdS hcd
  by_cases hcL : c = Fin.last m
  · have hal : a ≠ Fin.last m := fun h => hac (h.trans hcL.symm)
    have hbl : b ≠ Fin.last m := fun h => hbc (h.trans hcL.symm)
    have hdl : d ≠ Fin.last m := fun h => hcd.symm (h.trans hcL.symm)
    refine le_trans (ghost_four_last hm0 hm h3 (x := a) (y := b) (z := d) hab had hbd hal hbl
      hdl) ?_
    refine Finset.card_le_card ?_
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [← hcL]; exact col_mem _ hcS haS hac.symm
    · rw [← hcL]; exact col_mem _ hcS hbS hbc.symm
    · rw [← hcL]; exact col_mem _ hcS hdS hcd
    · exact col_mem _ haS hbS hab
    · exact col_mem _ haS hdS had
    · exact col_mem _ hbS hdS hbd
  by_cases hdL : d = Fin.last m
  · have hal : a ≠ Fin.last m := fun h => had (h.trans hdL.symm)
    have hbl : b ≠ Fin.last m := fun h => hbd (h.trans hdL.symm)
    have hcl : c ≠ Fin.last m := fun h => hcd (h.trans hdL.symm)
    refine le_trans (ghost_four_last hm0 hm h3 (x := a) (y := b) (z := c) hab hac hbc hal hbl
      hcl) ?_
    refine Finset.card_le_card ?_
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [← hdL]; exact col_mem _ hdS haS had.symm
    · rw [← hdL]; exact col_mem _ hdS hbS hbd.symm
    · rw [← hdL]; exact col_mem _ hdS hcS hcd.symm
    · exact col_mem _ haS hbS hab
    · exact col_mem _ haS hcS hac
    · exact col_mem _ hbS hcS hbc
  · refine le_trans (ghost_four_base hm0 hm
      ⟨hab, hac, had, hbc, hbd, hcd, haL, hbL, hcL, hdL⟩) ?_
    refine Finset.card_le_card ?_
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl
    · exact col_mem _ haS hbS hab
    · exact col_mem _ haS hcS hac
    · exact col_mem _ haS hdS had
    · exact col_mem _ hbS hcS hbc
    · exact col_mem _ hbS hdS hbd
    · exact col_mem _ hcS hdS hcd

/-! ### Consequences: `f(n,4,5) ≤ n - 1` -/

/-- **The upper bound `f(m+1, 4, 5) ≤ m`** for every odd `m` with `3 ∤ m`, i.e. `f(n,4,5) ≤ n - 1`
for `n = m + 1`: the ghost colouring of `K_{m+1}` with `m` colours is admissible. -/
theorem EG_le_ghost (m : ℕ) (hm0 : 0 < m) (hm : m % 2 = 1) (h3 : ¬ 3 ∣ m) : EG (m + 1) ≤ m :=
  EG_le (m + 1) m (ghostCol m hm0) (admissible_ghost m hm0 hm h3)

end JSP140
