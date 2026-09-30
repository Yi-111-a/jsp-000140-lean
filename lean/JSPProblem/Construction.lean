import JSPProblem.Counting

/-!
# JSP-000140 — a linear construction: the sum (round-robin) colouring

The catalog answer (BCDP22, arXiv:2207.02920) is `f(n, 4, 5) = 5n/6 + o(n)`.  The *upper* half of
this needs colourings of `K_n` that use few colours, the *lower* half needs that every such
colouring uses many colours.  This file provides the **upper** half for the easy range of `ε`:
the classical *sum colouring* (also called the round-robin or starter colouring)

    c({a, b}) = a + b  (mod m)

of `K_n` with `m` colours, `n ≤ m`.  Its two relevant properties are:

* it is **proper**: two edges with a common endpoint get different colours, so a `K₄` can only
  have two edges of one colour if they are *disjoint*; and
* for **odd** `m`, at most one pair of disjoint edges of a `K₄` shares a colour (because two such
  pairs would force `2(a - d) ≡ 0 (mod m)`, i.e. `a = d`).

Consequently every `K₄` spans at least five colours when `m` is odd, so

* `EG n ≤ n` for odd `n` (take `m = n`), and
* `EG n ≤ n + 1` for every `n` (take `m = n + 1`, which is odd when `n` is even).

Together with the classical counting lower bound `3(n-1)/4 ≤ f(n,4,5)` of `Counting.lean` this
gives the first genuine two-sided shape bound of the development (see `Main.fiveSixthShape`):
`|f(n,4,5) - 5n/6| ≤ n/6 + 1`, i.e. `f(n,4,5) = 5n/6 + O(n)`.
-/

namespace JSP140

variable {n m : ℕ}

/-! ### The sum colouring -/

/-- **The sum colouring** (round-robin colouring) of `K_n` with `m` colours, where `n ≤ m`: the
edge `{a, b}` receives the colour `(a + b) mod m`.  For `m = n` this is the classical round-robin
colouring of a tournament schedule; it uses exactly `m` colours. -/
def sumColMod (m n : ℕ) (h : n ≤ m) : Col n m :=
  Sym2.rec (motive := fun _ => Fin m)
    (fun a b => ⟨(a.val + b.val) % m, Nat.mod_lt _ (by have := a.isLt; omega)⟩)
    (by
      intro a b c d h
      cases h with
      | refl => rfl
      | swap x y => simp [Nat.add_comm])

/-- The sum colouring of `K_n` with exactly `n` colours: the edge `{a, b}` gets the colour
`(a + b) mod n`. -/
abbrev sumCol (n : ℕ) : Col n n := sumColMod n n (le_refl n)

@[simp] theorem sumColMod_val_mk (m n : ℕ) (h : n ≤ m) (a b : Verts n) :
    (sumColMod m n h s(a, b)).val = (a.val + b.val) % m := rfl

theorem sumCol_val_mk (n : ℕ) (a b : Verts n) : (sumCol n s(a, b)).val = (a.val + b.val) % n :=
  sumColMod_val_mk n n _ a b

/-! ### Arithmetic in `ZMod m` -/

theorem natCast_zmod_inj (_hm : 0 < m) {x y : ℕ} (hx : x < m) (hy : y < m)
    (h : (x : ZMod m) = (y : ZMod m)) : x = y := by
  have h' := congrArg (fun t : ZMod m => t.val) h
  simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] using h'

theorem natCast_zmod_eq_iff (_hm : 0 < m) {x y : ℕ} :
    (x : ZMod m) = (y : ZMod m) ↔ x % m = y % m := by
  constructor
  · intro h
    have h' := congrArg (fun t : ZMod m => t.val) h
    simpa only [ZMod.val_natCast] using h'
  · intro h
    rw [← ZMod.natCast_mod x m, ← ZMod.natCast_mod y m, h]

/-- **Odd modulus.**  For `m` odd, multiplication by `2` in `ZMod m` is injective: `2` is a unit.
This is exactly the step that makes the sum colouring admissible for odd `m` and fails for even
`m` (where the two collisions `a+b = c+d`, `a+c = b+d` can coexist). -/
theorem two_mul_inj (hm : m % 2 = 1) {x y : ZMod m} (h : (2 : ZMod m) * x = (2 : ZMod m) * y) :
    x = y := by
  have hcop : Nat.Coprime 2 m := by
    rw [Nat.prime_two.coprime_iff_not_dvd]
    intro hd
    rw [Nat.dvd_iff_mod_eq_zero] at hd
    omega
  have h2 : (2 : ZMod m) * (2 : ZMod m)⁻¹ = 1 := by
    rw [ZMod.mul_inv_eq_gcd, ZMod.val_two_eq_two_mod]
    have hgcd : Nat.gcd (2 % m) m = 1 := by
      rcases m with _ | _ | m
      · omega
      · simp
      · rw [Nat.mod_eq_of_lt (by omega)]
        exact Nat.coprime_iff_gcd_eq_one.mpr hcop
    rw [hgcd, Nat.cast_one]
  have h2' : (2 : ZMod m)⁻¹ * 2 = 1 := by rw [mul_comm]; exact h2
  have h' := congrArg (fun t : ZMod m => (2 : ZMod m)⁻¹ * t) h
  rwa [← mul_assoc, h2', one_mul, ← mul_assoc, h2', one_mul] at h'

/-- Two vertices of `K_n` whose residues modulo `m` agree are equal. -/
theorem fin_zmod_inj {n m : ℕ} (h : n ≤ m) {a b : Verts n}
    (hab : (a.val : ZMod m) = (b.val : ZMod m)) : a = b := by
  refine Fin.ext ?_
  exact natCast_zmod_inj (lt_of_lt_of_le (Nat.zero_lt_of_lt a.isLt) h)
    (lt_of_lt_of_le a.isLt h) (lt_of_lt_of_le b.isLt h) hab

/-- Two edges of the sum colouring have the same colour exactly when the corresponding sums of
vertices agree modulo `m`. -/
theorem sumColMod_eq_iff (h : n ≤ m) {a b c d : Verts n} :
    sumColMod m n h s(a, b) = sumColMod m n h s(c, d) ↔
      (a.val : ZMod m) + (b.val : ZMod m) = (c.val : ZMod m) + (d.val : ZMod m) := by
  have hm : 0 < m := lt_of_lt_of_le (Nat.zero_lt_of_lt a.isLt) h
  constructor
  · intro he
    have h' := congrArg (fun t : Fin m => (t.val : ZMod m)) he
    simpa only [sumColMod_val_mk, ZMod.natCast_mod, Nat.cast_add] using h'
  · intro hz
    refine Fin.ext ?_
    have hz' : ((a.val + b.val : ℕ) : ZMod m) = ((c.val + d.val : ℕ) : ZMod m) := by
      simpa only [Nat.cast_add] using hz
    exact (natCast_zmod_eq_iff hm).mp hz'

/-! ### The two structural properties of the sum colouring -/

/-- The sum colouring does not depend on the order of the two endpoints of an edge. -/
theorem sumColMod_swap (m n : ℕ) (h : n ≤ m) (x y : Verts n) :
    sumColMod m n h s(y, x) = sumColMod m n h s(x, y) :=
  congrArg _ (Sym2.sound (Sym2.rel_iff.mpr (Or.inr ⟨rfl, rfl⟩)))

/-- **Properness.**  Two edges of the sum colouring with a common endpoint have different colours.
Hence a `K₄` can carry two edges of one colour only if they are *disjoint*. -/
theorem sumColMod_adj_ne (h : n ≤ m) {x y z : Verts n} (hyz : y ≠ z) :
    sumColMod m n h s(x, y) ≠ sumColMod m n h s(x, z) := by
  intro he
  exact hyz (fin_zmod_inj h (add_left_cancel ((sumColMod_eq_iff h).mp he)))

/-- **Properness**, with the common endpoint written last. -/
theorem sumColMod_adj_ne_last (h : n ≤ m) {x y z : Verts n} (hxy : x ≠ y) :
    sumColMod m n h s(x, z) ≠ sumColMod m n h s(y, z) := by
  intro he
  exact hxy (fin_zmod_inj h (add_right_cancel ((sumColMod_eq_iff h).mp he)))

/-- **Properness**, with the common endpoint written first in one edge and second in the other. -/
theorem sumColMod_adj_ne_mid (h : n ≤ m) {x y z : Verts n} (hxz : x ≠ z) :
    sumColMod m n h s(x, y) ≠ sumColMod m n h s(y, z) := by
  intro he
  have hz := (sumColMod_eq_iff h (a := x) (b := y) (c := y) (d := z)).mp he
  rw [← add_comm (y.val : ZMod m) (x.val : ZMod m)] at hz
  exact hxz (fin_zmod_inj h (add_left_cancel hz))

/-- **At most one monochromatic pair of opposite edges.**  For odd `m`, if two *disjoint* edges
`{a, b}` and `{c, d}` of a `K₄` share a colour, then neither of the other two perfect matchings
`{{a,c},{b,d}}` and `{{a,d},{b,c}}` is monochromatic.  Indeed, if e.g. `a + c = b + d` also held,
adding the two congruences would give `2a = 2d`, i.e. `a = d` because `2` is invertible in
`ZMod m`. -/
theorem sumColMod_one_collision (hm : m % 2 = 1) (h : n ≤ m) {a b c d : Verts n}
    (had : a ≠ d) (hac : a ≠ c)
    (h1 : sumColMod m n h s(a, b) = sumColMod m n h s(c, d)) :
    sumColMod m n h s(a, c) ≠ sumColMod m n h s(b, d) ∧
      sumColMod m n h s(a, d) ≠ sumColMod m n h s(b, c) := by
  have key : ∀ (u v : Verts n), (a.val : ZMod m) + (b.val : ZMod m)
      = (u.val : ZMod m) + (v.val : ZMod m) →
      (a.val : ZMod m) + (u.val : ZMod m) = (b.val : ZMod m) + (v.val : ZMod m) →
      (a.val : ZMod m) = (v.val : ZMod m) := by
    intro u v h2 h3
    have k : (2 : ZMod m) * (a.val : ZMod m) = (2 : ZMod m) * (v.val : ZMod m) := by
      calc (2 : ZMod m) * (a.val : ZMod m) = (a.val : ZMod m) + (a.val : ZMod m) := by ring
        _ = ((a.val : ZMod m) + (b.val : ZMod m)) + ((a.val : ZMod m) + (u.val : ZMod m))
              - ((b.val : ZMod m) + (u.val : ZMod m)) := by ring
        _ = ((u.val : ZMod m) + (v.val : ZMod m)) + ((b.val : ZMod m) + (v.val : ZMod m))
              - ((b.val : ZMod m) + (u.val : ZMod m)) := by rw [h2, h3]
        _ = (2 : ZMod m) * (v.val : ZMod m) := by ring
    exact two_mul_inj hm k
  have h1' := (sumColMod_eq_iff h).mp h1
  refine ⟨fun h2 => ?_, fun h2 => ?_⟩
  · have h2' := (sumColMod_eq_iff h).mp h2
    exact had (fin_zmod_inj h (key c d h1' h2'))
  · have h2' := (sumColMod_eq_iff h).mp h2
    exact hac (fin_zmod_inj h (key d c (by rw [h1', add_comm]) (by rw [h2', add_comm])))

/-! ### Five distinct colours -/

/-- Five pairwise distinct colours which all occur on a clique span at least five colours. -/
private lemma card_ge_five {n k : ℕ} {c : Col n k} {S : Finset (Verts n)}
    (x₁ x₂ x₃ x₄ x₅ : Fin k) (h₁₂ : x₁ ≠ x₂) (h₁₃ : x₁ ≠ x₃) (h₁₄ : x₁ ≠ x₄) (h₁₅ : x₁ ≠ x₅)
    (h₂₃ : x₂ ≠ x₃) (h₂₄ : x₂ ≠ x₄) (h₂₅ : x₂ ≠ x₅)
    (h₃₄ : x₃ ≠ x₄) (h₃₅ : x₃ ≠ x₅) (h₄₅ : x₄ ≠ x₅)
    (hmem : x₁ ∈ colorsOn c S ∧ x₂ ∈ colorsOn c S ∧ x₃ ∈ colorsOn c S ∧ x₄ ∈ colorsOn c S ∧
      x₅ ∈ colorsOn c S) : 5 ≤ (colorsOn c S).card := by
  have hsub : ({x₁, x₂, x₃, x₄, x₅} : Finset (Fin k)) ⊆ colorsOn c S := by
    intro y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl
    · exact hmem.1
    · exact hmem.2.1
    · exact hmem.2.2.1
    · exact hmem.2.2.2.1
    · exact hmem.2.2.2.2
  have hcard : ({x₁, x₂, x₃, x₄, x₅} : Finset (Fin k)).card = 5 := by
    rw [show ({x₁, x₂, x₃, x₄, x₅} : Finset (Fin k))
        = insert x₁ (insert x₂ (insert x₃ (insert x₄ (insert x₅ ∅)))) from rfl,
      Finset.card_insert_of_notMem (by simp [h₁₂, h₁₃, h₁₄, h₁₅]),
      Finset.card_insert_of_notMem (by simp [h₂₃, h₂₄, h₂₅]),
      Finset.card_insert_of_notMem (by simp [h₃₄, h₃₅]),
      Finset.card_insert_of_notMem (by simp [h₄₅])]
    simp
  calc 5 = ({x₁, x₂, x₃, x₄, x₅} : Finset (Fin k)).card := hcard.symm
    _ ≤ (colorsOn c S).card := Finset.card_le_card hsub

/-- The colour of an edge between two vertices of a clique occurs in `colorsOn` of the clique. -/
private lemma col_mem {n k : ℕ} (c : Col n k) {S : Finset (Verts n)} {x y : Verts n}
    (hx : x ∈ S) (hy : y ∈ S) (hxy : x ≠ y) : c s(x, y) ∈ colorsOn c S :=
  Finset.mem_image.mpr ⟨s(x, y), mem_edgeFinset_mk hx hy hxy, rfl⟩

/-! ### The sum colouring is admissible for odd `m` -/

/-- **The sum colouring of `K_n` with `m` colours (`n ≤ m`) is admissible whenever `m` is odd**:
every four-vertex clique spans at least five colours, as required by the catalog condition of
`JSP-000140`. -/
theorem admissible_sumColMod (hm : m % 2 = 1) (h : n ≤ m) : Admissible (sumColMod m n h) := by
  intro S hS
  obtain ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, hS⟩ := Finset.card_eq_four.mp hS
  have haS : a ∈ S := by rw [hS]; simp
  have hbS : b ∈ S := by rw [hS]; simp
  have hcS : c ∈ S := by rw [hS]; simp
  have hdS : d ∈ S := by rw [hS]; simp
  have mem : ∀ x y : Verts n, x ∈ S → y ∈ S → x ≠ y →
      sumColMod m n h s(x, y) ∈ colorsOn (sumColMod m n h) S :=
    fun _ _ hx hy hxy => col_mem _ hx hy hxy
  by_cases h1 : sumColMod m n h s(a, b) = sumColMod m n h s(c, d)
  · obtain ⟨h25, h34⟩ := sumColMod_one_collision hm h had hac h1
    refine card_ge_five (sumColMod m n h s(a, b)) (sumColMod m n h s(a, c)) (sumColMod m n h s(a, d))
      (sumColMod m n h s(b, c)) (sumColMod m n h s(b, d))
      (sumColMod_adj_ne h hbc) (sumColMod_adj_ne h hbd) (sumColMod_adj_ne_mid h hac)
      (sumColMod_adj_ne_mid h had) (sumColMod_adj_ne h hcd) (sumColMod_adj_ne_last h hab) h25
      h34 (sumColMod_adj_ne_last h hab) (sumColMod_adj_ne h hcd) ?_
    exact ⟨mem a b haS hbS hab, mem a c haS hcS hac, mem a d haS hdS had, mem b c hbS hcS hbc,
      mem b d hbS hdS hbd⟩
  · by_cases h2 : sumColMod m n h s(a, c) = sumColMod m n h s(b, d)
    · obtain ⟨h15, h34'⟩ := sumColMod_one_collision (b := c) (c := b) hm h had hab h2
      have h34 : sumColMod m n h s(a, d) ≠ sumColMod m n h s(b, c) := by
        simpa only [sumColMod_swap] using h34'
      refine card_ge_five (sumColMod m n h s(a, b)) (sumColMod m n h s(a, c)) (sumColMod m n h s(a, d))
        (sumColMod m n h s(b, c)) (sumColMod m n h s(c, d))
        (sumColMod_adj_ne h hbc) (sumColMod_adj_ne h hbd) (sumColMod_adj_ne_mid h hac) h15
        (sumColMod_adj_ne h hcd) (sumColMod_adj_ne_last h hab) (sumColMod_adj_ne_mid h had) h34
        (sumColMod_adj_ne_last h hac) (sumColMod_adj_ne_mid h hbd) ?_
      exact ⟨mem a b haS hbS hab, mem a c haS hcS hac, mem a d haS hdS had, mem b c hbS hcS hbc,
        mem c d hcS hdS hcd⟩
    · by_cases h3 : sumColMod m n h s(a, d) = sumColMod m n h s(b, c)
      · obtain ⟨h15', h24'⟩ := sumColMod_one_collision (b := d) (c := b) (d := c) hm h hac hab h3
        have h15 : sumColMod m n h s(a, b) ≠ sumColMod m n h s(c, d) := by
          simpa only [sumColMod_swap] using h15'
        have h24 : sumColMod m n h s(a, c) ≠ sumColMod m n h s(b, d) := by
          simpa only [sumColMod_swap] using h24'
        refine card_ge_five (sumColMod m n h s(a, b)) (sumColMod m n h s(a, c))
          (sumColMod m n h s(a, d)) (sumColMod m n h s(b, d)) (sumColMod m n h s(c, d))
          (sumColMod_adj_ne h hbc) (sumColMod_adj_ne h hbd) (sumColMod_adj_ne_mid h had) h15
          (sumColMod_adj_ne h hcd) h24 (sumColMod_adj_ne_mid h had)
          (sumColMod_adj_ne_last h hab) (sumColMod_adj_ne_last h hac) (sumColMod_adj_ne_last h hbc) ?_
        exact ⟨mem a b haS hbS hab, mem a c haS hcS hac, mem a d haS hdS had, mem b d hbS hdS hbd,
          mem c d hcS hdS hcd⟩
      · refine card_ge_five (sumColMod m n h s(a, b)) (sumColMod m n h s(a, c))
          (sumColMod m n h s(a, d)) (sumColMod m n h s(b, c)) (sumColMod m n h s(b, d))
          (sumColMod_adj_ne h hbc) (sumColMod_adj_ne h hbd) (sumColMod_adj_ne_mid h hac)
          (sumColMod_adj_ne_mid h had) (sumColMod_adj_ne h hcd) (sumColMod_adj_ne_last h hab)
          (fun hh => h2 hh) (fun hh => h3 hh) (sumColMod_adj_ne_last h hab)
          (sumColMod_adj_ne h hcd) ?_
        exact ⟨mem a b haS hbS hab, mem a c haS hcS hac, mem a d haS hdS had, mem b c hbS hcS hbc,
          mem b d hbS hdS hbd⟩

/-- **The round-robin colouring of `K_n` is admissible when `n` is odd.**  In other words: for
odd `n`, the classical round-robin colouring `c({a,b}) = a + b mod n` of `K_n` with `n` colours
has at least five colours in every `K₄`. -/
theorem admissible_sumCol (n : ℕ) (hn : n % 2 = 1) : Admissible (sumCol n) :=
  admissible_sumColMod hn (le_refl n)

/-! ### Consequences: the first linear upper bounds for `f(n, 4, 5)` -/

/-- **The linear upper bound for odd `n`.**  For odd `n`, the round-robin colouring is an
admissible `n`-colouring of `K_n`, so `f(n,4,5) ≤ n`. -/
theorem EG_le_sumCol (n : ℕ) (hn : n % 2 = 1) : EG n ≤ n :=
  EG_le n n (sumCol n) (admissible_sumCol n hn)

/-- **The linear upper bound in general.**  Every `n` admits an admissible colouring with `n + 1`
colours: use the sum colouring modulo `n + 1`, which is odd when `n` is even. -/
theorem EG_le_succ (n : ℕ) : EG n ≤ n + 1 := by
  by_cases hn : n % 2 = 1
  · have h1 := EG_le_sumCol n hn
    omega
  · have hm : (n + 1) % 2 = 1 := by omega
    have h2 : EG n ≤ n + 1 :=
      EG_le n (n + 1) (sumColMod (n + 1) n (Nat.le_succ n)) (admissible_sumColMod hm (Nat.le_succ n))
    exact h2

/-- `f(n,4,5) ≤ n` for odd `n` and `f(n,4,5) ≤ n + 1` in general: `f(n,4,5) = Θ(n)`. -/
theorem EG_le_linear (n : ℕ) : EG n ≤ n + 1 ∧ (n % 2 = 1 → EG n ≤ n) :=
  ⟨EG_le_succ n, fun hn => EG_le_sumCol n hn⟩

end JSP140
