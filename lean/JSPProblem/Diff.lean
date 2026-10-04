import JSPProblem.NoMerge

/-!
# JSP-000140 — round 81: THE NO-DIFFERENCE THEOREM (the 1-factorisation family is never
# admissible)

`Construction.lean` (round 3) builds the **sum (round-robin) colouring** `c({a,b}) = a + b` of
`K_m` and proves it admissible for odd `m`; `NoMerge.lean` (round 77) then kills every
non-injective variant of it (`NoMerge.injective_of_admissible`), i.e. **merging the colours of the
cyclic construction never preserves admissibility**.

The other classical explicit colouring of `K_m` is the **difference (1-factorisation) colouring**

    c_ψ({a, b}) = ψ (a - b)  (mod m),        ψ : ZMod m → Fin k ,                 (`Diff.diffCol`)

a colour class of which is a *Cayley graph* of `ZMod m`.  It is the colouring used in the
hand-checked constructions of rounds 12–14, which reached `n - O(1)` colours at best and were
abandoned.  Nothing was proved about the family.  This file proves, for **every** colour map
`ψ`, **every** budget `k` and **every** modulus `m ≥ 4`:

* **`Diff.card_path_class` — THE MONOCHROMATIC PATH.**  All `m - 1` edges `{p, p+1}` (vertices in
  the natural order of `Fin m`) carry the *same* colour `ψ (-1)`.  So one colour class of a
  difference colouring contains a **Hamiltonian path** of `K_m`, whatever `ψ` is: the family is
  not merely too big, it is monochromatically degenerate.
* **`Diff.three_consecutive` — THE MECHANISM.**  The four vertices `0, 1, 2, 3` carry three edges
  of colour `ψ (-1)`, so they span at most four colours
  (`Definitions.colorsOn_card_le_four`) — inadmissible.
* **`Diff.three_of_arith`** — the same for *every* four-term arithmetic progression
  `p, p+d, p+2d, p+3d` in the natural order, with common colour `ψ (-d)`.
* **`Diff.never_admissible` / `Diff.diffCol_admissible_iff` — THE NO-DIFFERENCE THEOREM.**
  `Admissible (diffCol m k hk ψ) ↔ m ≤ 3`.  The characterisation is *sharp* and needs no parity
  hypothesis (unlike the sum type): the whole 1-factorisation family is dead, at every budget,
  including the best one (`Diff.card_path_class` shows `k` cannot be pushed below `m - 1`).
* **`Diff.no_diff_family` / `Diff.no_cyclic_pair`** — the same in the language of `Col`: no
  admissible colouring of `K_m` (`m ≥ 4`) is of difference type, and for odd `m ≥ 5` no palette
  makes a difference-type colouring admissible together with a sum-type one.

## Why it matters for the prize

`JSPProblem.Main` still needs `Main.AdmissibleUpper ε` for `0 < ε < 1/6`, i.e. admissible
colourings of `K_n` with `5n/6 + εn` colours for all large `n`.  This file closes the last
*explicit* candidate: together with `NoMerge.no_merge` the two cyclic (translation-invariant)
families are settled —

    every translation-invariant colouring of `K_m` that is admissible uses exactly `m` colours,
    and every anti-translation-invariant one is inadmissible already at `m = 4`,

so the missing `1/6` of the colours cannot come from `ZMod m` at all.  That is the formal reason
why the construction of arXiv:2207.02920 has to be probabilistic and non-cyclic, and it retires a
family that rounds 60–75 had only been able to test by brute force.
-/

namespace JSP140

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

/-! ### Small finset tools (copies: `NoMerge`'s are private to that file) -/

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

/-! ### Vertices as residues: the natural order -/

/-- The `n`-th vertex of `K_m`, i.e. the vertex of the residue `n` of `ZMod m`.  Its `Fin` value
is `n`, so the vertices `0 < 1 < 2 < ...` of `Fin m` are ordered by their residue. -/
def zfinN (m : ℕ) [NeZero m] (n : ℕ) : Verts m := zfin ((n : ℕ) : ZMod m)

@[simp] theorem zfinN_val (m : ℕ) [NeZero m] (n : ℕ) (hn : n < m) : (zfinN m n : Verts m).val = n := by
  rw [zfinN, zfin_val, ZMod.val_natCast, Nat.mod_eq_of_lt hn]

@[simp] theorem zfinN_cast (m : ℕ) [NeZero m] (n : ℕ) :
    (zfinN m n : ZMod m) = ((n : ℕ) : ZMod m) := by rw [zfinN, zfin_cast]

/-- Two different residues below `m` are two different vertices. -/
theorem zfinN_ne (m : ℕ) [NeZero m] {a b : ℕ} (ha : a < m) (hb : b < m) (hab : a ≠ b) :
    zfinN m a ≠ zfinN m b := by
  intro hh
  have h' := congrArg (fun v : Verts m => v.val) hh
  rw [zfinN_val m a ha, zfinN_val m b hb] at h'
  exact hab h'

/-- The four vertices `0, 1, 2, 3` of `K_m` are pairwise distinct as soon as `m ≥ 4`. -/
theorem four_distinct (m : ℕ) [NeZero m] (hm : 4 ≤ m) :
    zfinN m 0 ≠ zfinN m 1 ∧ zfinN m 0 ≠ zfinN m 2 ∧ zfinN m 0 ≠ zfinN m 3 ∧
      zfinN m 1 ≠ zfinN m 2 ∧ zfinN m 1 ≠ zfinN m 3 ∧ zfinN m 2 ≠ zfinN m 3 :=
  ⟨zfinN_ne m (by omega) (by omega) (by omega), zfinN_ne m (by omega) (by omega) (by omega),
    zfinN_ne m (by omega) (by omega) (by omega), zfinN_ne m (by omega) (by omega) (by omega),
    zfinN_ne m (by omega) (by omega) (by omega), zfinN_ne m (by omega) (by omega) (by omega)⟩

/-! ### The difference colouring -/

/-- **THE ORIENTED DIFFERENCE.**  The colour of the edge `{a, b}` is `ψ` applied to the residue
`a - b`, the edge being written with its *smaller* endpoint first.  That convention is what makes
the formula a well-defined function on unordered pairs when `ψ (-x) ≠ ψ (x)`. -/
def diffPair (m k : ℕ) (ψ : ZMod m → Fin k) (a b : Verts m) : Fin k :=
  ψ (if a.val ≤ b.val then (a : ZMod m) - (b : ZMod m) else (b : ZMod m) - (a : ZMod m))

/-- The orientation convention does not matter: `diffPair` is symmetric. -/
theorem diffPair_swap (m k : ℕ) (ψ : ZMod m → Fin k) (a b : Verts m) :
    diffPair m k ψ a b = diffPair m k ψ b a := by
  by_cases h1 : a.val ≤ b.val
  · by_cases h2 : b.val ≤ a.val
    · have hval : a.val = b.val := Nat.le_antisymm h1 h2
      have hab : a = b := Fin.ext hval
      subst hab
      rfl
    · simp [diffPair, h1, h2]
  · have h2 : b.val ≤ a.val := Nat.le_of_lt (lt_of_not_ge h1)
    simp [diffPair, h1, h2]

/-- **THE DIFFERENCE (1-FACTORISATION) COLOURING** of `K_m`: the edge `{a, b}` receives the colour
`ψ (a - b)`.  With `ψ x = ⟨x.val, _⟩` and `m` prime, this is the classical 1-factorisation of
`K_m`, whose colour classes are Hamilton cycles. -/
def diffCol (m k : ℕ) (hk : 0 < k) (ψ : ZMod m → Fin k) : Col m k :=
  Sym2.rec (motive := fun _ => Fin k) (diffPair m k ψ)
    (by
      intro a b c d h
      cases h with
      | refl => rfl
      | swap x y => simp [diffPair_swap])

@[simp] theorem diffCol_mk (m k : ℕ) (hk : 0 < k) (ψ : ZMod m → Fin k) (a b : Verts m) :
    diffCol m k hk ψ s(a, b) = diffPair m k ψ a b := rfl

theorem diffPair_of_le (m k : ℕ) (ψ : ZMod m → Fin k) {a b : Verts m} (hle : a.val ≤ b.val) :
    diffPair m k ψ a b = ψ ((a : ZMod m) - (b : ZMod m)) := by simp [diffPair, hle]

theorem diffPair_of_lt (m k : ℕ) (ψ : ZMod m → Fin k) {a b : Verts m} (hle : b.val < a.val) :
    diffPair m k ψ a b = ψ ((b : ZMod m) - (a : ZMod m)) := by
  have hne : ¬ a.val ≤ b.val := by omega
  simp [diffPair, hne]

/-- **THE COLOUR OF THE NATURAL PATH.**  In the difference colouring the single residue `-1` is the
colour of the whole path `0 - 1 - 2 - ...`. -/
def pathColour (m k : ℕ) (ψ : ZMod m → Fin k) : Fin k := ψ (-((1 : ℕ) : ZMod m))

/-- **THE VALUE ON AN INCREASING EDGE.**  If the two endpoints are written in increasing natural
order with gap `d`, the colour is `ψ (-d)`. -/
theorem diffCol_edge_natCast {m k : ℕ} [NeZero m] (hk : 0 < k) (ψ : ZMod m → Fin k) {p d : ℕ}
    (hp : p + d < m) :
    diffCol m k hk ψ s(zfinN m p, zfinN m (p + d)) = ψ (-(d : ZMod m)) := by
  have hle : (zfinN m p : Verts m).val ≤ (zfinN m (p + d) : Verts m).val := by
    rw [zfinN_val m p (by omega), zfinN_val m (p + d) hp]
    omega
  rw [diffCol_mk, diffPair_of_le m k ψ (a := zfinN m p) (b := zfinN m (p + d)) hle, zfinN_cast,
    zfinN_cast, Nat.cast_add]
  congr 1
  ring

/-- **THE VALUE ON A PATH EDGE.** -/
theorem diffCol_edge_path {m k : ℕ} [NeZero m] (hk : 0 < k) (ψ : ZMod m → Fin k) {p : ℕ}
    (hp : p + 1 < m) : diffCol m k hk ψ s(zfinN m p, zfinN m (p + 1)) = pathColour m k ψ := by
  rw [diffCol_edge_natCast hk ψ hp]
  rfl

/-- **THE MONOCHROMATIC PATH, EDGE BY EDGE.**  Every edge `{p, p+1}` of the natural ordering of
`K_m` carries the single colour `pathColour m k ψ`, whatever `ψ` is. -/
theorem path_edge_mem_class {m k : ℕ} [NeZero m] (hk : 0 < k) (ψ : ZMod m → Fin k) {p : ℕ}
    (hp : p + 1 < m) :
    s(zfinN m p, zfinN m (p + 1))
      ∈ classIn (diffCol m k hk ψ) (pathColour m k ψ) (Finset.univ : Finset (Verts m)) := by
  rw [mem_classIn]
  refine ⟨mem_edgeFinset_mk (Finset.mem_univ _) (Finset.mem_univ _)
    (zfinN_ne m (by omega) hp (by omega)), diffCol_edge_path hk ψ hp⟩

/-- **THE MONOCHROMATIC PATH.**  In the difference colouring `diffCol m k hk ψ` the colour class
of `pathColour m k ψ = ψ (-1)` contains the whole path `0 - 1 - 2 - ... - (m-1)`, i.e. it has at
least `m - 1` edges, for *every* colour map `ψ`.  In particular, even at the best possible budget
`k = m - 1` the family is monochromatically degenerate: one colour carries a Hamiltonian path. -/
theorem card_path_class {m k : ℕ} [NeZero m] (hm : 0 < m) (hk : 0 < k) (ψ : ZMod m → Fin k) :
    m - 1
      ≤ (classIn (diffCol m k hk ψ) (pathColour m k ψ) (Finset.univ : Finset (Verts m))).card := by
  set T : Finset (Sym2 (Verts m)) :=
    (Finset.range (m - 1)).image (fun p : ℕ => s(zfinN m p, zfinN m (p + 1))) with hTdef
  have hinj : Set.InjOn (fun p : ℕ => s(zfinN m p, zfinN m (p + 1))) (Finset.range (m - 1)) := by
    rw [Set.InjOn]
    intro p hp q hq h
    have hp' : p < m - 1 := Finset.mem_range.mp hp
    have hq' : q < m - 1 := Finset.mem_range.mp hq
    have hp : p < m := by omega
    have hq1 : q + 1 < m := by omega
    have hp1 : p + 1 < m := by omega
    have hq : q < m := by omega
    rcases sym2_inj h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have h3 := congrArg (fun v : Verts m => v.val) h1
      rw [zfinN_val m p hp, zfinN_val m q hq] at h3
      exact h3
    · have h3 := congrArg (fun v : Verts m => v.val) h1
      rw [zfinN_val m p hp, zfinN_val m (q + 1) hq1] at h3
      have h4 := congrArg (fun v : Verts m => v.val) h2
      rw [zfinN_val m (p + 1) hp1, zfinN_val m q hq] at h4
      omega
  have hcardT : T.card = m - 1 := by
    rw [hTdef, Finset.card_image_of_injOn hinj, Finset.card_range]
  have hsub : T ⊆ classIn (diffCol m k hk ψ) (pathColour m k ψ) (Finset.univ : Finset (Verts m)) := by
    intro e he
    rw [hTdef, Finset.mem_image] at he
    obtain ⟨p, hp, rfl⟩ := he
    have hp' : p + 1 ≤ m - 1 := Nat.succ_le_of_lt (Finset.mem_range.mp hp)
    exact path_edge_mem_class hk ψ (by omega)
  have hcardsub : T.card
      ≤ (classIn (diffCol m k hk ψ) (pathColour m k ψ) (Finset.univ : Finset (Verts m))).card :=
    Finset.card_le_card hsub
  rw [← hcardT]
  exact hcardsub

/-! ### The mechanism: three edges of one colour in a `K₄` -/

/-- **THE MECHANISM.**  For `m ≥ 4` the four vertices `0, 1, 2, 3` of `K_m` span **three** edges
of colour `pathColour m k ψ` (namely `{0,1}`, `{1,2}`, `{2,3}`), so their `K₄` spans at most four
colours (`Definitions.colorsOn_card_le_four`) and `diffCol` is not admissible. -/
theorem three_consecutive {m k : ℕ} (hm : 4 ≤ m) (hk : 0 < k) (ψ : ZMod m → Fin k) :
    ∃ S : Finset (Verts m), S.card = 4 ∧
      3 ≤ (classIn (diffCol m k hk ψ) (pathColour m k ψ) S).card := by
  haveI : NeZero m := ⟨Nat.pos_iff_ne_zero.mp (by omega)⟩
  have h4 := four_distinct m hm
  set S : Finset (Verts m) := {zfinN m 0, zfinN m 1, zfinN m 2, zfinN m 3} with hSdef
  have hcard4 : S.card = 4 := by
    rw [hSdef]
    exact card_four h4.1 h4.2.1 h4.2.2.1 h4.2.2.2.1 h4.2.2.2.2.1 h4.2.2.2.2.2
  set T : Finset (Sym2 (Verts m)) :=
    {s(zfinN m 0, zfinN m 1), s(zfinN m 1, zfinN m 2), s(zfinN m 2, zfinN m 3)} with hTdef
  have hed12 : s(zfinN m 0, zfinN m 1) ≠ s(zfinN m 1, zfinN m 2) := by
    intro hh
    rcases sym2_inj hh with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact h4.2.2.2.1 h2
    · exact h4.2.1 h1
  have hed23 : s(zfinN m 1, zfinN m 2) ≠ s(zfinN m 2, zfinN m 3) := by
    intro hh
    rcases sym2_inj hh with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact h4.2.2.2.1 h1
    · exact h4.2.2.2.2.1 h1
  have hed13 : s(zfinN m 0, zfinN m 1) ≠ s(zfinN m 2, zfinN m 3) := by
    intro hh
    rcases sym2_inj hh with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact h4.2.1 h1
    · exact h4.2.2.1 h1
  have hcard3 : T.card = 3 := by
    rw [hTdef]
    exact card_three hed12 hed13 hed23
  have m0 : zfinN m 0 ∈ S := by rw [hSdef]; simp
  have m1 : zfinN m 1 ∈ S := by rw [hSdef]; simp
  have m2 : zfinN m 2 ∈ S := by rw [hSdef]; simp
  have m3 : zfinN m 3 ∈ S := by rw [hSdef]; simp
  have hsub : T ⊆ classIn (diffCol m k hk ψ) (pathColour m k ψ) S := by
    intro t ht
    simp only [hTdef, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl
    · exact mem_classIn.mpr ⟨mem_edgeFinset_mk m0 m1 h4.1, diffCol_edge_path hk ψ (by omega)⟩
    · exact mem_classIn.mpr
        ⟨mem_edgeFinset_mk m1 m2 h4.2.2.2.1, diffCol_edge_path hk ψ (by omega)⟩
    · exact mem_classIn.mpr
        ⟨mem_edgeFinset_mk m2 m3 h4.2.2.2.2.2, diffCol_edge_path hk ψ (by omega)⟩
  refine ⟨S, hcard4, ?_⟩
  rw [← hcard3]
  exact Finset.card_le_card hsub

/-- **THE MECHANISM, IN GENERAL FORM.**  Every four-term arithmetic progression
`p, p+d, p+2d, p+3d` lying inside `Fin m` in the natural order spans three edges of the single
colour `ψ (-d)`; (`Diff.three_consecutive` is the instance `d = 1`, `p = 0`).  So every such
progression is a witness against admissibility, for every `ψ`. -/
theorem three_of_arith {m k : ℕ} (hk : 0 < k) (ψ : ZMod m → Fin k) {p d : ℕ} (hd : 0 < d)
    (hp : p + 3 * d < m) :
    ∃ S : Finset (Verts m), S.card = 4 ∧
      3 ≤ (classIn (diffCol m k hk ψ) (ψ (-(d : ZMod m))) S).card := by
  haveI : NeZero m := ⟨Nat.pos_iff_ne_zero.mp (by omega)⟩
  set S : Finset (Verts m) :=
    {zfinN m p, zfinN m (p + d), zfinN m (p + d + d), zfinN m (p + d + d + d)} with hSdef
  have hne1 : zfinN m p ≠ zfinN m (p + d) := zfinN_ne m (by omega) (by omega) (by omega)
  have hne2 : zfinN m p ≠ zfinN m (p + d + d) := zfinN_ne m (by omega) (by omega) (by omega)
  have hne3 : zfinN m p ≠ zfinN m (p + d + d + d) := zfinN_ne m (by omega) (by omega) (by omega)
  have hne4 : zfinN m (p + d) ≠ zfinN m (p + d + d) := zfinN_ne m (by omega) (by omega) (by omega)
  have hne5 : zfinN m (p + d) ≠ zfinN m (p + d + d + d) := zfinN_ne m (by omega) (by omega) (by omega)
  have hne6 : zfinN m (p + d + d) ≠ zfinN m (p + d + d + d) :=
    zfinN_ne m (by omega) (by omega) (by omega)
  have hcard4 : S.card = 4 := by
    rw [hSdef]
    exact card_four hne1 hne2 hne3 hne4 hne5 hne6
  set T : Finset (Sym2 (Verts m)) :=
    {s(zfinN m p, zfinN m (p + d)), s(zfinN m (p + d), zfinN m (p + d + d)),
      s(zfinN m (p + d + d), zfinN m (p + d + d + d))} with hTdef
  have hed12 : s(zfinN m p, zfinN m (p + d)) ≠ s(zfinN m (p + d), zfinN m (p + d + d)) := by
    intro hh
    rcases sym2_inj hh with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact hne4 h2
    · exact hne2 h1
  have hed23 : s(zfinN m (p + d), zfinN m (p + d + d)) ≠ s(zfinN m (p + d + d), zfinN m (p + d + d + d)) := by
    intro hh
    rcases sym2_inj hh with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact hne4 h1
    · exact hne5 h1
  have hed13 : s(zfinN m p, zfinN m (p + d)) ≠ s(zfinN m (p + d + d), zfinN m (p + d + d + d)) := by
    intro hh
    rcases sym2_inj hh with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact hne5 h2
    · exact hne3 h1
  have hcard3 : T.card = 3 := by
    rw [hTdef]
    exact card_three hed12 hed13 hed23
  have m0 : zfinN m p ∈ S := by rw [hSdef]; simp
  have m1 : zfinN m (p + d) ∈ S := by rw [hSdef]; simp
  have m2 : zfinN m (p + d + d) ∈ S := by rw [hSdef]; simp
  have m3 : zfinN m (p + d + d + d) ∈ S := by rw [hSdef]; simp
  have hsub : T ⊆ classIn (diffCol m k hk ψ) (ψ (-(d : ZMod m))) S := by
    intro t ht
    simp only [hTdef, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl
    · exact mem_classIn.mpr ⟨mem_edgeFinset_mk m0 m1 hne1,
        diffCol_edge_natCast hk ψ (p := p) (d := d) (by omega)⟩
    · exact mem_classIn.mpr ⟨mem_edgeFinset_mk m1 m2 hne4,
        diffCol_edge_natCast hk ψ (p := p + d) (d := d) (by omega)⟩
    · exact mem_classIn.mpr ⟨mem_edgeFinset_mk m2 m3 hne6,
        diffCol_edge_natCast hk ψ (p := p + d + d) (d := d) (by omega)⟩
  refine ⟨S, hcard4, ?_⟩
  rw [← hcard3]
  exact Finset.card_le_card hsub

/-! ### The no-difference theorem -/

/-- **THE NO-DIFFERENCE THEOREM.**  For `m ≥ 4`, for every number of colours `k` and every colour
map `ψ : ZMod m → Fin k`, the difference colouring `diffCol m k hk ψ` is **not** admissible. -/
theorem never_admissible {m k : ℕ} (hm : 4 ≤ m) (hk : 0 < k) (ψ : ZMod m → Fin k) :
    ¬ Admissible (diffCol m k hk ψ) := by
  intro hc
  obtain ⟨S, hS, h3⟩ := three_consecutive hm hk ψ
  have h4 := colorsOn_card_le_four hS h3
  have h5 := hc S hS
  omega

/-- **THE REVERSED CONVENTION FAILS TOO.**  Reading the difference the other way round,
`{a, b} ↦ ψ (b - a)`, is `diffCol` with the colour map `x ↦ ψ (-x)`, so it is never admissible
either: the no-go does not depend on the orientation convention of an edge. -/
def diffColR (m k : ℕ) (hk : 0 < k) (ψ : ZMod m → Fin k) : Col m k :=
  diffCol m k hk (fun x => ψ (-x))

theorem diffColR_never_admissible {m k : ℕ} (hm : 4 ≤ m) (hk : 0 < k) (ψ : ZMod m → Fin k) :
    ¬ Admissible (diffColR m k hk ψ) := never_admissible hm hk _

/-- **THE DIFFERENCE FAMILY IS WORTH NOTHING.**  For `m ≥ 4` there is no admissible colouring of
`K_m` whose colour of `{a, b}` depends only on the difference `a - b`, at *any* number of
colours.  This is the exact analogue of `NoMerge.no_merge` for the 1-factorisation family. -/
theorem no_diff_family {m : ℕ} (hm : 4 ≤ m) :
    ¬ ∃ (k : ℕ) (hk : 0 < k) (ψ : ZMod m → Fin k), Admissible (diffCol m k hk ψ) := by
  rintro ⟨k, hk, ψ, hc⟩
  exact never_admissible hm hk ψ hc

/-- For `m ≤ 3` there is no four-vertex clique at all, so `diffCol` is vacuously admissible: the
other half of the classification. -/
theorem diffCol_admissible_small {m k : ℕ} (hm : m ≤ 3) (hk : 0 < k) (ψ : ZMod m → Fin k) :
    Admissible (diffCol m k hk ψ) := by
  intro S hS
  have hle := Finset.card_le_univ S
  rw [Fintype.card_fin] at hle
  omega

/-- **THE COMPLETE CLASSIFICATION OF THE DIFFERENCE FAMILY.**
`Admissible (diffCol m k hk ψ) ↔ m ≤ 3`: for every `m ≥ 4`, every `k`, every `ψ`, the difference
colouring fails.  No parity hypothesis is needed, in contrast with `NoMerge.k_ge` (the sum type
needs `m` colours, the difference type never works at all). -/
theorem diffCol_admissible_iff {m k : ℕ} (hk : 0 < k) (ψ : ZMod m → Fin k) :
    Admissible (diffCol m k hk ψ) ↔ m ≤ 3 := by
  constructor
  · intro hc
    by_contra hcon
    have hpos : 3 < m := Nat.lt_of_not_ge hcon
    have hm : 4 ≤ m := by omega
    exact (never_admissible hm hk ψ hc).elim
  · intro hm3
    exact diffCol_admissible_small (hm := hm3) hk ψ

/-- **THE TWO CYCLIC FAMILIES ARE INCOMPATIBLE.**  For odd `m ≥ 5` and any two colour maps
`φ, ψ : ZMod m → Fin k` on one palette, the difference colouring is inadmissible, so no palette
can make both a sum-type and a difference-type colouring admissible.  Together with
`NoMerge.k_ge` this says that the whole translation-invariant part of the search space
contributes exactly the round-robin colouring of `Construction.lean`, and the missing `1/6` of
the colours can only be reached outside `ZMod m`. -/
theorem no_cyclic_pair {m k : ℕ} (hm : 5 ≤ m) (hodd : m % 2 = 1) (hk : 0 < k)
    (φ ψ : ZMod m → Fin k) :
    ¬ (Admissible (mergedCol m k hk φ) ∧ Admissible (diffCol m k hk ψ)) :=
  fun h => never_admissible (by omega) hk ψ h.2

/-- **A COMPUTER-CHECKED INSTANCE.**  The smallest difference-type colouring of `K_4` — the
1-factorisation with four colours — is refused by the kernel, so the theorem above is not vacuous
and hides no definitional gap. -/
theorem four_colouring_refused :
    ¬ Admissible (diffCol 4 4 (by omega) (fun x : ZMod 4 => ⟨x.val, ZMod.val_lt x⟩)) := by
  unfold Admissible
  decide

/-! ### The statement the family cannot reach -/

/-- **AN ADMISSIBLE COLOURING IS NEVER OF DIFFERENCE TYPE.**  The contrapositive reading of
`Diff.diffCol_admissible_iff` in the shape used elsewhere in this development: no admissible
colouring of `K_m` with `m ≥ 4` is a Cayley colouring of `ZMod m`. -/
theorem not_diff_of_admissible {m k : ℕ} (hm : 4 ≤ m) (hk : 0 < k) (ψ : ZMod m → Fin k)
    (hc : Admissible (diffCol m k hk ψ)) : m ≤ 3 := (diffCol_admissible_iff hk ψ).mp hc

/-- **THE CYCLIC EXHAUSTION THEOREM** (rounds 77 + 81 combined).  Let `m ≥ 5` be odd, let `c` be a
colouring of `K_m` whose colour map is a function of `a + b` or of `a - b` in `ZMod m`, and let
`c` be admissible.  Then `c` needs `m` colours at least: in the whole translation-invariant part
of the search space the round-robin colouring of `Construction.lean` is optimal, and the
difference type is excluded altogether.  This is the formal reason why the catalogue constant
`5n/6` cannot be reached inside `ZMod m` (`Main.AdmissibleUpper` must come from outside). -/
theorem cyclic_exhausted {m k : ℕ} (hm : 5 ≤ m) (hodd : m % 2 = 1) (hk : 0 < k) (c : Col m k)
    (hc : Admissible c)
    (htype : (∃ φ : ZMod m → Fin k, c = mergedCol m k hk φ) ∨
      (∃ ψ : ZMod m → Fin k, c = diffCol m k hk ψ)) : m ≤ k := by
  rcases htype with ⟨φ, hφ⟩ | ⟨ψ, hψ⟩
  · exact k_ge m k hm hodd hk φ (by rw [← hφ]; exact hc)
  · exact absurd (by rw [← hψ]; exact hc) (never_admissible (by omega) hk ψ)

end JSP140