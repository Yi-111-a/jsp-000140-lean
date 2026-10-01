import JSPProblem.FastSearch

/-!
# The vertex-addition search — `JSP-000140`

The search of `FastSearch.lean` fills the *slots* `a * n + b` of `K_n` in the order
`a = 0, 1, …, n-1`, i.e. **all the edges at vertex `0` first, then all the edges at vertex `1`,
and so on**.  With that order the first `K₄` — and hence the first pruning test — only happens
after `n-1` edges have been coloured, so the search is extremely weak.

`VertexSearch.lean` replaces the slot numbering by the **vertex-addition numbering**: the edges
are enumerated by their *larger* endpoint,

    (0,1), (0,2), (1,2), (0,3), (1,3), (2,3), (0,4), … , (n-2,n-1),

so the position of the edge `{a,b}` (`a < b`) is `tri b + a` with `tri b = C(b,2)`.  Under this
order the first `K₄` is completed after **six** edges, the first four `K₄`s after **ten**, and so
on: every clique is tested as early as it possibly can be.  Measured on `K₇` with six colours
(`discovery/JSP-000140/`), the number of search nodes of

* "is there an admissible six-colouring of `K₇`?" drops from **13 301 689** to **38 654**,

a factor of 344, which brings the whole certificate within reach of `native_decide`.

Main contents.

* `tri`, `nEdgeC`, `slotC`, `slotOfC` — the vertex-addition numbering, with `tri_succ`,
  `tri_mono`, `slotC_inj`, `slotOfC_inj` (the numbering is a bijection onto `[0, C(n,2))`);
* `quadSlotsC`, `slotQuadC`, `quadOKC`, `allOKC`, `quadOKC_of`, `quadGroupsC` — the pruning test
  and the group table, in the new numbering;
* `searchAuxC`, **`searchAuxC_iff` — THE COMPLETENESS THEOREM**, `hasAdmissibleC`,
  `hasAdmissibleC_iff`, `EG_ge_of_certC` — the search and its lower-bound engine.

`searchAuxC_iff` is the same theorem as `FastSearch.searchAuxSg_iff`, with two simplifications
that come for free with the dense numbering: there is no "slot carrying no edge" to skip (every
position `d < C(n,2)` carries exactly one edge), and the `K₄` which a position completes is
determined by the position alone.
-/

namespace JSP140

private theorem update_of_ne' {k : ℕ} {M : PTab k} {d s : ℕ} (hs : s ≠ d) (j : Fin k) :
    Function.update M d (some j) s = M s := Function.update_of_ne hs (some j) M

private theorem update_eq_self' {k : ℕ} {M : PTab k} {d : ℕ} {j : Fin k} :
    Function.update M d (some j) d = some j := by simp [Function.update]

/-! ### `tri b = C(b,2)`, the number of edges of `K_b` -/

/-- `tri b = C(b,2)`, the number of edges of `K_b`. -/
def tri (b : ℕ) : ℕ := b * (b - 1) / 2

/-- The number of edges of `K_n`, i.e. the number of vertex-addition slots. -/
def nEdgeC (n : ℕ) : ℕ := tri n

private theorem div_two_add (A B : ℕ) : A / 2 + B = (A + 2 * B) / 2 := by
  have h1 := Nat.div_add_mod A 2
  have h2 := Nat.div_add_mod (A + 2 * B) 2
  omega

/-- **`tri` advances by `b`**: `tri (b+1) = tri b + b`. -/
theorem tri_succ (b : ℕ) : tri b + b = tri (b + 1) := by
  rcases b with _ | m
  · rfl
  · simp only [tri, Nat.succ_sub_one]
    have h1 : (m + 1) * m + 2 * (m + 1) = (m + 1) * (m + 2) := by
      calc (m + 1) * m + 2 * (m + 1) = (m + 1) * m + (m + 1) * 2 := by
            simp [Nat.mul_comm]
        _ = (m + 1) * (m + 2) := (Nat.mul_add (m + 1) m 2).symm
    have h2 := div_two_add ((m + 1) * m) (m + 1)
    rw [h1] at h2
    simpa [Nat.mul_comm] using h2

/-- **`tri` is non-decreasing.** -/
theorem tri_mono {b c : ℕ} (h : b ≤ c) : tri b ≤ tri c := by
  have hb1 : b - 1 ≤ c - 1 := by omega
  have h1 : b * (b - 1) ≤ c * (c - 1) :=
    (Nat.mul_le_mul_left b hb1).trans (Nat.mul_le_mul_right (c - 1) h)
  unfold tri
  exact Nat.div_le_div_right h1

/-- **The vertex-addition position determines the larger endpoint.** -/
theorem lt_n_of_tri_lt {b n : ℕ} (h : tri b < tri n) : b < n := by
  by_contra hc
  have h2 : n ≤ b := Nat.le_of_not_gt hc
  have h3 : tri n ≤ tri b := tri_mono h2
  omega

/-! ### The vertex-addition slot of an edge -/

/-- **The vertex-addition slot of the pair `a < b`**: the edges are enumerated by their larger
endpoint, so `{a,b}` occupies the position `tri b + a`. -/
def slotC (a b : ℕ) : ℕ := tri b + a

/-- The vertex-addition slot of a pair of vertices. -/
def slotCPair (n : ℕ) (a b : Verts n) : ℕ := slotC (min a b).val (max a b).val

theorem slotCPair_swap (n : ℕ) (a b : Verts n) : slotCPair n a b = slotCPair n b a := by
  simp only [slotCPair, min_comm, max_comm]

/-- **The vertex-addition slot of an edge.** -/
def slotOfC : Sym2 (Verts n) → ℕ :=
  Sym2.rec (motive := fun _ => ℕ) (fun a b => slotCPair n a b)
    (by
      intro a b c d h
      cases h with
      | refl => rfl
      | swap x y => simp [slotCPair, min_comm, max_comm])

@[simp] theorem slotCPair_mk (a b : Verts n) : slotCPair n a b = slotOfC s(a, b) := rfl

@[simp] theorem slotOfC_mk (a b : Verts n) : slotOfC s(a, b) = slotCPair n a b := rfl

theorem slotCPair_of_lt {n : ℕ} {a b : Verts n} (h : a < b) :
    slotCPair n a b = slotC a.val b.val := by
  simp only [slotCPair, min_eq_left h.le, max_eq_right h.le]

/-- **Distinct edges occupy distinct slots.** -/
theorem slotC_inj {a b a' b' : ℕ} (h1 : a < b) (h2 : a' < b') (h : slotC a b = slotC a' b') :
    a = a' ∧ b = b' := by
  have e1 : tri b ≤ slotC a' b' := by rw [← h, slotC]; omega
  have e1b : tri b' ≤ slotC a' b' := by rw [slotC]; omega
  have e2 : slotC a b < tri (b + 1) := by
    have hlt : slotC a b < tri b + b := by
      rw [slotC]; exact (Nat.add_lt_add_left h1) (tri b)
    rw [slotC, tri_succ] at hlt
    exact hlt
  have e3 : slotC a' b' < tri (b' + 1) := by
    have hlt : slotC a' b' < tri b' + b' := by
      rw [slotC]; exact (Nat.add_lt_add_left h2) (tri b')
    rw [slotC, tri_succ] at hlt
    exact hlt
  rcases Nat.lt_trichotomy b b' with hb | hb | hb
  · exfalso
    have hlt : tri (b + 1) ≤ tri b' := tri_mono (by omega)
    rw [h] at e2
    omega
  · subst hb
    refine ⟨by unfold slotC at h; omega, rfl⟩
  · exfalso
    have hlt : tri (b' + 1) ≤ tri b := tri_mono (by omega)
    omega

/-- **Every edge lives in a slot below `C(n,2)`.** -/
theorem slotCPair_lt {n : ℕ} {a b : Verts n} (h : a ≠ b) : slotCPair n a b < nEdgeC n := by
  unfold nEdgeC
  rcases lt_trichotomy a b with hlt | hlt | hlt
  · rw [slotCPair_of_lt hlt]
    have h3 : slotC a.val b.val < tri (b.val + 1) := by
      have hlt' : slotC a.val b.val < tri b.val + b.val := by
        rw [slotC]; exact (Nat.add_lt_add_left hlt) _
      rwa [slotC, tri_succ] at hlt'
    have h4 : tri (b.val + 1) ≤ tri n := tri_mono (by omega)
    omega
  · exact (h hlt).elim
  · rw [slotCPair_swap n a b, slotCPair_of_lt hlt]
    have h3 : slotC b.val a.val < tri (a.val + 1) := by
      have hlt' : slotC b.val a.val < tri a.val + a.val := by
        rw [slotC]; exact (Nat.add_lt_add_left hlt) _
      rwa [slotC, tri_succ] at hlt'
    have h4 : tri (a.val + 1) ≤ tri n := tri_mono (by omega)
    omega

/-- **Every edge lives in a slot below `C(n,2)`. -/
theorem slotOfC_lt {n : ℕ} {e : Sym2 (Verts n)} (he : OffDiag e) : slotOfC e < nEdgeC n := by
  obtain ⟨a, b, rfl⟩ := Sym2.exists.mp ⟨e, rfl⟩
  exact slotCPair_lt (offDiag_iff.mp he)

/-- **An edge is determined by its vertex-addition slot.** -/
theorem slotOfC_eq_slotC_iff {n : ℕ} {e : Sym2 (Verts n)} {a b : Verts n}
    (he : OffDiag e) (h : a < b) :
    slotOfC e = slotC a.val b.val ↔ e = s(a, b) := by
  constructor
  · intro hF
    obtain ⟨x, y, rfl⟩ := Sym2.exists.mp ⟨e, rfl⟩
    have hxy : x ≠ y := offDiag_iff.mp he
    have hbase : slotCPair n x y = slotC a.val b.val := (slotOfC_mk x y).symm.trans hF
    rcases lt_trichotomy x y with h1 | h1 | h1
    · obtain ⟨hh1, hh2⟩ := slotC_inj (a := x.val) (b := y.val) (a' := a.val) (b' := b.val)
        (by exact Fin.lt_iff_val_lt_val.mp h1) (by exact Fin.lt_iff_val_lt_val.mp h)
        ((slotCPair_of_lt h1).symm.trans hbase)
      rw [show x = a from Fin.ext hh1, show y = b from Fin.ext hh2]
    · exact (hxy h1).elim
    · obtain ⟨hh1, hh2⟩ := slotC_inj (a := y.val) (b := x.val) (a' := a.val) (b' := b.val)
        (by exact Fin.lt_iff_val_lt_val.mp h1) (by exact Fin.lt_iff_val_lt_val.mp h)
        ((slotCPair_of_lt h1).symm.trans (slotCPair_swap n x y).symm |>.trans hbase)
      rw [show x = b from Fin.ext hh2, show y = a from Fin.ext hh1, sym2_swap]
  · intro hf
    subst hf
    rw [slotOfC_mk, slotCPair_of_lt h]

/-- **Distinct edges occupy distinct slots.** -/
theorem slotOfC_inj {n : ℕ} {e e' : Sym2 (Verts n)} (he : OffDiag e) (he' : OffDiag e')
    (h : slotOfC e = slotOfC e') : e = e' := by
  obtain ⟨a, b, rfl⟩ := Sym2.exists.mp ⟨e, rfl⟩
  obtain ⟨a', b', rfl⟩ := Sym2.exists.mp ⟨e', rfl⟩
  have hab : a ≠ b := offDiag_iff.mp he
  have ha'b' : a' ≠ b' := offDiag_iff.mp he'
  have hbase : slotCPair n a b = slotCPair n a' b' := h
  rcases lt_trichotomy a b with h1 | h1 | h1
  · rcases lt_trichotomy a' b' with h2 | h2 | h2
    · obtain ⟨hh1, hh2⟩ := slotC_inj (a := a.val) (b := b.val) (a' := a'.val) (b' := b'.val)
        (by exact Fin.lt_iff_val_lt_val.mp h1) (by exact Fin.lt_iff_val_lt_val.mp h2)
        ((slotCPair_of_lt h1).symm.trans (hbase.trans (slotCPair_of_lt h2)))
      rw [show a = a' from Fin.ext hh1, show b = b' from Fin.ext hh2]
    · exact (ha'b' h2).elim
    · obtain ⟨hh1, hh2⟩ := slotC_inj (a := a.val) (b := b.val) (a' := b'.val) (b' := a'.val)
        (by exact Fin.lt_iff_val_lt_val.mp h1) (by exact Fin.lt_iff_val_lt_val.mp h2)
        ((slotCPair_of_lt h1).symm.trans
          (hbase.trans ((slotCPair_swap n a' b').trans (slotCPair_of_lt h2))))
      rw [show a = b' from Fin.ext hh1, show b = a' from Fin.ext hh2, sym2_swap]
  · exact (hab h1).elim
  · rcases lt_trichotomy a' b' with h2 | h2 | h2
    · obtain ⟨hh1, hh2⟩ := slotC_inj (a := b.val) (b := a.val) (a' := a'.val) (b' := b'.val)
        (by exact Fin.lt_iff_val_lt_val.mp h1) (by exact Fin.lt_iff_val_lt_val.mp h2)
        (((slotCPair_of_lt h1).symm.trans (slotCPair_swap n a b).symm).trans
          (hbase.trans (slotCPair_of_lt h2)))
      rw [show b = a' from Fin.ext hh1, show a = b' from Fin.ext hh2, sym2_swap]
    · exact (ha'b' h2).elim
    · obtain ⟨hh1, hh2⟩ := slotC_inj (a := b.val) (b := a.val) (a' := b'.val) (b' := a'.val)
        (by exact Fin.lt_iff_val_lt_val.mp h1) (by exact Fin.lt_iff_val_lt_val.mp h2)
        (((slotCPair_of_lt h1).symm.trans (slotCPair_swap n a b).symm).trans
          (hbase.trans ((slotCPair_swap n a' b').trans (slotCPair_of_lt h2))))
      rw [show b = b' from Fin.ext hh1, show a = a' from Fin.ext hh2]

/-! ### The position of the search -/

/-- **The current position of the vertex-addition search**, in the state `(b, a)`: the edges
`{0,b}, …, {b-1,b}` occupy `tri b, …, tri b + b - 1`, so the next position is
`tri b + min a b`.  For `a ≥ b` (the state after the last edge at vertex `b` has been coloured)
this is `tri b + b = tri (b+1)`, the first position of the next vertex. -/
def posC (b a : ℕ) : ℕ := tri b + min a b

theorem posC_eq_slotC {b a : ℕ} (h : a < b) : posC b a = slotC a b := by
  simp only [posC, min_eq_left h.le, slotC]

theorem posC_succ {b a : ℕ} (h : a < b) : posC b (a + 1) = posC b a + 1 := by
  have key : min (a + 1) b = min a b + 1 := by
    by_cases h2 : a + 1 ≤ b
    · rw [min_eq_left h2, min_eq_left h.le]
    · have h3 : a + 1 = b := by omega
      subst h3
      rw [min_eq_left (Nat.le_refl (a + 1)), min_eq_left h.le]
  simp only [posC, key]
  omega

theorem posC_skip {b a : ℕ} (h : b ≤ a) : posC b a = posC (b + 1) 0 := by
  have h1 : min a b = b := min_eq_right h
  simp only [posC, h1]
  rw [min_eq_left (Nat.zero_le (b + 1)), Nat.add_zero]
  exact tri_succ b

/-- The number of steps the search still has to make in the state `(b, a)`: the edges still to
colour (`nEdgeC n - posC b a`), plus the number of vertices still to be skipped over
(`n - b`).  The search consumes exactly one unit of it per step. -/
def fuelC (n : ℕ) (b a : ℕ) : ℕ := (nEdgeC n - posC b a) + (n - b)

private theorem fuelC_succ {n b a : ℕ} (hd : posC b a < nEdgeC n) (h : a < b) :
    fuelC n b (a + 1) + 1 = fuelC n b a := by
  have h2 := posC_succ h
  unfold fuelC
  omega

private theorem fuelC_skip {n b a : ℕ} (hb : b < n) (h : b ≤ a) :
    fuelC n (b + 1) 0 + 1 = fuelC n b a := by
  have h2 := posC_skip h
  unfold fuelC
  omega

/-! ### The pruning test in the new numbering -/

/-- The six vertex-addition slots of a quadruple. -/
def quadSlotsC (n : ℕ) (q : Quad n) : List ℕ :=
  [slotCPair n q.a q.b, slotCPair n q.a q.c, slotCPair n q.a q.d,
    slotCPair n q.b q.c, slotCPair n q.b q.d, slotCPair n q.c q.d]

/-- **The vertex-addition slot at which a `K₄` is completed**: the largest of its six slots. -/
def slotQuadC (n : ℕ) (q : Quad n) : ℕ :=
  max (slotCPair n q.a q.b)
    (max (slotCPair n q.a q.c)
      (max (slotCPair n q.a q.d)
        (max (slotCPair n q.b q.c) (max (slotCPair n q.b q.d) (slotCPair n q.c q.d)))))

private theorem le_qslotC1 (A B C D E F : ℕ) : A ≤ max A (max B (max C (max D (max E F)))) :=
  le_max_left _ _
private theorem le_qslotC2 (A B C D E F : ℕ) : B ≤ max A (max B (max C (max D (max E F)))) :=
  (le_max_left _ _).trans (le_max_right _ _)
private theorem le_qslotC3 (A B C D E F : ℕ) : C ≤ max A (max B (max C (max D (max E F)))) :=
  (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
private theorem le_qslotC4 (A B C D E F : ℕ) : D ≤ max A (max B (max C (max D (max E F)))) :=
  (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
private theorem le_qslotC5 (A B C D E F : ℕ) : E ≤ max A (max B (max C (max D (max E F)))) :=
  (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans
    ((le_max_right _ _).trans (le_max_right _ _))))
private theorem le_qslotC6 (A B C D E F : ℕ) : F ≤ max A (max B (max C (max D (max E F)))) :=
  (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans
    ((le_max_right _ _).trans (le_max_right _ _))))

/-- **Every one of the six slots of a `K₄` is at most the slot at which it is completed.** -/
theorem le_slotQuadC {n : ℕ} (q : Quad n) (s : ℕ) (h : s ∈ quadSlotsC n q) : s ≤ slotQuadC n q := by
  rw [slotQuadC]
  simp only [quadSlotsC, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h
  · rw [h]; exact le_qslotC1 _ _ _ _ _ _
  · rw [h]; exact le_qslotC2 _ _ _ _ _ _
  · rw [h]; exact le_qslotC3 _ _ _ _ _ _
  · rw [h]; exact le_qslotC4 _ _ _ _ _ _
  · rw [h]; exact le_qslotC5 _ _ _ _ _ _
  · rw [h]; exact le_qslotC6 _ _ _ _ _ _

/-- **THE PRUNING TEST** (the distinctness count `ndist`, see `Distinct.lean`). -/
def quadOKC {n k : ℕ} (M : PTab k) (q : Quad n) : Bool :=
  match collect6 M (quadSlotsC n q) with
  | none => true
  | some l => decide (5 ≤ ndist l)

/-- All the `K₄`s of a group are admissible. -/
def allOKC {n k : ℕ} (M : PTab k) : List (Quad n) → Bool
  | [] => true
  | q :: qs => quadOKC M q && allOKC M qs

theorem allOKC_of {n k : ℕ} {M : PTab k} {l : List (Quad n)}
    (h : ∀ q, q ∈ l → quadOKC M q = true) : allOKC M l = true := by
  induction l with
  | nil => rfl
  | cons q qs ih =>
      have h1 : quadOKC M q = true := h q List.mem_cons_self
      have h2 : allOKC M qs = true := ih (fun r hr => h r (List.mem_cons_of_mem _ hr))
      simp only [allOKC, h1, h2, Bool.true_and]

/-- **THE SOUNDNESS OF THE PRUNING TEST.** -/
theorem quadOKC_of {n k : ℕ} {M : PTab k} {q : Quad n} {c : Col n k} {d : ℕ}
    (h : incQuad q) (hd : slotQuadC n q = d)
    (hall : ∀ e, OffDiag e → slotOfC e ≤ d → M (slotOfC e) = some (c e))
    (hc : Admissible c) : quadOKC M q = true := by
  have e1 : slotOfC s(q.a, q.b) ≤ d := by
    rw [← slotCPair_mk, ← hd]; exact le_qslotC1 _ _ _ _ _ _
  have e2 : slotOfC s(q.a, q.c) ≤ d := by
    rw [← slotCPair_mk, ← hd]; exact le_qslotC2 _ _ _ _ _ _
  have e3 : slotOfC s(q.a, q.d) ≤ d := by
    rw [← slotCPair_mk, ← hd]; exact le_qslotC3 _ _ _ _ _ _
  have e4 : slotOfC s(q.b, q.c) ≤ d := by
    rw [← slotCPair_mk, ← hd]; exact le_qslotC4 _ _ _ _ _ _
  have e5 : slotOfC s(q.b, q.d) ≤ d := by
    rw [← slotCPair_mk, ← hd]; exact le_qslotC5 _ _ _ _ _ _
  have e6 : slotOfC s(q.c, q.d) ≤ d := by
    rw [← slotCPair_mk, ← hd]; exact le_qslotC6 _ _ _ _ _ _
  have hFD := fourDistinct_of_incQuad h
  have g1 : M (slotOfC s(q.a, q.b)) = some (c s(q.a, q.b)) :=
    hall _ (offDiag_iff.mpr hFD.1) e1
  have g2 : M (slotOfC s(q.a, q.c)) = some (c s(q.a, q.c)) :=
    hall _ (offDiag_iff.mpr hFD.2.1) e2
  have g3 : M (slotOfC s(q.a, q.d)) = some (c s(q.a, q.d)) :=
    hall _ (offDiag_iff.mpr hFD.2.2.1) e3
  have g4 : M (slotOfC s(q.b, q.c)) = some (c s(q.b, q.c)) :=
    hall _ (offDiag_iff.mpr hFD.2.2.2.1) e4
  have g5 : M (slotOfC s(q.b, q.d)) = some (c s(q.b, q.d)) :=
    hall _ (offDiag_iff.mpr hFD.2.2.2.2.1) e5
  have g6 : M (slotOfC s(q.c, q.d)) = some (c s(q.c, q.d)) :=
    hall _ (offDiag_iff.mpr hFD.2.2.2.2.2) e6
  have key : quadOKC M q = decide (5 ≤ ndist (quadColors c q)) := by
    simp only [quadOKC, quadSlotsC, collect6, slotCPair_mk]
    rw [g1, g2, g3, g4, g5, g6]
    rfl
  rw [key, decide_ndist]
  exact quad_ok_of_admissible h hc

/-- **THE GROUP TABLE** of the vertex-addition search, computed once. -/
def quadGroupsC (n : ℕ) : List (List (Quad n)) :=
  List.ofFn fun d : Fin (nEdgeC n) =>
    (quadsOf n).filter (fun q => slotQuadC n q = d.val)

theorem quadGroupsC_getD (n d : ℕ) (hd : d < nEdgeC n) :
    (quadGroupsC n).getD d [] = (quadsOf n).filter (fun q => slotQuadC n q = d) := by
  rw [quadGroupsC, List.getD]
  simp [hd]

theorem mem_quadGroupsC {n d : ℕ} (hd : d < nEdgeC n) {q : Quad n}
    (h : q ∈ (quadGroupsC n).getD d []) : incQuad q ∧ slotQuadC n q = d := by
  have h2 : q ∈ (quadsOf n).filter (fun r => slotQuadC n r = d) := by
    rw [← quadGroupsC_getD n d hd]; exact h
  simp only [quadsOf, List.mem_filter] at h2
  exact ⟨incQuadB_iff.mp h2.left.2, decide_eq_true_eq.mp h2.right⟩

/-! ### The invariants -/

/-- **The prefix invariant** in the vertex-addition numbering: every edge whose slot is below the
current position is coloured, and nothing beyond the current position is. -/
def PFilledC (n : ℕ) {k : ℕ} (M : PTab k) (b a : ℕ) : Prop :=
  (∀ e : Sym2 (Verts n), OffDiag e → slotOfC e < posC b a → ∃ j : Fin k, M (slotOfC e) = some j) ∧
    (∀ s, posC b a ≤ s → M s = none)

def PSpecC (n : ℕ) {k : ℕ} (M : PTab k) (u b a : ℕ) : Prop := PInv M u ∧ PFilledC n M b a

theorem PSpecC_none {n k : ℕ} : PSpecC n (M := (fun _ => none : PTab k)) 0 1 0 := by
  refine ⟨⟨Nat.zero_le _, ?_, ?_⟩, ⟨?_, ?_⟩⟩
  · intro i hi; omega
  · intro j hj
    obtain ⟨s, hs⟩ := hj
    have hnone : (fun _ => none : PTab k) s = none := rfl
    exact absurd (hnone.symm.trans hs) (by simp)
  · intro e he hlt
    exact (Nat.not_lt_zero (slotOfC e) hlt).elim
  · intro s hs; rfl

/-- **The prefix invariant is preserved by colouring the current slot.** -/
theorem PFilledC_update (n : ℕ) {k : ℕ} {M : PTab k} {b a : ℕ} (hd : posC b a < nEdgeC n)
    (hfill : PFilledC n M b a) (h : a < b) {j : Fin k} :
    PFilledC n (Function.update M (posC b a) (some j)) b (a + 1) := by
  obtain ⟨hfill1, hfill2⟩ := hfill
  have hd' : posC b a < tri n := by simpa [nEdgeC] using hd
  have hb : b < n := lt_n_of_tri_lt (by
    have h1 : tri b ≤ posC b a := by simp only [posC, min_eq_left h.le]; omega
    omega)
  constructor
  · intro e he hlt
    by_cases hF : slotOfC e = posC b a
    · have he' : e = s(⟨a, by omega⟩, ⟨b, hb⟩) :=
        (slotOfC_eq_slotC_iff he h).mp (by rw [hF, posC_eq_slotC h])
      rw [he'] at hF ⊢
      rw [hF]
      exact ⟨j, update_eq_self'⟩
    · have hM : Function.update M (posC b a) (some j) (slotOfC e) = M (slotOfC e) :=
        update_of_ne' hF j
      rw [hM]
      obtain ⟨j', hj'⟩ := hfill1 e he (by have h2 := posC_succ h; omega)
      exact ⟨j', hj'⟩
  · intro s hs
    have h3 : Function.update M (posC b a) (some j) s = M s := update_of_ne' (by
      have h2 := posC_succ h
      omega) j
    rw [h3]
    exact hfill2 s (by have h2 := posC_succ h; omega)

/-- **The prefix invariant survives the skip from vertex `b` to vertex `b+1`.** -/
theorem PFilledC_skip (n : ℕ) {k : ℕ} {M : PTab k} {b a : ℕ} (hfill : PFilledC n M b a)
    (h : b ≤ a) : PFilledC n M (b + 1) 0 := by
  have h2 : PFilledC n M (b + 1) 0 = PFilledC n M b a := by
    unfold PFilledC
    rw [posC_skip h]
  rw [h2]
  exact hfill

/-- The total colouring read off a partial colouring. -/
def tabOfC (n : ℕ) {k : ℕ} (dflt : Fin k) (M : PTab k) : Col n k :=
  fun e => (M (slotOfC e)).getD dflt

theorem tabOfC_agrees {n k : ℕ} (dflt : Fin k) {M : PTab k} {b a : ℕ}
    (hspec : PFilledC n M b a) (e : Sym2 (Verts n)) (he : OffDiag e)
    (hslot : slotOfC e < posC b a) : M (slotOfC e) = some ((tabOfC n dflt M) e) := by
  obtain ⟨j, hj⟩ := hspec.1 e he hslot
  have h2 : (M (slotOfC e)).getD dflt = j := by rw [hj, Option.getD_some]
  unfold tabOfC
  exact hj.trans (congrArg some h2).symm

/-- **Agreement below a position.** -/
def AgreesC {n k : ℕ} (M : PTab k) (c : Col n k) (t : ℕ) : Prop :=
  ∀ e : Sym2 (Verts n), OffDiag e → slotOfC e < t → M (slotOfC e) = some (c e)

private theorem getD_someC {k : ℕ} {M : PTab k} {dflt : Fin k} {s : ℕ} {j : Fin k}
    (h : M s = some j) : (M s).getD dflt = j := by
  simp only [h, Option.getD_some]

theorem colorsOn_tabOfC {n k : ℕ} {dflt : Fin k} {M : PTab k} {c : Col n k} {t : ℕ}
    (hall : AgreesC M c t) (S : Finset (Verts n))
    (ht : ∀ e : Sym2 (Verts n), OffDiag e → slotOfC e < nEdgeC n → slotOfC e < t) :
    colorsOn (tabOfC n dflt M) S = colorsOn c S := by
  refine Finset.image_congr ?_
  intro e hemem
  obtain ⟨a, b, rfl⟩ := Sym2.exists.mp ⟨e, rfl⟩
  obtain ⟨-, hne⟩ := mem_edgeFinset.mp hemem
  have hmem := hall s(a, b) hne (ht _ hne (slotOfC_lt hne))
  unfold tabOfC
  rw [getD_someC hmem]

/-! ### The search -/

/-- **THE VERTEX-ADDITION SEARCH.**  `searchAuxC dflt G M u b a fuel` colours the edge
`{a,b}` (at the position `posC b a`) with a colour from `allowedColors k u` — the colour
permutation symmetry reduction of `FastSearch.lean` — and prunes the branch as soon as one of
the `K₄`s completed at that position fails the catalog condition.  In the state `a ≥ b` it moves
on to the next vertex without colouring. -/
def searchAuxC (n : ℕ) {k : ℕ} (dflt : Fin k) (G : List (List (Quad n))) (M : PTab k)
    (u b a fuel : ℕ) : Bool :=
  match fuel with
  | 0 => decide (Admissible (tabOfC n dflt M))
  | fuel' + 1 =>
      if h : posC b a < nEdgeC n then
        if h2 : a < b then
          (allowedColors k u).any fun j =>
            let M' := Function.update M (posC b a) (some j)
            allOKC M' (G.getD (posC b a) []) &&
              searchAuxC n dflt G M' (if j.val < u then u else u + 1) b (a + 1) fuel'
        else searchAuxC n dflt G M u (b + 1) 0 fuel'
      else decide (Admissible (tabOfC n dflt M))

/-- **Is there an admissible colouring of `K_n` with `k+1` colours?**  (Vertex-addition order.) -/
def hasAdmissibleC (n k : ℕ) : Bool :=
  searchAuxC n (k := k + 1) ⟨0, by omega⟩ (quadGroupsC n) (fun _ => none) 0 1 0 (nEdgeC n + n)

/-! ### Completeness -/

/-- **THE COMPLETENESS THEOREM OF THE VERTEX-ADDITION SEARCH.** -/
theorem searchAuxC_iff {n k : ℕ} (dflt : Fin k) (G : List (List (Quad n))) {M : PTab k}
    {u b a fuel : ℕ}
    (hG : ∀ d, d < nEdgeC n → ∀ q, q ∈ G.getD d [] → incQuad q ∧ slotQuadC n q = d)
    (hm : fuelC n b a ≤ fuel) (hspec : PSpecC n M u b a) :
    searchAuxC n dflt G M u b a fuel = true ↔
      ∃ c : Col n k, AgreesC M c (posC b a) ∧ Admissible c := by
  induction fuel generalizing M u b a with
  | zero =>
      have hlt1 : nEdgeC n ≤ posC b a := by
        have h1 : fuelC n b a = 0 := by omega
        unfold fuelC at h1
        omega
      rw [searchAuxC]
      constructor
      · intro h
        refine ⟨tabOfC n dflt M, ?_, decide_eq_true_eq.mp h⟩
        intro e he hslot
        exact tabOfC_agrees dflt hspec.2 e he (by omega)
      · rintro ⟨c, hagr, hc⟩
        refine decide_eq_true_eq.mpr ?_
        intro S hS
        have hcol : colorsOn (tabOfC n dflt M) S = colorsOn c S :=
          colorsOn_tabOfC hagr S (by
            intro e' he' hlt
            have h2 := slotOfC_lt he'
            omega)
        rw [hcol]
        exact hc S hS
  | succ fuel' ih =>
      have hmf : fuelC n b a ≤ fuel' + 1 := hm
      by_cases hd : posC b a < nEdgeC n
      · rw [searchAuxC, dif_pos hd]
        by_cases hm2 : a < b
        · rw [dif_pos hm2, List.any_eq_true]
          have hb : b < n := lt_n_of_tri_lt (by
            have h1 : tri b ≤ posC b a := by simp only [posC, min_eq_left hm2.le]; omega
            have h2 : posC b a < tri n := by simpa [nEdgeC] using hd
            omega)
          have hne2 : a < n := by omega
          constructor
          · rintro ⟨j, hjmem, hj⟩
            obtain ⟨-, hjG⟩ := (Bool.and_eq_true _ _).mp hj
            have hnone : M (posC b a) = none := hspec.2.2 _ (Nat.le_refl _)
            have hspec' : PSpecC n (Function.update M (posC b a) (some j))
                (if j.val < u then u else u + 1) b (a + 1) :=
              ⟨PInv_update hspec.1 hnone (allowedColors_val_le hjmem),
                PFilledC_update n hd hspec.2 hm2⟩
            have hpos : posC b (a + 1) = posC b a + 1 := posC_succ hm2
            have hm' : fuelC n b (a + 1) ≤ fuel' := by
              have h2 := fuelC_succ hd hm2
              omega
            obtain ⟨c, hagr, hc⟩ := ih hm' hspec' |>.mp hjG
            refine ⟨c, fun e he hslot => ?_, hc⟩
            have hne : slotOfC e ≠ posC b a := by omega
            have h3 : Function.update M (posC b a) (some j) (slotOfC e) = M (slotOfC e) :=
              update_of_ne' hne j
            rw [← h3]
            exact hagr e he (by have h2 := posC_succ hm2; omega)
          · rintro ⟨c, hagr, hc⟩
            set e : Sym2 (Verts n) := s(⟨a, hne2⟩, ⟨b, hb⟩) with hedef
            have hsd2 : slotOfC e = posC b a := by
              rw [hedef, slotOfC_mk, slotCPair_of_lt hm2, ← posC_eq_slotC hm2]
            have hfe : ∀ f : Sym2 (Verts n), OffDiag f → slotOfC f = posC b a → f = e := by
              intro f hfF hF
              exact (slotOfC_eq_slotC_iff hfF hm2).mp (by rw [hF, posC_eq_slotC hm2])
            have hinv := hspec.1
            by_cases hsl : (c e).val ≤ u
            · refine ⟨c e, mem_allowedColors hsl, ?_⟩
              have hagr' : ∀ f : Sym2 (Verts n), OffDiag f → slotOfC f ≤ posC b a →
                  Function.update M (posC b a) (some (c e)) (slotOfC f) = some (c f) := by
                intro f hf hfs
                by_cases hF : slotOfC f = posC b a
                · have h2 : Function.update M (posC b a) (some (c e)) (slotOfC f)
                      = some (c e) := by
                    rw [hF]
                    exact update_eq_self'
                  simpa only [hfe f hf hF] using h2
                · rw [update_of_ne' hF (c e)]
                  exact hagr f hf (by omega)
              have hnone : M (posC b a) = none := hspec.2.2 _ (Nat.le_refl _)
              have hpos : posC b (a + 1) = posC b a + 1 := posC_succ hm2
              refine (Bool.and_eq_true _ _).mpr ⟨allOKC_of (fun q hq => ?_),
                ih ?_ ⟨PInv_update hspec.1 hnone hsl,
                  PFilledC_update n hd hspec.2 hm2⟩ |>.mpr ⟨c, ?_, hc⟩⟩
              · obtain ⟨h1, h2⟩ := hG (posC b a) hd q hq
                exact quadOKC_of h1 h2 hagr' hc
              · have h2 := fuelC_succ hd hm2
                omega
              · intro f hf hfs
                exact hagr' f hf (by omega)
            · have hku : u < k := by
                have h2 := hinv.1
                omega
              have hne : (⟨u, hku⟩ : Fin k) ≠ c e := by
                intro hc'
                have h2 : (⟨u, hku⟩ : Fin k).val = (c e).val := congrArg Fin.val hc'
                simp only [Fin.val_mk] at h2
                omega
              have hc' : Admissible (swapCol c ⟨u, hku⟩ (c e) hne) :=
                admissible_swapCol (n := n) (k := k) (c := c) ⟨u, hku⟩ (c e) hne hc
              refine ⟨⟨u, hku⟩, mem_allowedColors (le_refl u), ?_⟩
              have hmin : min (⟨u, hku⟩ : Fin k).val (c e).val = u := by
                simp only [Fin.val_mk]
                exact Nat.min_eq_left (by omega)
              have hagr' : ∀ f : Sym2 (Verts n), OffDiag f → slotOfC f ≤ posC b a →
                  Function.update M (posC b a) (some (⟨u, hku⟩ : Fin k)) (slotOfC f) =
                    some (swapCol c ⟨u, hku⟩ (c e) hne f) := by
                intro f hf hfs
                by_cases hF : slotOfC f = posC b a
                · have h2 : Function.update M (posC b a) (some (⟨u, hku⟩ : Fin k)) (slotOfC f)
                      = some (swapCol c ⟨u, hku⟩ (c e) hne f) := by
                    rw [hF, hfe f hf hF, swapCol_apply, swp_of_eq hne (c e) rfl]
                    exact update_eq_self'
                  simpa only [hfe f hf hF] using h2
                · rw [update_of_ne' hF ⟨u, hku⟩]
                  have hmem := hagr f hf (by omega)
                  have hval := hinv.2.2 (c f) ⟨slotOfC f, hmem⟩
                  have hfix : swapCol c ⟨u, hku⟩ (c e) hne f = c f :=
                    swapCol_apply_of_small f (by rw [hmin]; exact hval)
                  rw [hfix]
                  exact hmem
              have hnone : M (posC b a) = none := hspec.2.2 _ (Nat.le_refl _)
              have hpos : posC b (a + 1) = posC b a + 1 := posC_succ hm2
              refine (Bool.and_eq_true _ _).mpr ⟨allOKC_of (fun q hq => ?_),
                ih ?_ ⟨PInv_update hspec.1 hnone (le_refl u),
                  PFilledC_update n hd hspec.2 hm2⟩ |>.mpr ⟨_, ?_, hc'⟩⟩
              · obtain ⟨h1, h2⟩ := hG (posC b a) hd q hq
                exact quadOKC_of h1 h2 hagr' hc'
              · have h2 := fuelC_succ hd hm2
                omega
              · intro f hf hfs
                exact hagr' f hf (by omega)
        · rw [dif_neg hm2]
          have hskip : b ≤ a := Nat.le_of_not_gt hm2
          have hspec' : PSpecC n M u (b + 1) 0 := ⟨hspec.1, PFilledC_skip n hspec.2 hskip⟩
          have hm' : fuelC n (b + 1) 0 ≤ fuel' := by
            have hlt : tri b < nEdgeC n := by
              have h1 : tri b ≤ posC b a := by simp only [posC]; omega
              omega
            have hb2 : b < n := lt_n_of_tri_lt (by simpa [nEdgeC] using hlt)
            have h2 := fuelC_skip hb2 hskip
            omega
          constructor
          · intro h
            obtain ⟨c, hagr, hc⟩ := ih hm' hspec' |>.mp h
            refine ⟨c, fun e he hslot => ?_, hc⟩
            rw [posC_skip hskip] at hslot
            exact hagr e he hslot
          · rintro ⟨c, hagr, hc⟩
            refine ih hm' hspec' |>.mpr ⟨c, fun e he hslot => ?_, hc⟩
            rw [← posC_skip hskip] at hslot
            exact hagr e he hslot
      · rw [searchAuxC, dif_neg hd]
        constructor
        · intro h
          refine ⟨tabOfC n dflt M, fun e he hslot => tabOfC_agrees dflt hspec.2 e he hslot,
            decide_eq_true_eq.mp h⟩
        · rintro ⟨c, hagr, hc⟩
          refine decide_eq_true_eq.mpr ?_
          intro S hS
          have hcol : colorsOn (tabOfC n dflt M) S = colorsOn c S :=
            colorsOn_tabOfC hagr S (by
              intro e' he' hlt
              have h2 := slotOfC_lt he'
              omega)
          rw [hcol]
          exact hc S hS

/-- **THE SEARCH IS COMPLETE.** -/
theorem hasAdmissibleC_iff (n k : ℕ) :
    hasAdmissibleC n k = true ↔ ∃ c : Col n (k + 1), Admissible c := by
  have h0 : posC 1 0 = 0 := by
    simp only [posC, Nat.min_zero]
    rfl
  have h := searchAuxC_iff (n := n) (k := k + 1) ⟨0, by omega⟩ (quadGroupsC n)
    (M := fun _ => none) (u := 0) (b := 1) (a := 0) (fuel := nEdgeC n + n)
    (fun d hd q hq => mem_quadGroupsC hd hq)
    (by unfold fuelC; rw [h0]; omega) (PSpecC_none (n := n))
  constructor
  · intro hb
    obtain ⟨c, _, hc⟩ := h.mp hb
    exact ⟨c, hc⟩
  · rintro ⟨T, hT⟩
    exact h.mpr ⟨T, fun e he hslot => (Nat.not_lt_zero _ hslot).elim, hT⟩

set_option maxRecDepth 1000000 in
/-- **CERTIFICATE (vertex-addition search): no admissible 6-colouring of `K₇`.**  Equivalently:
`K₇` has no colouring with six colours satisfying the catalog condition, so
`f(7,4,5) ≥ 7 > 5 = 5(7-1)/6` —
the first order at which `f` exceeds the counting bound. -/
theorem certC_seven_six : hasAdmissibleC 7 5 = false := by native_decide

set_option maxRecDepth 1000000 in
/-- **CERTIFICATE (vertex-addition search): `K₇` has an admissible 7-colouring.**  Together with
`certC_seven_six` this pins `f(7,4,5) = 7`.  (It is also a cross-check of
`hasAdmissibleC_iff`: the search is complete, so it finds the round-robin colouring.) -/
theorem certC_seven_seven : hasAdmissibleC 7 6 = true := by native_decide

set_option maxRecDepth 1000000 in
/-- **CERTIFICATE (vertex-addition search): `K₆` has an admissible 6-colouring.** -/
theorem certC_six_six : hasAdmissibleC 6 5 = true := by native_decide

/-- **THE LOWER-BOUND ENGINE OF THE VERTEX-ADDITION SEARCH.** -/
theorem EG_ge_of_certC {n k : ℕ} (h : hasAdmissibleC n k = false) : k + 2 ≤ EG n := by
  have h1 : ¬ ∃ c : Col n (k + 1), Admissible c := by
    rintro ⟨c, hc⟩
    have h2 : hasAdmissibleC n k = true := (hasAdmissibleC_iff n k).mpr ⟨c, hc⟩
    rw [h2] at h
    exact Bool.noConfusion h
  by_contra hle
  obtain ⟨c, hc⟩ := EG_admissible n
  have hk : EG n ≤ k + 1 := Nat.le_of_not_gt (by omega)
  exact h1 ⟨liftCol c hk, admissible_liftCol c hk hc⟩

/-- **`f(7,4,5) = 7` — THE FIRST EXACT VALUE EXCEEDING THE COUNTING BOUND `5(n-1)/6`.** -/
theorem EG_seven : EG 7 = 7 :=
  Nat.le_antisymm (EG_le_sumCol 7 (by omega)) (EG_ge_of_certC certC_seven_six)

end JSP140
