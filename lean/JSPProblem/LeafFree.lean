import JSPProblem.QuadEnum

/-!
# The **leaf-free** vertex-addition search — `JSP-000140`

## Why the leaf test of `VertexSearch.lean` is pure overhead

`VertexSearch.searchAuxC` tests, **at every leaf** — that is, at every complete assignment of the
`C(n,2)` slots — the predicate

```lean
decide (Admissible (tabOfC n dflt M))
```

of `Definitions.lean`.  That predicate quantifies over **all `2^n` four-element `Finset`s** of
`Verts n`, and for each of them builds the image of its six edges under `tabOfC`.  For `n = 9`
that is 512 vertex sets, each with six `Function.update` lookups, a `Finset.image` and a `card` —
per leaf, of which the search has 21 286 763 for the certificate "no admissible 7-colouring of
`K₉`".  (Measured: the search reaches that answer in 4.4 s in C, and did not finish in Lean in
30 minutes.)

**None of it is necessary.**  Every `K₄` of `K_n` is *completed* at the position
`slotQuadC n q` — the largest of its six slots — and `slotQuadC n q < C(n,2)` (`slotQuadC_lt`).
So by the time the search reaches the end of the table, **every `K₄` has already been tested, and
has already passed**; the leaf test only repeats what the pruning tests have done.

`LeafFree.lean` makes this explicit:

* `searchAuxD` is `searchAuxC` with the leaf replaced by `true` (and with `dflt`, `tabOfC` and
  `Admissible` gone from the search altogether);
* the extra invariant **`QPassedC M t`** — every `K₄` completed below the position `t` has already
  passed the pruning test — carries the information the leaf test used to recompute, and is
  maintained by `QPassedC_update` / `QPassedC_skip`;
* **`searchAuxD_iff` is the completeness theorem**: the leaf-free search returns `true` on the
  partial colouring `M` at the position `posC b a` **iff some admissible colouring of `K_n` agrees
  with `M` on every edge below that position** — proved by induction on the fuel, using the
  `QuadEnum` bridge `Admissible c ↔ ∀ q ∈ quadsOf n, …` for the leaves and the round-19
  `admissible_swapCol` for the symmetry step.

The `Finset`-world statement needed at the leaves is isolated in

* **`admissible_of_quadsOKC`** — if a total colouring `c` agrees with a partial colouring `M` on
  every edge, and every `K₄` passes the pruning test on `M`, then `Admissible c`; together with
  `quadOKC_test` (the pruning test read backwards, through `collect6_eq_quadColors` and
  `quadColors_toFinset`) this supplies the "proved equivalence to `Admissible`" that round 21 named
  as the missing ingredient of its blocker **B2′**.
-/

namespace JSP140

private theorem update_of_ne' {k : ℕ} {M : PTab k} {d s : ℕ} (hs : s ≠ d) (j : Fin k) :
    Function.update M d (some j) s = M s := by
  simp only [Function.update]
  rw [dif_neg hs]

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

/-! ### Every `K₄` is completed below the end of the table -/

/-- **The six slots of a `K₄` lie below `C(n,2)`.** -/
theorem quadSlotsC_lt {n : ℕ} {q : Quad n} (h : incQuad q) (s : ℕ) (hs : s ∈ quadSlotsC n q) :
    s < nEdgeC n := by
  have hFD := fourDistinct_of_incQuad h
  simp only [quadSlotsC, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with hs | hs | hs | hs | hs | hs
  · rw [hs]; exact slotCPair_lt hFD.1
  · rw [hs]; exact slotCPair_lt hFD.2.1
  · rw [hs]; exact slotCPair_lt hFD.2.2.1
  · rw [hs]; exact slotCPair_lt hFD.2.2.2.1
  · rw [hs]; exact slotCPair_lt hFD.2.2.2.2.1
  · rw [hs]; exact slotCPair_lt hFD.2.2.2.2.2

private theorem max6_lt {A B C D E F t : ℕ} (h1 : A < t) (h2 : B < t) (h3 : C < t) (h4 : D < t)
    (h5 : E < t) (h6 : F < t) : max A (max B (max C (max D (max E F)))) < t := by
  rw [max_lt_iff]; refine ⟨h1, ?_⟩
  rw [max_lt_iff]; refine ⟨h2, ?_⟩
  rw [max_lt_iff]; refine ⟨h3, ?_⟩
  rw [max_lt_iff]; refine ⟨h4, ?_⟩
  rw [max_lt_iff]; exact ⟨h5, h6⟩

private theorem mem_quadSlotsC (n : ℕ) (q : Quad n) (s : ℕ) (h : s = slotCPair n q.a q.b ∨
    s = slotCPair n q.a q.c ∨ s = slotCPair n q.a q.d ∨ s = slotCPair n q.b q.c ∨
    s = slotCPair n q.b q.d ∨ s = slotCPair n q.c q.d) : s ∈ quadSlotsC n q := by
  rw [quadSlotsC]
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  exact h

/-- **A `K₄` is completed before the last slot of the table.** -/
theorem slotQuadC_lt {n : ℕ} {q : Quad n} (h : incQuad q) : slotQuadC n q < nEdgeC n := by
  have h1 : slotCPair n q.a q.b < nEdgeC n := quadSlotsC_lt h _ (mem_quadSlotsC n q _ (Or.inl rfl))
  have h2 : slotCPair n q.a q.c < nEdgeC n := quadSlotsC_lt h _ (mem_quadSlotsC n q _ (Or.inr (Or.inl rfl)))
  have h3 : slotCPair n q.a q.d < nEdgeC n := quadSlotsC_lt h _ (mem_quadSlotsC n q _ (Or.inr (Or.inr (Or.inl rfl))))
  have h4 : slotCPair n q.b q.c < nEdgeC n := quadSlotsC_lt h _ (mem_quadSlotsC n q _ (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h5 : slotCPair n q.b q.d < nEdgeC n := quadSlotsC_lt h _ (mem_quadSlotsC n q _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h6 : slotCPair n q.c q.d < nEdgeC n := quadSlotsC_lt h _ (mem_quadSlotsC n q _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))))
  simp only [slotQuadC]
  exact max6_lt h1 h2 h3 h4 h5 h6

private theorem offDiag_pair {n : ℕ} {q : Quad n} (h : incQuad q) :
    q.a ≠ q.b ∧ q.a ≠ q.c ∧ q.a ≠ q.d ∧ q.b ≠ q.c ∧ q.b ≠ q.d ∧ q.c ≠ q.d :=
  fourDistinct_of_incQuad h

/-- **The six colours read off a partial colouring which agrees with `c` are the colours of
`c`.** -/
theorem collect6_eq_quadColors {n k : ℕ} {M : PTab k} {q : Quad n} {c : Col n k}
    (h : incQuad q)
    (hagr : ∀ x y : Verts n, x ≠ y → M (slotCPair n x y) = some (c s(x, y))) :
    collect6 M (quadSlotsC n q) = some (quadColors c q) := by
  have hFD := offDiag_pair h
  simp only [quadSlotsC, quadColors, collect6]
  rw [hagr q.a q.b hFD.1, hagr q.a q.c hFD.2.1, hagr q.a q.d hFD.2.2.1,
    hagr q.b q.c hFD.2.2.2.1, hagr q.b q.d hFD.2.2.2.2.1, hagr q.c q.d hFD.2.2.2.2.2]
  rfl

/-- **THE PRUNING TEST, READ BACKWARDS.**  If the partial colouring `M` agrees with `c` on all six
edges of a `K₄`, and the `K₄` passes the pruning test, then `c` gives it at least five colours. -/
theorem quadOKC_test {n k : ℕ} {M : PTab k} {q : Quad n} {c : Col n k}
    (h : incQuad q)
    (hagr : ∀ e : Sym2 (Verts n), OffDiag e → M (slotOfC e) = some (c e))
    (hok : quadOKC M q = true) : 5 ≤ (colorsOn c (quadSet q)).card := by
  have hagr' : ∀ x y : Verts n, x ≠ y → M (slotCPair n x y) = some (c s(x, y)) := by
    intro x y hxy
    have h1 := hagr s(x, y) (offDiag_iff.mpr hxy)
    rwa [slotOfC_mk] at h1
  have h1 : collect6 M (quadSlotsC n q) = some (quadColors c q) :=
    collect6_eq_quadColors h hagr'
  have key : quadOKC M q = decide (5 ≤ ndist (quadColors c q)) := by
    simp only [quadOKC]
    rw [h1]
  rw [key] at hok
  have h2 : 5 ≤ ndist (quadColors c q) := of_decide_eq_true hok
  have h3 : 5 ≤ ((quadColors c q).toFinset : Finset (Fin k)).card :=
    (ndist_eq_card (quadColors c q)) ▸ h2
  rwa [quadColors_toFinset c q h] at h3

set_option maxHeartbeats 800000 in
/-- **THE LEAF IS FREE.**  If a total colouring `c` agrees with a partial colouring `M` on every
edge of `K_n`, and every `K₄` passes the pruning test on `M`, then `c` is admissible.  This is the
equivalence to `Admissible` that the leaf test of `VertexSearch.lean` used to provide by brute
force. -/
theorem admissible_of_quadsOKC {n k : ℕ} {M : PTab k} {c : Col n k}
    (hagr : ∀ e : Sym2 (Verts n), OffDiag e → M (slotOfC e) = some (c e))
    (h : ∀ q : Quad n, incQuad q → quadOKC M q = true) : Admissible c := by
  intro S hS
  obtain ⟨q, hq1, hq2⟩ := exists_mem_quadsOf_of_card hS
  have hq' : incQuad q := incQuad_of_mem_quadsOf hq1
  have hagr' : ∀ x y : Verts n, x ≠ y → M (slotCPair n x y) = some (c s(x, y)) := by
    intro x y hxy
    have h1 := hagr s(x, y) (offDiag_iff.mpr hxy)
    rwa [slotOfC_mk] at h1
  have h5 : 5 ≤ (colorsOn c (quadSet q)).card := quadOKC_test hq' hagr (h q hq')
  rw [← hq2]
  exact h5

/-! ### The invariant that replaces the leaf test -/

/-- **THE PRUNING HISTORY.**  Every `K₄` completed below the position `t` has already passed the
pruning test.  This is exactly the information the leaf test of `VertexSearch.lean` recomputed from
scratch at every leaf. -/
def QPassedC (n : ℕ) {k : ℕ} (M : PTab k) (t : ℕ) : Prop :=
  ∀ q : Quad n, incQuad q → slotQuadC n q < t → quadOKC M q = true

/-- **A member of a group passes the pruning test.** -/
theorem allOKC_of_mem {n k : ℕ} {M : PTab k} {l : List (Quad n)} {q : Quad n}
    (h : allOKC M l = true) (hq : q ∈ l) : quadOKC M q = true := by
  induction l with
  | nil => cases hq
  | cons r rs ih =>
      rw [allOKC] at h
      obtain ⟨h1, h2⟩ := (Bool.and_eq_true _ _).mp h
      rcases List.mem_cons.mp hq with hq | hq
      · subst hq; exact h1
      · exact ih h2 hq

/-- **The pruning test is unchanged by colouring a slot which the `K₄` does not use.** -/
theorem quadOKC_update {n k : ℕ} {M : PTab k} {q : Quad n} {t : ℕ} {j : Fin k}
    (hall : ∀ s, s ∈ quadSlotsC n q → s < t) :
    quadOKC (Function.update M t (some j)) q = quadOKC M q := by
  have key : ∀ l : List ℕ, (∀ s ∈ l, s < t) →
      collect6 (Function.update M t (some j)) l = collect6 M l := by
    intro l
    induction l with
    | nil => intro _; rfl
    | cons s0 ss ih =>
      intro h
      rw [collect6,
        update_of_ne' (fun hst => absurd (hst ▸ h s0 (by simp)) (Nat.lt_irrefl _)) j,
        collect6]
      simp only [ih (fun u hu => h u (List.mem_cons_of_mem s0 hu))]
  simp only [quadOKC]
  rw [key (quadSlotsC n q) hall]

/-- **THE PRUNING HISTORY IS MAINTAINED BY COLOURING THE CURRENT SLOT.** -/
theorem QPassedC_update {n k : ℕ} {M : PTab k} {G : List (List (Quad n))} {t : ℕ} {j : Fin k}
    (hinc : ∀ q : Quad n, incQuad q → q ∈ G.getD (slotQuadC n q) [])
    (hq : QPassedC n M t) (hok : allOKC (Function.update M t (some j)) (G.getD t []) = true) :
    QPassedC n (Function.update M t (some j)) (t + 1) := by
  intro q hq1 hlt
  have hle : slotQuadC n q ≤ t := by omega
  rcases Nat.lt_or_ge (slotQuadC n q) t with h | h
  · rw [quadOKC_update (fun s hs => lt_of_le_of_lt (le_slotQuadC q s hs) h)]
    exact hq q hq1 h
  · have heq : slotQuadC n q = t := le_antisymm hle h
    have hmem : q ∈ (G.getD t []) := by rw [← heq]; exact hinc q hq1
    exact allOKC_of_mem hok hmem

/-- **THE PRUNING HISTORY SURVIVES THE SKIP FROM VERTEX `b` TO VERTEX `b+1`.** -/
theorem QPassedC_skip {n k : ℕ} {M : PTab k} {b a : ℕ} (hq : QPassedC n M (posC b a))
    (h : b ≤ a) : QPassedC n M (posC (b + 1) 0) := by
  rw [← posC_skip h]
  exact hq

/-! ### The group table is complete -/

/-- **THE GROUP TABLE IS COMPLETE**: every `K₄` of `K_n` is tested at the position at which it is
completed.  (`mem_quadGroupsC`, of round 21, is the other direction.) -/
theorem mem_quadGroupsC_slotQuadC {n : ℕ} {q : Quad n} (h : incQuad q) :
    q ∈ (quadGroupsC n).getD (slotQuadC n q) [] := by
  rw [quadGroupsC_getD n (slotQuadC n q) (slotQuadC_lt h)]
  simp only [List.mem_filter]
  exact ⟨mem_quadsOf_of_incQuad h, rfl⟩

/-! ### The leaf-free search -/

/-- **THE LEAF-FREE VERTEX-ADDITION SEARCH.**  As `VertexSearch.searchAuxC`, but the leaf is
`true`: by the time the end of the table is reached every `K₄` has been tested (see
`searchAuxD_iff`). -/
def searchAuxD (n : ℕ) {k : ℕ} (G : List (List (Quad n))) (M : PTab k)
    (u b a fuel : ℕ) : Bool :=
  match fuel with
  | 0 => true
  | fuel' + 1 =>
      if h : posC b a < nEdgeC n then
        if h2 : a < b then
          (allowedColors k u).any fun j =>
            let M' := Function.update M (posC b a) (some j)
            allOKC M' (G.getD (posC b a) []) &&
              searchAuxD n G M' (if j.val < u then u else u + 1) b (a + 1) fuel'
        else searchAuxD n G M u (b + 1) 0 fuel'
      else true

/-- **Is there an admissible colouring of `K_n` with `k+1` colours?**  (Leaf-free
vertex-addition order.) -/
def hasAdmissibleD (n k : ℕ) : Bool :=
  searchAuxD n (k := k + 1) (quadGroupsC n) (fun _ => none) 0 1 0 (nEdgeC n + n)

/-! ### Completeness -/

/-- **THE COMPLETENESS THEOREM OF THE LEAF-FREE SEARCH.** -/
theorem searchAuxD_iff {n k : ℕ} (hk : 1 ≤ k) (G : List (List (Quad n))) {M : PTab k}
    {u b a fuel : ℕ}
    (hG : ∀ d, d < nEdgeC n → ∀ q, q ∈ G.getD d [] → incQuad q ∧ slotQuadC n q = d)
    (hinc : ∀ q : Quad n, incQuad q → q ∈ G.getD (slotQuadC n q) [])
    (hm : fuelC n b a ≤ fuel) (hspec : PSpecC n M u b a) (hq : QPassedC n M (posC b a)) :
    searchAuxD n G M u b a fuel = true ↔
      ∃ c : Col n k, AgreesC M c (posC b a) ∧ Admissible c := by
  induction fuel generalizing M u b a with
  | zero =>
      have hlt1 : nEdgeC n ≤ posC b a := by
        have h1 : fuelC n b a = 0 := by omega
        unfold fuelC at h1
        omega
      have hleaf : true = true ↔ (∃ c : Col n k, AgreesC M c (posC b a) ∧ Admissible c) := by
        constructor
        · intro _
          set dflt : Fin k := ⟨0, by omega⟩ with hdflt
          have hagr : ∀ e : Sym2 (Verts n), OffDiag e →
              M (slotOfC e) = some ((tabOfC n dflt M) e) := by
            intro e he
            exact tabOfC_agrees dflt hspec.2 e he (by have h2 := slotOfC_lt he; omega)
          refine ⟨tabOfC n dflt M, ?_, ?_⟩
          · intro e he hlt'
            exact tabOfC_agrees dflt hspec.2 e he (by have h2 := slotOfC_lt he; omega)
          · exact admissible_of_quadsOKC hagr (fun q hq1 => hq q hq1 (by
              have h2 := slotQuadC_lt hq1
              omega))
        · rintro ⟨_, _, _⟩
          rfl
      rw [searchAuxD]
      exact hleaf
  | succ fuel' ih =>
      have hmf : fuelC n b a ≤ fuel' + 1 := hm
      by_cases hd : posC b a < nEdgeC n
      · rw [searchAuxD, dif_pos hd]
        by_cases hm2 : a < b
        · rw [dif_pos hm2, List.any_eq_true]
          have hb : b < n := lt_n_of_tri_lt (by
            have h1 : tri b ≤ posC b a := by simp only [posC, min_eq_left hm2.le]; omega
            have h2 : posC b a < tri n := by simpa [nEdgeC] using hd
            omega)
          have hne2 : a < n := by omega
          constructor
          · rintro ⟨j, hjmem, hj⟩
            obtain ⟨hjG, hjS⟩ := (Bool.and_eq_true _ _).mp hj
            have hnone : M (posC b a) = none := hspec.2.2 _ (Nat.le_refl _)
            have hspec' : PSpecC n (Function.update M (posC b a) (some j))
                (if j.val < u then u else u + 1) b (a + 1) :=
              ⟨PInv_update hspec.1 hnone (allowedColors_val_le hjmem),
                PFilledC_update n hd hspec.2 hm2⟩
            have hpos : posC b (a + 1) = posC b a + 1 := posC_succ hm2
            have hm' : fuelC n b (a + 1) ≤ fuel' := by
              have h2 := fuelC_succ hd hm2
              omega
            have hq' : QPassedC n (Function.update M (posC b a) (some j)) (posC b a + 1) :=
              QPassedC_update hinc hq hjG
            rw [← hpos] at hq'
            obtain ⟨c, hagr, hc⟩ := ih hm' hspec' hq' |>.mp hjS
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
                    simp [Function.update]
                  simpa only [hfe f hf hF] using h2
                · rw [update_of_ne' hF (c e)]
                  exact hagr f hf (by omega)
              have hnone : M (posC b a) = none := hspec.2.2 _ (Nat.le_refl _)
              have hpos : posC b (a + 1) = posC b a + 1 := posC_succ hm2
              have hok : allOKC (Function.update M (posC b a) (some (c e)))
                  (G.getD (posC b a) []) = true := by
                refine allOKC_of (fun q hqq => ?_)
                obtain ⟨h1, h2⟩ := hG (posC b a) hd q hqq
                exact quadOKC_of h1 h2 hagr' hc
              refine (Bool.and_eq_true _ _).mpr ⟨hok,
                ih ?_ ⟨PInv_update hspec.1 hnone hsl, PFilledC_update n hd hspec.2 hm2⟩ ?_ |>.mpr
                  ⟨c, ?_, hc⟩⟩
              · have h2 := fuelC_succ hd hm2
                omega
              · rw [hpos]
                exact QPassedC_update hinc hq hok
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
                    simp [Function.update]
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
              have hok : allOKC (Function.update M (posC b a) (some (⟨u, hku⟩ : Fin k)))
                  (G.getD (posC b a) []) = true := by
                refine allOKC_of (fun q hqq => ?_)
                obtain ⟨h1, h2⟩ := hG (posC b a) hd q hqq
                exact quadOKC_of h1 h2 hagr' hc'
              refine (Bool.and_eq_true _ _).mpr ⟨hok,
                ih ?_ ⟨PInv_update hspec.1 hnone (le_refl u),
                  PFilledC_update n hd hspec.2 hm2⟩ ?_ |>.mpr ⟨_, ?_, hc'⟩⟩
              · have h2 := fuelC_succ hd hm2
                omega
              · rw [hpos]
                exact QPassedC_update hinc hq hok
              · intro f hf hfs
                exact hagr' f hf (by omega)
        · rw [dif_neg hm2]
          have hskip : b ≤ a := Nat.le_of_not_gt hm2
          have hspec' : PSpecC n M u (b + 1) 0 := ⟨hspec.1, PFilledC_skip n hspec.2 hskip⟩
          have hq' : QPassedC n M (posC (b + 1) 0) := QPassedC_skip hq hskip
          have hm' : fuelC n (b + 1) 0 ≤ fuel' := by
            have hlt : tri b < nEdgeC n := by
              have h1 : tri b ≤ posC b a := by simp only [posC]; omega
              omega
            have hb2 : b < n := lt_n_of_tri_lt (by simpa [nEdgeC] using hlt)
            have h2 := fuelC_skip hb2 hskip
            omega
          constructor
          · intro h
            obtain ⟨c, hagr, hc⟩ := ih hm' hspec' hq' |>.mp h
            refine ⟨c, fun e he hslot => ?_, hc⟩
            rw [posC_skip hskip] at hslot
            exact hagr e he hslot
          · rintro ⟨c, hagr, hc⟩
            refine ih hm' hspec' hq' |>.mpr ⟨c, fun e he hslot => ?_, hc⟩
            rw [← posC_skip hskip] at hslot
            exact hagr e he hslot
      · rw [searchAuxD, dif_neg hd]
        have hleaf : true = true ↔ (∃ c : Col n k, AgreesC M c (posC b a) ∧ Admissible c) := by
          constructor
          · intro _
            set dflt : Fin k := ⟨0, by omega⟩ with hdflt
            have hagr : ∀ e : Sym2 (Verts n), OffDiag e →
                M (slotOfC e) = some ((tabOfC n dflt M) e) := by
              intro e he
              exact tabOfC_agrees dflt hspec.2 e he (by have h2 := slotOfC_lt he; omega)
            refine ⟨tabOfC n dflt M, ?_, ?_⟩
            · intro e he hlt'
              exact tabOfC_agrees dflt hspec.2 e he (by have h2 := slotOfC_lt he; omega)
            · exact admissible_of_quadsOKC hagr (fun q hq1 => hq q hq1 (by
                have h2 := slotQuadC_lt hq1
                omega))
          · rintro ⟨_, _, _⟩
            rfl
        constructor
        · intro h; exact hleaf.mp h
        · intro h; exact hleaf.mpr h

/-- **THE LEAF-FREE SEARCH IS COMPLETE.** -/
theorem hasAdmissibleD_iff (n k : ℕ) :
    hasAdmissibleD n k = true ↔ ∃ c : Col n (k + 1), Admissible c := by
  have h0 : posC 1 0 = 0 := by simp only [posC, Nat.min_zero]; rfl
  have hq0 : QPassedC n (fun _ => none : PTab (k + 1)) (posC 1 0) := by
    intro q hq1 hlt
    exact absurd hlt (Nat.not_lt_zero _)
  have h := searchAuxD_iff (n := n) (k := k + 1) (by omega) (quadGroupsC n)
    (M := fun _ => none) (u := 0) (b := 1) (a := 0) (fuel := nEdgeC n + n)
    (fun d hd q hq => mem_quadGroupsC hd hq) (fun q hq => mem_quadGroupsC_slotQuadC hq)
    (by unfold fuelC; rw [h0]; omega) (PSpecC_none (n := n)) hq0
  constructor
  · intro hb
    obtain ⟨c, _, hc⟩ := h.mp hb
    exact ⟨c, hc⟩
  · rintro ⟨T, hT⟩
    exact h.mpr ⟨T, fun e he hslot => (Nat.not_lt_zero _ hslot).elim, hT⟩

/-- **THE LOWER-BOUND ENGINE OF THE LEAF-FREE SEARCH.** -/
theorem EG_ge_of_certD {n k : ℕ} (h : hasAdmissibleD n k = false) : k + 2 ≤ EG n := by
  have h1 : ¬ ∃ c : Col n (k + 1), Admissible c := by
    rintro ⟨c, hc⟩
    have h2 : hasAdmissibleD n k = true := (hasAdmissibleD_iff n k).mpr ⟨c, hc⟩
    rw [h2] at h
    exact Bool.noConfusion h
  by_contra hle
  obtain ⟨c, hc⟩ := EG_admissible n
  have hk : EG n ≤ k + 1 := Nat.le_of_not_gt (by omega)
  exact h1 ⟨liftCol c hk, admissible_liftCol c hk hc⟩

/-! ### Certificates -/

set_option maxRecDepth 1000000 in
/-- **CERTIFICATE (leaf-free search): no admissible 6-colouring of `K₇`.**  Equivalently:
`K₇` has no colouring with six colours satisfying the catalog condition, so
`f(7,4,5) ≥ 7 > 5 = 5(7-1)/6`.  The same certificate as `VertexSearch.certC_seven_six`, obtained
without the leaf test and without a `Finset` per `K₄`. -/
theorem certD_seven_six : hasAdmissibleD 7 5 = false := by native_decide

set_option maxRecDepth 1000000 in
/-- **CERTIFICATE (leaf-free search): `K₇` has an admissible 7-colouring.**  Together with
`certD_seven_six` this pins `f(7,4,5) = 7`, and is a cross-check of `hasAdmissibleD_iff`. -/
theorem certD_seven_seven : hasAdmissibleD 7 6 = true := by native_decide

/-- **`f(7,4,5) = 7` through the leaf-free engine.** -/
theorem EG_seven_leaffree : EG 7 = 7 :=
  Nat.le_antisymm (EG_le_sumCol 7 (by omega)) (EG_ge_of_certD certD_seven_six)

end JSP140
