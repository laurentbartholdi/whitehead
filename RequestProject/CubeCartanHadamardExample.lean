module

public import RequestProject.CubeCartanHadamard

@[expose] public section

/-!
# A model of the descending-cube axioms

The hypotheses collected in `FiniteChains.DescCubeStr` are not vacuous: this file exhibits
the standard example, the cubulation of the positive octant of three-space (the vertices are
triples of natural numbers, the edges decrease one coordinate by one, and the squares and
three-cubes are the usual ones).  It is an infinite three-dimensional cube complex with the
descending-cube property, so `FiniteChains.DescCubeStr.ker_d₂_eq_range_d₃` applies to it and
is a statement with content.

The linear order on the vertices — used only to orient the cells — is the lexicographic one.
-/

namespace FiniteChains

namespace OctantModel

/-- Vertices of the model: triples of natural numbers, ordered lexicographically. -/
abbrev V3 : Type := ℕ ×ₗ ℕ ×ₗ ℕ

/-- The coordinates of a vertex. -/
def co (v : V3) : ℕ × ℕ × ℕ := (ofLex v).map id ofLex

/-- A vertex with prescribed coordinates. -/
def mk3 (a b c : ℕ) : V3 := toLex (a, toLex (b, c))

@[simp] theorem co_mk3 (a b c : ℕ) : co (mk3 a b c) = (a, b, c) := rfl

theorem eq_of_co {u v : V3} (h : co u = co v) : u = v := by
  have h1 := congrArg Prod.fst h
  have h2 := congrArg (fun p => p.2.1) h
  have h3 := congrArg (fun p => p.2.2) h
  exact ofLex.injective (Prod.ext h1 (Prod.ext h2 h3))

/-- The combinatorial distance to the origin. -/
def htO (v : V3) : ℕ := (co v).1 + (co v).2.1 + (co v).2.2

/-- The descending neighbours: the vertices below `w` in every coordinate whose height is
one less — that is, `w` with exactly one coordinate decreased by one. -/
def dnO (w : V3) : Set V3 :=
  {v | (co v).1 ≤ (co w).1 ∧ (co v).2.1 ≤ (co w).2.1 ∧ (co v).2.2 ≤ (co w).2.2 ∧
    htO v + 1 = htO w}

/-- The fourth vertex of a square: the coordinatewise minimum. -/
def medO (_w u v : V3) : V3 :=
  mk3 (min (co u).1 (co v).1) (min (co u).2.1 (co v).2.1) (min (co u).2.2 (co v).2.2)

@[simp] theorem co_medO (w u v : V3) :
    co (medO w u v) = (min (co u).1 (co v).1, min (co u).2.1 (co v).2.1,
      min (co u).2.2 (co v).2.2) := rfl

theorem ne_co {u v : V3} (h : u ≠ v) : co u ≠ co v := fun hc => h (eq_of_co hc)

/-- The cubulated positive octant, as a `DescCubeStr`. -/
def octant : DescCubeStr V3 where
  ht := htO
  dn := dnO
  med := medO
  ht_dn := by
    intro w a ha
    exact ha.2.2.2
  dim_le := by
    classical
    intro w s hs
    -- every descending neighbour of `w` is one of three explicit vertices
    have hsub : s ⊆ ({mk3 ((co w).1 - 1) (co w).2.1 (co w).2.2,
        mk3 (co w).1 ((co w).2.1 - 1) (co w).2.2,
        mk3 (co w).1 (co w).2.1 ((co w).2.2 - 1)} : Finset V3) := by
      intro v hv
      have hmem : v ∈ dnO w := hs hv
      obtain ⟨h1, h2, h3, h4⟩ := hmem
      simp only [htO] at h4
      simp only [Finset.mem_insert, Finset.mem_singleton]
      have hco : (co v).1 = (co w).1 - 1 ∧ (co v).2.1 = (co w).2.1 ∧ (co v).2.2 = (co w).2.2
          ∨ (co v).1 = (co w).1 ∧ (co v).2.1 = (co w).2.1 - 1 ∧ (co v).2.2 = (co w).2.2
          ∨ (co v).1 = (co w).1 ∧ (co v).2.1 = (co w).2.1 ∧ (co v).2.2 = (co w).2.2 - 1 := by
        omega
      rcases hco with ⟨e1, e2, e3⟩ | ⟨e1, e2, e3⟩ | ⟨e1, e2, e3⟩
      · exact Or.inl (eq_of_co (by rw [co_mk3]; exact Prod.ext e1 (Prod.ext e2 e3)))
      · exact Or.inr (Or.inl (eq_of_co (by rw [co_mk3]; exact Prod.ext e1 (Prod.ext e2 e3))))
      · exact Or.inr (Or.inr (eq_of_co (by rw [co_mk3]; exact Prod.ext e1 (Prod.ext e2 e3))))
    refine le_trans (Finset.card_le_card hsub) ?_
    refine le_trans (Finset.card_insert_le _ _) ?_
    refine Nat.succ_le_succ ?_
    refine le_trans (Finset.card_insert_le _ _) ?_
    simp
  med_comm := by
    intro w a b
    apply eq_of_co
    simp [Nat.min_comm]
  med_mem := by
    intro w a b ha hb hab
    obtain ⟨ha1, ha2, ha3, ha4⟩ := ha
    obtain ⟨hb1, hb2, hb3, hb4⟩ := hb
    have hne := ne_co hab
    have hne' : ¬ ((co a).1 = (co b).1 ∧ (co a).2.1 = (co b).2.1 ∧ (co a).2.2 = (co b).2.2) := by
      intro h
      exact hne (Prod.ext h.1 (Prod.ext h.2.1 h.2.2))
    simp only [htO] at ha4 hb4
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [co_medO, htO] <;> omega
  med_ne := by
    intro w a b c ha hb hc hab hac hbc
    obtain ⟨ha1, ha2, ha3, ha4⟩ := ha
    obtain ⟨hb1, hb2, hb3, hb4⟩ := hb
    obtain ⟨hc1, hc2, hc3, hc4⟩ := hc
    have hbc' : ¬ ((co b).1 = (co c).1 ∧ (co b).2.1 = (co c).2.1 ∧ (co b).2.2 = (co c).2.2) := by
      intro h
      exact ne_co hbc (Prod.ext h.1 (Prod.ext h.2.1 h.2.2))
    have hab' : ¬ ((co a).1 = (co b).1 ∧ (co a).2.1 = (co b).2.1 ∧ (co a).2.2 = (co b).2.2) := by
      intro h
      exact ne_co hab (Prod.ext h.1 (Prod.ext h.2.1 h.2.2))
    have hac' : ¬ ((co a).1 = (co c).1 ∧ (co a).2.1 = (co c).2.1 ∧ (co a).2.2 = (co c).2.2) := by
      intro h
      exact ne_co hac (Prod.ext h.1 (Prod.ext h.2.1 h.2.2))
    simp only [htO] at ha4 hb4 hc4
    intro hcon
    have h := congrArg co hcon
    simp only [co_medO, Prod.mk.injEq] at h
    omega
  med_bottom₁ := by
    intro w a b c _ _ _ _ _ _
    apply eq_of_co
    simp only [co_medO, Prod.mk.injEq]
    refine ⟨by omega, by omega, by omega⟩
  med_bottom₂ := by
    intro w a b c _ _ _ _ _ _
    apply eq_of_co
    simp only [co_medO, Prod.mk.injEq]
    refine ⟨by omega, by omega, by omega⟩

theorem mem_dn_mk3 {a b c a' b' c' : ℕ} (h1 : a' ≤ a) (h2 : b' ≤ b) (h3 : c' ≤ c)
    (h4 : a' + b' + c' + 1 = a + b + c) : mk3 a' b' c' ∈ octant.dn (mk3 a b c) :=
  ⟨h1, h2, h3, by simpa [htO] using h4⟩

/-- The model really contains three-cubes: this is the unit cube at the origin, with top
vertex `(1,1,1)` and the three descending directions listed in the lexicographic order. -/
def unitCube : octant.CbC :=
  ⟨(mk3 1 1 1, mk3 0 1 1, mk3 1 0 1, mk3 1 1 0),
    mem_dn_mk3 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    mem_dn_mk3 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    mem_dn_mk3 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    by decide, by decide⟩

/-- Consequently the vanishing of the second homology applies to a nontrivial complex. -/
theorem octant_ker_eq_range :
    LinearMap.ker octant.d₂ = LinearMap.range octant.d₃ :=
  octant.ker_d₂_eq_range_d₃

end OctantModel

end FiniteChains
