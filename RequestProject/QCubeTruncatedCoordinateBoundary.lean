module

public import RequestProject.QCubeThreeCoordinateIncidence

@[expose] public section

/-! Genuine finite truncated cube boundaries, including their cut-face coefficients. -/
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Davis
open RACG Mirror Comb
open scoped Classical
variable {V : Type} [DecidableEq V] [Fintype V] {A : CommRel V}

theorem qCube_coordinate_pos_iff (c : QCube A) (σ : Finset V) :
    posCube σ = qCubeToCoordinate c ↔ σ = c.spx ∧ c.sgn = 0 := by
  constructor
  · intro he
    have hs : σ = c.spx := by
      have h := congrArg freeSet he
      simpa using h
    refine ⟨hs, ?_⟩
    funext v
    have h := qCubeToCoordinate_parity c v
    rw [← he] at h
    by_cases hv : v ∈ σ <;> simpa [posCube, hv] using h.symm
  · rintro ⟨rfl, hsgn⟩
    exact (qCubeToCoordinate_sgn_zero c hsgn).symm

variable [LinearOrder V]

noncomputable def qCubeTruncatedCoordinateBoundary (c : QCube A) :
    (Cube V ⊕ Finset V) →₀ ℤ :=
  Finsupp.lmapDomain ℤ ℤ Sum.inl (qCubeCoordinateFacetChain c) +
    if c.sgn = 0 then Finsupp.single (Sum.inr c.spx) (cutSign c.spx) else 0

/-- Every ordinary and cut-face coefficient of the genuine finite truncated boundary
is exactly the boundary used by the collapse. -/
theorem qCubeTruncatedCoordinateBoundary_apply (c : QCube A) (f : Cube V ⊕ Finset V) :
    qCubeTruncatedCoordinateBoundary c f = cubeBdry (qCubeToCoordinate c) f := by
  classical
  cases f with
  | inl g =>
      have hmap : Finsupp.mapDomain (Sum.inl : Cube V → Cube V ⊕ Finset V) (qCubeCoordinateFacetChain c) (Sum.inl g) =
          qCubeCoordinateFacetChain c g := Finsupp.mapDomain_apply_of_injective Sum.inl_injective _ g
      by_cases hsgn : c.sgn = 0 <;>
        simp [qCubeTruncatedCoordinateBoundary, Finsupp.lmapDomain_apply, hmap,
          qCubeCoordinateFacetChain_apply, hsgn]
  | inr σ =>
      have hmap : Finsupp.mapDomain (Sum.inl : Cube V → Cube V ⊕ Finset V) (qCubeCoordinateFacetChain c) (Sum.inr σ) = 0 :=
        Finsupp.mapDomain_notin_range _ _ (by rintro ⟨g, h⟩; cases h)
      simp only [qCubeTruncatedCoordinateBoundary, Finsupp.add_apply,
        Finsupp.lmapDomain_apply, hmap, zero_add, cubeBdry_inr, qCube_coordinate_pos_iff]
      by_cases hsgn : c.sgn = 0
      · by_cases hs : σ = c.spx
        · subst σ
          simp [hsgn]
        · simp [hsgn, hs]
      · simp [hsgn]

/-- For a three-cube the extra cut face has coefficient minus one precisely at the
positive corner, and is absent for every other sign pattern. -/
theorem qThreeCubeTruncatedCoordinateBoundary (c : QThreeCube A) :
    qCubeTruncatedCoordinateBoundary c.1 =
      Finsupp.lmapDomain ℤ ℤ Sum.inl (qCubeCoordinateFacetChain c.1) -
        if c.1.sgn = 0 then Finsupp.single (Sum.inr c.1.spx) 1 else 0 := by
  simp only [qCubeTruncatedCoordinateBoundary, cutSign, c.2]
  by_cases hsgn : c.1.sgn = 0 <;> simp [hsgn, sub_eq_add_neg]

noncomputable def qThreeTruncatedCoordinateBoundary : (QThreeCube A →₀ ℤ) →ₗ[ℤ]
    ((Cube V ⊕ Finset V) →₀ ℤ) :=
  Finsupp.linearCombination ℤ (fun c : QThreeCube A => qCubeTruncatedCoordinateBoundary c.1)

noncomputable def qThreeCutFaceChain : (QThreeCube A →₀ ℤ) →ₗ[ℤ] (Finset V →₀ ℤ) :=
  Finsupp.linearCombination ℤ (fun c : QThreeCube A =>
    if c.1.sgn = 0 then Finsupp.single c.1.spx 1 else 0)

/-- The finite truncated three-boundary is its proved ordinary coordinate boundary
minus the finite chain of positive-corner cut faces. -/
theorem qThreeTruncatedCoordinateBoundary_split (r : QThreeCube A →₀ ℤ) :
    qThreeTruncatedCoordinateBoundary r =
      Finsupp.lmapDomain ℤ ℤ Sum.inl
        (Finsupp.linearCombination ℤ (fun c : QThreeCube A => qCubeCoordinateFacetChain c.1) r) -
      Finsupp.lmapDomain ℤ ℤ Sum.inr (qThreeCutFaceChain r) := by
  classical
  induction r using Finsupp.induction_linear with
  | zero => simp
  | add r s hr hs =>
      simp only [map_add, hr, hs]
      abel
  | single c n =>
      rw [qThreeTruncatedCoordinateBoundary, Finsupp.linearCombination_single,
        qThreeCubeTruncatedCoordinateBoundary, smul_sub,
        Finsupp.linearCombination_single, map_smul,
        qThreeCutFaceChain, Finsupp.linearCombination_single, map_smul]
      by_cases hsgn : c.1.sgn = 0 <;>
        simp [hsgn, Finsupp.lmapDomain_apply]

end FiniteChains.Davis
