import RequestProject.OrderNerveWithTopCone
import RequestProject.QuotientSameFibersHomeomorph
import RequestProject.BallHomotopyExtension
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! Radial identification of an actual order-nerve cone with a genuine normed
disk. The input is the boundary homeomorphism; the extension, its inverse,
continuity, and exact boundary restriction are constructed here. -/

noncomputable section
namespace FiniteChains.RelativeAttachment
open scoped unitInterval Classical

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem radialPoint_mem_ball (r : I) (x : UnitBoundary E) :
    ‖(r : ℝ) • x.val‖ ≤ 1 := by
  rw [norm_smul, Real.norm_of_nonneg r.property.1, x.property, mul_one]
  exact r.property.2

def ballRadialQuotient : C(I × UnitBoundary E, ClosedUnitBall E) where
  toFun rx := ⟨(rx.1 : ℝ) • rx.2.val, radialPoint_mem_ball E rx.1 rx.2⟩
  continuous_toFun := by
    exact ((continuous_subtype_val.comp continuous_fst).smul
      (continuous_subtype_val.comp continuous_snd)).subtype_mk _

@[simp] theorem ballRadialQuotient_norm (r : I) (x : UnitBoundary E) :
    ‖(ballRadialQuotient E (r, x)).val‖ = (r : ℝ) := by
  change ‖(r : ℝ) • x.val‖ = _
  rw [norm_smul, Real.norm_of_nonneg r.property.1, x.property, mul_one]

@[simp] theorem ballRadialQuotient_one (x : UnitBoundary E) :
    ballRadialQuotient E (1, x) = unitBoundaryInclusion E x := by
  apply Subtype.ext
  exact one_smul ℝ x.val

theorem ballRadialQuotient_eq_iff (a b : I × UnitBoundary E) :
    ballRadialQuotient E a = ballRadialQuotient E b ↔
      a.1 = b.1 ∧ (a.1 = 0 ∨ a.2 = b.2) := by
  constructor
  · intro h
    have hn := (ballRadialQuotient_norm E a.1 a.2).symm.trans
      ((congrArg (fun x : ClosedUnitBall E => ‖x.val‖) h).trans
        (ballRadialQuotient_norm E b.1 b.2))
    have hr : a.1 = b.1 := Subtype.ext hn
    refine ⟨hr, ?_⟩
    by_cases hz : a.1 = 0
    · exact Or.inl hz
    · right
      apply Subtype.ext
      have he := congrArg (fun x : ClosedUnitBall E => x.val) h
      change (a.1 : ℝ) • a.2.val = (b.1 : ℝ) • b.2.val at he
      rw [← hr] at he
      have hrne : (a.1 : ℝ) ≠ 0 := fun ha => hz (Subtype.ext ha)
      have hi := congrArg (fun x : E => (a.1 : ℝ)⁻¹ • x) he
      simpa only [smul_smul, inv_mul_cancel₀ hrne, one_smul] using hi
  · rintro ⟨hr, hz | hx⟩
    · apply Subtype.ext
      change (a.1 : ℝ) • a.2.val = (b.1 : ℝ) • b.2.val
      rw [← hr, hz]
      simp
    · exact congrArg (ballRadialQuotient E) (Prod.ext hr hx)

theorem ballRadialQuotient_surjective (u : UnitBoundary E) :
    Function.Surjective (ballRadialQuotient E) := by
  intro x
  by_cases hx : x.val = 0
  · exact ⟨(0, u), Subtype.ext (by simp [ballRadialQuotient, hx])⟩
  · have hn : ‖x.val‖ ≠ 0 := norm_ne_zero_iff.mpr hx
    let r : I := ⟨‖x.val‖, norm_nonneg _, x.property⟩
    let v : UnitBoundary E := ⟨‖x.val‖⁻¹ • x.val, by
      rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
        inv_mul_cancel₀ hn]⟩
    refine ⟨(r, v), Subtype.ext ?_⟩
    change ‖x.val‖ • (‖x.val‖⁻¹ • x.val) = x.val
    rw [smul_smul, mul_inv_cancel₀ hn, one_smul]

omit [NormedSpace ℝ E] in
theorem unitBoundary_isCompact [ProperSpace E] : IsCompact {x : E | ‖x‖ = 1} := by
  simpa only [Metric.sphere, dist_zero_right] using isCompact_sphere (0 : E) 1

end FiniteChains.RelativeAttachment

namespace FiniteChains.Comb
open RelativeAttachment
open scoped Classical unitInterval

variable {P : Type} [PartialOrder P] [Fintype P] [Nonempty P]
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    (e : orderNerveRealization P ≃ₜ UnitBoundary E)

private def coneBallQuotient : C(I × orderNerveRealization P, ClosedUnitBall E) :=
  (ballRadialQuotient E).comp
    ⟨fun rx => (rx.1, e rx.2), continuous_fst.prodMk (e.continuous.comp continuous_snd)⟩

omit [Fintype P] [ProperSpace E] in
private theorem coneBallQuotient_surjective : Function.Surjective (coneBallQuotient e) := by
  let p₀ : P := Classical.choice inferInstance
  intro x
  obtain ⟨⟨r, u⟩, hu⟩ := ballRadialQuotient_surjective E
    (e (orderNerveRealizationVertex p₀)) x
  exact ⟨(r, e.symm u), by simpa only [coneBallQuotient, ContinuousMap.comp_apply,
    ContinuousMap.coe_mk, Homeomorph.apply_symm_apply] using hu⟩

omit [Fintype P] [Nonempty P] [ProperSpace E] in
private theorem coneBallQuotient_fibers (a b : I × orderNerveRealization P) :
    orderNerveRadialCone P a = orderNerveRadialCone P b ↔
      coneBallQuotient e a = coneBallQuotient e b := by
  rw [orderNerveRadialCone_eq_iff]
  change _ ↔ ballRadialQuotient E (a.1, e a.2) =
    ballRadialQuotient E (b.1, e b.2)
  rw [ballRadialQuotient_eq_iff]
  simp only [e.injective.eq_iff]

/-- Extend a boundary homeomorphism radially over the actual order cone. -/
def orderNerveWithTopBallHomeomorph :
    orderNerveRealization (WithTop P) ≃ₜ ClosedUnitBall E := by
  letI : CompactSpace (UnitBoundary E) := isCompact_iff_compactSpace.mp
    (unitBoundary_isCompact E)
  letI : CompactSpace (orderNerveRealization P) := e.isClosedEmbedding.compactSpace
  exact quotientSameFibersHomeomorph (orderNerveRadialCone P) (coneBallQuotient e)
    ((orderNerveRadialCone P).continuous.isClosedMap.isQuotientMap
      (orderNerveRadialCone P).continuous (orderNerveRadialCone_surjective P))
    ((coneBallQuotient e).continuous.isClosedMap.isQuotientMap
      (coneBallQuotient e).continuous (coneBallQuotient_surjective e))
    (coneBallQuotient_fibers e)

theorem orderNerveWithTopBallHomeomorph_radial (r : I) (x : orderNerveRealization P) :
    orderNerveWithTopBallHomeomorph e (orderNerveRadialCone P (r, x)) =
      ballRadialQuotient E (r, e x) := by
  exact quotientSameFibersHomeomorph_apply _ _ _ _ _ (r, x)

/-- The boundary restriction is exactly the supplied map, with no reparametrization. -/
theorem orderNerveWithTopBallHomeomorph_boundary (x : orderNerveRealization P) :
    orderNerveWithTopBallHomeomorph e (orderNerveConeBase P x) =
      unitBoundaryInclusion E (e x) := by
  rw [← orderNerveRadialCone_one P x, orderNerveWithTopBallHomeomorph_radial,
    ballRadialQuotient_one]

theorem orderNerveWithTopBallHomeomorph_norm (x : orderNerveRealization (WithTop P)) :
    ‖(orderNerveWithTopBallHomeomorph e x).val‖ =
      1 - orderNerveRealizationCoordinates (WithTop P) x ⊤ := by
  obtain ⟨⟨r, u⟩, rfl⟩ := orderNerveRadialCone_surjective P x
  rw [orderNerveWithTopBallHomeomorph_radial, ballRadialQuotient_norm,
    orderNerveRadialCone_top]
  ring

theorem orderNerveWithTopBallHomeomorph_boundary_iff
    (x : orderNerveRealization (WithTop P)) :
    ‖(orderNerveWithTopBallHomeomorph e x).val‖ = 1 ↔
      x ∈ Set.range (orderNerveConeBase P) := by
  constructor
  · intro hx
    obtain ⟨⟨r, u⟩, rfl⟩ := orderNerveRadialCone_surjective P x
    rw [orderNerveWithTopBallHomeomorph_radial, ballRadialQuotient_norm] at hx
    have hr : r = 1 := Subtype.ext hx
    exact ⟨u, by rw [hr, orderNerveRadialCone_one]⟩
  · rintro ⟨u, rfl⟩
    rw [orderNerveWithTopBallHomeomorph_boundary]
    exact (e u).property

end FiniteChains.Comb
