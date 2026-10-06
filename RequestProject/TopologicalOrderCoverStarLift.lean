module

public import RequestProject.HomeomorphContinuousMap
public import RequestProject.TopologicalOrderCoverDeck
public import RequestProject.OrderNerveRealizationStarContractible

@[expose] public section

/-! Actual continuous covering lifts over each closed vertex star. They
are obtained by lifting its explicit contraction, so no local path
connectedness or covering-classification hypothesis is added.
Unverified source. -/

noncomputable section
namespace FiniteChains.Comb
open CategoryTheory Simplicial Topology
open scoped unitInterval Classical

theorem orderNerveRealizationMap_vertex {P Q : Type} [PartialOrder P] [PartialOrder Q]
    (f : P → Q) (hf : Monotone f) (v : P) :
    orderNerveRealizationMap f hf (orderNerveRealizationVertex v) =
      orderNerveRealizationVertex (f v) := by
  exact congrArg (fun k : TopCat.of (SimplexCategory.toTop.obj ⦋0⦌) ⟶
      orderNerveRealization Q => k default)
    (orderNerveRealizationSimplex_natural f hf (ComposableArrows.mk₀ v))

theorem orderNerveRealizationCone_vertex {P : Type} [PartialOrder P]
    (v : P) (hv : ∀ p, p ≤ v ∨ v ≤ p) (t : I) :
    orderNerveRealizationCone v hv t (orderNerveRealizationVertex v) =
      orderNerveRealizationVertex v := by
  apply orderNerveRealizationCoordinates_injective P
  funext q
  rw [orderNerveRealizationCone_coordinates, orderNerveRealizationCoordinates_vertex]
  split_ifs <;> ring

namespace TopologicalOrderCover
variable {P : Type} [PartialOrder P] {E : Type} [TopologicalSpace E]
  (p : C(E, orderNerveRealization P)) (hp : IsCoveringMap p)

def starCenter (q : P) : orderNerveVertexStar P q := ⟨q, Or.inl le_rfl⟩

theorem star_comparable (q : P) (v : orderNerveVertexStar P q) :
    v ≤ starCenter q ∨ starCenter q ≤ v := v.property

def starBaseMap (q : P) : C(orderNerveRealization (orderNerveVertexStar P q), orderNerveRealization P) :=
  ⟨orderNerveRealizationMap Subtype.val (fun _ _ h => h),
    (orderNerveRealizationMap (Subtype.val : orderNerveVertexStar P q → P)
      (fun _ _ h => h)).hom.continuous⟩

def starContraction (q : P) :
    (ContinuousMap.const (orderNerveRealization (orderNerveVertexStar P q))
      (orderNerveRealizationVertex q)).Homotopy (starBaseMap q) where
  toFun tx := starBaseMap q
    (orderNerveRealizationCone (starCenter q) (star_comparable q) (unitInterval.symm tx.1) tx.2)
  continuous_toFun := (starBaseMap q).continuous.comp
    ((orderNerveRealizationCone_continuous (starCenter q) (star_comparable q)).comp
      ((unitInterval.continuous_symm.comp continuous_fst).prodMk continuous_snd))
  map_zero_left x := by
    rw [unitInterval.symm_zero, orderNerveRealizationCone_one]
    exact orderNerveRealizationMap_vertex _ _ _
  map_one_left x := by rw [unitInterval.symm_one, orderNerveRealizationCone_zero]

def starLiftHomotopy (v : Cover p hp) :
    C(I × orderNerveRealization (orderNerveVertexStar P v.1), E) :=
  hp.liftHomotopy (starContraction v.1).toContinuousMap (ContinuousMap.const _ (point p hp v))
    (fun x => ((starContraction v.1).apply_zero x).trans (point_projection p hp v).symm)

theorem starLiftHomotopy_projection (v : Cover p hp) (t : I)
    (x : orderNerveRealization (orderNerveVertexStar P v.1)) :
    p (starLiftHomotopy p hp v (t, x)) = starContraction v.1 (t, x) :=
  congrFun (hp.liftHomotopy_lifts _ _ _) (t, x)

theorem starLiftHomotopy_zero (v : Cover p hp)
    (x : orderNerveRealization (orderNerveVertexStar P v.1)) :
    starLiftHomotopy p hp v (0, x) = point p hp v := hp.liftHomotopy_zero _ _ _ x

def starLift (v : Cover p hp) : C(orderNerveRealization (orderNerveVertexStar P v.1), E) :=
  (starLiftHomotopy p hp v).comp ⟨fun x => (1, x), continuous_const.prodMk continuous_id⟩

theorem starLift_projection (v : Cover p hp)
    (x : orderNerveRealization (orderNerveVertexStar P v.1)) :
    p (starLift p hp v x) = starBaseMap v.1 x :=
  (starLiftHomotopy_projection p hp v 1 x).trans ((starContraction v.1).apply_one x)

theorem starLift_center (v : Cover p hp) :
    starLift p hp v (orderNerveRealizationVertex (starCenter v.1)) = point p hp v := by
  let c := orderNerveRealizationVertex (starCenter v.1)
  let L : C(I, E) := (starLiftHomotopy p hp v).comp
    ⟨fun t => (t, c), continuous_id.prodMk continuous_const⟩
  have hproj : ∀ t t', p (L t) = p (L t') := by
    intro t t'
    change p (starLiftHomotopy p hp v (t, c)) = p (starLiftHomotopy p hp v (t', c))
    rw [starLiftHomotopy_projection, starLiftHomotopy_projection]
    change starBaseMap v.1 (orderNerveRealizationCone _ _ (unitInterval.symm t) c) =
      starBaseMap v.1 (orderNerveRealizationCone _ _ (unitInterval.symm t') c)
    dsimp only [c]
    rw [orderNerveRealizationCone_vertex, orderNerveRealizationCone_vertex]
  exact (hp.const_of_comp L.continuous hproj 1 0).trans (starLiftHomotopy_zero p hp v c)

/-- On a closed star the lift is determined by its value at the center. -/
theorem starLift_unique (v : Cover p hp)
    (f : C(orderNerveRealization (orderNerveVertexStar P v.1), E))
    (hf : ∀ x, p (f x) = starBaseMap v.1 x)
    (hc : f (orderNerveRealizationVertex (starCenter v.1)) = point p hp v) :
    f = starLift p hp v := by
  letI := orderNerveRealization_contractible_of_comparable (starCenter v.1) (star_comparable v.1)
  apply ContinuousMap.coe_injective
  exact hp.eq_of_comp_eq f.continuous (starLift p hp v).continuous
    (funext (fun x => (hf x).trans (starLift_projection p hp v x).symm))
    (orderNerveRealizationVertex (starCenter v.1))
    (hc.trans (starLift_center p hp v).symm)

end TopologicalOrderCover
end FiniteChains.Comb
