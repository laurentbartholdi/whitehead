import RequestProject.HomeomorphContinuousMap
import RequestProject.TopologicalCoverPullback
import RequestProject.HomotopyEquivCancellation

/-! Pullbacks along homotopic maps are homeomorphic by covering path
transport. Pullback along a homotopy equivalence preserves the homotopy
type of the total space. All maps use actual homotopy lifts. -/

noncomputable section
namespace Whitehead
open scoped unitInterval Topology Classical

variable {X Y D : Type} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace D]

def coverPullbackHomotopyLift {f₀ f₁ : C(X, Y)} (p : C(D, Y)) (hp : IsCoveringMap p)
    (H : f₀.Homotopy f₁) : C(I × CoverPullback f₀ p, D) :=
  hp.liftHomotopy
    (H.toContinuousMap.comp ⟨fun tz => (tz.1, tz.2.val.1),
      continuous_fst.prodMk (continuous_fst.comp (continuous_subtype_val.comp continuous_snd))⟩)
    (coverPullbackMap f₀ p) (fun z => (H.apply_zero z.val.1).trans z.property)

theorem coverPullbackHomotopyLift_lifts {f₀ f₁ : C(X, Y)} (p : C(D, Y))
    (hp : IsCoveringMap p) (H : f₀.Homotopy f₁) (t : I) (z : CoverPullback f₀ p) :
    p (coverPullbackHomotopyLift p hp H (t, z)) = H (t, z.val.1) :=
  congrFun (hp.liftHomotopy_lifts _ _ _) (t, z)

@[simp] theorem coverPullbackHomotopyLift_zero {f₀ f₁ : C(X, Y)} (p : C(D, Y))
    (hp : IsCoveringMap p) (H : f₀.Homotopy f₁) (z : CoverPullback f₀ p) :
    coverPullbackHomotopyLift p hp H (0, z) = z.val.2 :=
  hp.liftHomotopy_zero _ _ _ z

def coverPullbackTransport {f₀ f₁ : C(X, Y)} (p : C(D, Y)) (hp : IsCoveringMap p)
    (H : f₀.Homotopy f₁) : C(CoverPullback f₀ p, CoverPullback f₁ p) where
  toFun z := ⟨(z.val.1, coverPullbackHomotopyLift p hp H (1, z)),
    (H.apply_one z.val.1).symm.trans (coverPullbackHomotopyLift_lifts p hp H 1 z).symm⟩
  continuous_toFun := ((continuous_fst.comp continuous_subtype_val).prodMk
    ((coverPullbackHomotopyLift p hp H).continuous.comp
      (continuous_const.prodMk continuous_id))).subtype_mk _

theorem coverPullbackTransport_symm_apply {f₀ f₁ : C(X, Y)} (p : C(D, Y))
    (hp : IsCoveringMap p) (H : f₀.Homotopy f₁) (z : CoverPullback f₀ p) :
    coverPullbackTransport p hp H.symm (coverPullbackTransport p hp H z) = z := by
  let z₁ := coverPullbackTransport p hp H z
  let R : I → D := fun t => coverPullbackHomotopyLift p hp H (unitInterval.symm t, z)
  let T : I → D := fun t => coverPullbackHomotopyLift p hp H.symm (t, z₁)
  have hR : Continuous R := (coverPullbackHomotopyLift p hp H).continuous.comp
    (unitInterval.continuous_symm.prodMk continuous_const)
  have hT : Continuous T := (coverPullbackHomotopyLift p hp H.symm).continuous.comp
    (continuous_id.prodMk continuous_const)
  have hproj : p ∘ R = p ∘ T := by
    funext t
    change p (coverPullbackHomotopyLift p hp H (unitInterval.symm t, z)) =
      p (coverPullbackHomotopyLift p hp H.symm (t, z₁))
    rw [coverPullbackHomotopyLift_lifts, coverPullbackHomotopyLift_lifts]
    rfl
  have hzero : R 0 = T 0 := by
    change coverPullbackHomotopyLift p hp H (unitInterval.symm 0, z) =
      coverPullbackHomotopyLift p hp H.symm (0, z₁)
    rw [unitInterval.symm_zero, coverPullbackHomotopyLift_zero]
    rfl
  have he := congrFun (hp.eq_of_comp_eq hR hT hproj 0 hzero) 1
  apply Subtype.ext
  refine Prod.ext rfl ?_
  change coverPullbackHomotopyLift p hp H.symm (1, z₁) = z.val.2
  change coverPullbackHomotopyLift p hp H (unitInterval.symm 1, z) =
    coverPullbackHomotopyLift p hp H.symm (1, z₁) at he
  simpa only [unitInterval.symm_one, coverPullbackHomotopyLift_zero] using he.symm

def coverPullbackHomotopyHomeomorph {f₀ f₁ : C(X, Y)} (p : C(D, Y))
    (hp : IsCoveringMap p) (H : f₀.Homotopy f₁) : CoverPullback f₀ p ≃ₜ CoverPullback f₁ p where
  toFun := coverPullbackTransport p hp H
  invFun := coverPullbackTransport p hp H.symm
  left_inv := coverPullbackTransport_symm_apply p hp H
  right_inv z := by
    simpa only [ContinuousMap.Homotopy.symm_symm] using
      coverPullbackTransport_symm_apply p hp H.symm z
  continuous_toFun := (coverPullbackTransport p hp H).continuous
  continuous_invFun := (coverPullbackTransport p hp H.symm).continuous

def coverPullbackMapHomotopy {f₀ f₁ : C(X, Y)} (p : C(D, Y))
    (hp : IsCoveringMap p) (H : f₀.Homotopy f₁) :
    ContinuousMap.Homotopy (coverPullbackMap f₀ p)
      ((coverPullbackMap f₁ p).comp (coverPullbackTransport p hp H)) where
  toContinuousMap := coverPullbackHomotopyLift p hp H
  map_zero_left := coverPullbackHomotopyLift_zero p hp H
  map_one_left _ := rfl

def coverPullbackMapEquivOfHomotopicId (f : C(Y, Y)) (p : C(D, Y))
    (hp : IsCoveringMap p) (H : f.Homotopy (ContinuousMap.id Y)) :
    ContinuousMap.HomotopyEquiv (CoverPullback f p) D := by
  let E := ((coverPullbackHomotopyHomeomorph p hp H).trans (coverPullbackIdentity p)).toHomotopyEquiv
  have h : (coverPullbackMap f p).Homotopic E.toFun := ⟨coverPullbackMapHomotopy p hp H⟩
  exact {
    toFun := coverPullbackMap f p
    invFun := E.invFun
    left_inv := ((ContinuousMap.Homotopic.refl E.invFun).comp h).trans E.left_inv
    right_inv := (h.comp (ContinuousMap.Homotopic.refl E.invFun)).trans E.right_inv }

/-- The projection from the pullback to the original total space is a
homotopy equivalence when the base map is. Two-of-six avoids imposing any
coherence or stationarity condition on the given base homotopies. -/
def coverPullbackMapHomotopyEquiv (e : ContinuousMap.HomotopyEquiv X Y)
    (p : C(D, Y)) (hp : IsCoveringMap p) :
    ContinuousMap.HomotopyEquiv (CoverPullback e.toFun p) D := by
  let q := coverPullbackProjection e.toFun p
  have hq := coverPullbackProjection_isCoveringMap e.toFun p hp
  let r := coverPullbackProjection e.invFun q
  let f := coverPullbackMap e.toFun r
  let g := coverPullbackMap e.invFun q
  let h := coverPullbackMap e.toFun p
  let E := (coverPullbackComposition e.toFun e.invFun q).toHomotopyEquiv.trans
    (coverPullbackMapEquivOfHomotopicId (e.invFun.comp e.toFun) q hq
      (Classical.choice e.left_inv))
  let F := (coverPullbackComposition e.invFun e.toFun p).toHomotopyEquiv.trans
    (coverPullbackMapEquivOfHomotopicId (e.toFun.comp e.invFun) p hp
      (Classical.choice e.right_inv))
  have hE : E.toFun = g.comp f := rfl
  have hF : F.toFun = h.comp g := rfl
  exact ContinuousMap.HomotopyEquiv.twoOfSixRight f g h E hE F hF

@[simp] theorem coverPullbackMapHomotopyEquiv_toFun (e : ContinuousMap.HomotopyEquiv X Y)
    (p : C(D, Y)) (hp : IsCoveringMap p) :
    (coverPullbackMapHomotopyEquiv e p hp).toFun = coverPullbackMap e.toFun p := rfl

end Whitehead
