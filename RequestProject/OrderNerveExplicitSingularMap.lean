import RequestProject.OrderNerveRealizationSubcomplex
import RequestProject.TopologicalSingular.MathlibComparison

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb
open CategoryTheory Opposite AlgebraicTopology
open TopologicalSingular
open scoped Simplicial

/-- The realization adjunction unit is the canonical realized simplex. -/
theorem orderNerveRealizationUnit_simplex {P : Type} [PartialOrder P]
    {n : SimplexCategory} (s : (nerve P).obj (op n)) :
    ((orderNerveRealizationUnit P).app (op n) s).down =
      orderNerveRealizationSimplex P s := by
  unfold orderNerveRealizationUnit sSetTopAdj
  rw (config := { transparency := .default }) [Presheaf.uliftYonedaAdjunction_unit_app_app]
  rfl

/-- The actual continuous singular simplex associated with an order simplex. -/
noncomputable def orderNerveSingularSimplex {P : Type} [PartialOrder P]
    {n : ℕ} (s : (nerve P).obj (op ⦋n⦌)) :
    Simplex (orderNerveRealization P) n :=
  (simplicesMathlibIso (orderNerveRealization P)).inv.app (op ⦋n⦌)
    ((orderNerveRealizationUnit P).app (op ⦋n⦌) s)

theorem orderNerveSingularSimplex_apply {P : Type} [PartialOrder P]
    {n : ℕ} (s : (nerve P).obj (op ⦋n⦌)) (z : Domain n) :
    orderNerveSingularSimplex s z = orderNerveRealizationSimplex P s (ULift.up ((simplexCoordinates n).symm z)) := by
  exact congrArg (fun f : SimplexCategory.toTop.obj ⦋n⦌ ⟶ orderNerveRealization P =>
    f (ULift.up ((simplexCoordinates n).symm z))) (orderNerveRealizationUnit_simplex s)

theorem orderNerveSingularSimplex_face {P : Type} [PartialOrder P]
    {n : ℕ} (s : (nerve P).obj (op ⦋n + 1⦌)) (i : Fin (n + 2)) :
    face i (orderNerveSingularSimplex s) = orderNerveSingularSimplex ((nerve P).δ i s) := by
  apply ContinuousMap.ext
  intro z
  rw (config := { transparency := .default }) [face_apply, orderNerveSingularSimplex_apply, orderNerveSingularSimplex_apply]
  have h := congrArg (fun f => f (ULift.up ((simplexCoordinates n).symm z)))
    (orderNerveRealizationSimplex_operator P (SimplexCategory.δ i) s)
  change orderNerveRealizationSimplex P s
    (ULift.up (Convexity.StdSimplex.map (SimplexCategory.δ i) ((simplexCoordinates n).symm z))) = _ at h
  have he : Convexity.StdSimplex.map (SimplexCategory.δ i) ((simplexCoordinates n).symm z) =
      (simplexCoordinates (n + 1)).symm (stdSimplex.map (SimplexCategory.δ i) z) := by
    apply (simplexCoordinates (n + 1)).injective
    rw [simplexCoordinates_map, Homeomorph.apply_symm_apply, Homeomorph.apply_symm_apply]
  rw [he] at h
  exact h

theorem orderNerveSingularSimplex_supported {P : Type} [PartialOrder P]
    {n : ℕ} (A : Set P) (s : (nerve P).obj (op ⦋n⦌))
    (hs : ∀ i, s.obj i ∈ A) (z : Domain n) :
    orderNerveSingularSimplex s z ∈ (orderNerveRealizationSubcomplex P A :
      Set (orderNerveRealization P)) := by
  rw (config := { transparency := .default }) [orderNerveSingularSimplex_apply]
  exact orderNerveRealizationSimplex_supported A s hs ⟨ULift.up ((simplexCoordinates n).symm z), rfl⟩

/-- The canonical chain comparison, with explicit continuous simplices as basis. -/
noncomputable def orderNerveExplicitSingularMap (P : Type) [PartialOrder P] :
    AlternatingFaceMapComplex.obj (mathlibOrderNerveModule P) ⟶ complex (orderNerveRealization P) :=
  orderNerveRealizationChainComparison P ≫ (freeComplexMathlibIso (orderNerveRealization P)).inv

theorem orderNerveExplicitSingularMap_single {P : Type} [PartialOrder P]
    (n : ℕ) (s : (nerve P).obj (op ⦋n⦌)) (r : ℤ) :
    (orderNerveExplicitSingularMap P).f n (Finsupp.single s r) =
      Finsupp.single (orderNerveSingularSimplex s) r := by
  change Finsupp.mapDomain _ (Finsupp.mapDomain _ (Finsupp.single s r)) = _
  simp only [Finsupp.mapDomain_single]
  rfl

end FiniteChains.Comb
