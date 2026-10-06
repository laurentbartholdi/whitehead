import RequestProject.OrderNerveTightChainMap
import RequestProject.TopologicalSingular.SmallRefinement
import RequestProject.OrderNerveGradedBoundary

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb
open CategoryTheory AlgebraicTopology TopologicalSingular SingularSubdivision
variable {P : Type} [PartialOrder P]

noncomputable def orderRefinementSmall (P : Type) [PartialOrder P] (n : ℕ) :
    Chain (orderNerveRealization P) n →ₗ[ℤ] smallChains (orderNerveRealizationOpenStar P) n :=
  (smallRefinement (orderNerveRealizationOpenStar P) (orderNerveRealizationOpenStar_isOpen P)
    (orderNerveRealizationOpenStar_cover P) n).codRestrict _
      (smallRefinement_mem_small _ _ _ n)

theorem orderRefinementSmall_boundary (n : ℕ) (c : Chain (orderNerveRealization P) (n + 1)) :
    smallBoundary (orderNerveRealizationOpenStar P) n (orderRefinementSmall P (n + 1) c) =
      orderRefinementSmall P n (boundary n c) := by
  apply Subtype.ext
  exact smallRefinement_boundary _ _ _ n c

noncomputable def orderSingularToNerve (P : Type) [PartialOrder P] (n : ℕ) :
    Chain (orderNerveRealization P) n →ₗ[ℤ] Nerve.Ch P :=
  (orderTightToNerve P n).comp (orderRefinementSmall P n)

theorem orderSingularToNerve_boundary (n : ℕ) (c : Chain (orderNerveRealization P) (n + 1)) :
    Nerve.bdry (orderSingularToNerve P (n + 1) c) =
      orderSingularToNerve P n (boundary n c) := by
  change Nerve.bdry (orderTightToNerve P (n + 1) (orderRefinementSmall P (n + 1) c)) = _
  rw (config := { transparency := .default }) [orderTightToNerve_boundary, orderRefinementSmall_boundary]
  rfl

theorem orderSingularToNerve_zero_boundary (c : Chain (orderNerveRealization P) 0) :
    Nerve.bdry (orderSingularToNerve P 0 c) =
      augmentation c • FreeAbelianGroup.of ([] : List P) := by
  change Nerve.bdry (orderSmallToNerve0 (orderRefinementSmall P 0 c)) = _
  rw (config := { transparency := .default }) [orderSmallToNerve0_boundary]
  rfl

theorem orderSingularToNerve_length (n : ℕ) (c : Chain (orderNerveRealization P) n) :
    Nerve.lengthProjection (n + 1) (orderSingularToNerve P n c) = orderSingularToNerve P n c :=
  orderTightToNerve_length n _

theorem orderSingularToNerve_mem_inc (n : ℕ) (c : Chain (orderNerveRealization P) n) :
    orderSingularToNerve P n c ∈ Nerve.Inc P := orderTightToNerve_mem_inc n _

theorem orderSingularToNerve_supported (n : ℕ) (A : Set P)
    {c : Chain (orderNerveRealization P) n}
    (hc : c ∈ subChains (orderNerveRealizationSubcomplex P A : Set (orderNerveRealization P)) n) :
    orderSingularToNerve P n c ∈ Nerve.IncOn A :=
  orderTightToNerve_supported n A _ (smallRefinement_support _ _ _ n _ hc)

/-- The return map on the original simplicial chains. -/
noncomputable def orderNerveRoundTrip (P : Type) [PartialOrder P] (n : ℕ) :
    (ComposableArrows P n →₀ ℤ) →ₗ[ℤ] Nerve.Ch P :=
  (orderSingularToNerve P n).comp ((orderNerveExplicitSingularMap P).f n).hom

theorem orderNerveRoundTrip_boundary (n : ℕ) (c : ComposableArrows P (n + 1) →₀ ℤ) :
    Nerve.bdry (orderNerveRoundTrip P (n + 1) c) =
      orderNerveRoundTrip P n
        ((AlternatingFaceMapComplex.objD (mathlibOrderNerveModule P) n).hom c) := by
  have he := congrArg (fun f => f c) ((orderNerveExplicitSingularMap P).comm (n + 1) n)
  rw (config := { transparency := .default }) [complex_d, AlternatingFaceMapComplex.obj_d_eq] at he
  change Nerve.bdry (orderSingularToNerve P (n + 1) _) = orderSingularToNerve P n _
  rw (config := { transparency := .default }) [orderSingularToNerve_boundary]
  exact congrArg (orderSingularToNerve P n) he

theorem orderNerveRoundTrip_supported (n : ℕ) (s : ComposableArrows P n) :
    orderNerveRoundTrip P n (Finsupp.single s 1) ∈ Nerve.IncOn (Set.range s.obj) := by
  apply orderSingularToNerve_supported
  change (orderNerveExplicitSingularMap P).f n (Finsupp.single s 1) ∈ _
  rw (config := { transparency := .default }) [orderNerveExplicitSingularMap_single]
  exact single_mem_subChains _ n _ 1 (orderNerveSingularSimplex_supported _ s (fun i => ⟨i, rfl⟩))

theorem orderNerveRoundTrip_zero_boundary (c : ComposableArrows P 0 →₀ ℤ) :
    Nerve.bdry (orderNerveRoundTrip P 0 c) = Nerve.bdry (orderNerveGradedEncode 0 c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, hc, hd]
  | single s r =>
    change Nerve.bdry (orderSingularToNerve P 0 ((orderNerveExplicitSingularMap P).f 0 _)) = _
    rw (config := { transparency := .default }) [orderNerveExplicitSingularMap_single, orderSingularToNerve_zero_boundary,
      augmentation_single, orderNerveGradedEncode_single, map_zsmul, Nerve.bdry_of]
    simp [orderNerveVertexList, List.ofFn_succ, Nerve.bdryOn]

end FiniteChains.Comb
