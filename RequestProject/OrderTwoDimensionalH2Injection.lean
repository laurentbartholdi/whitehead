module

public import RequestProject.OrderRealizationCockcroft
public import RequestProject.OrderThreeNormalization
public import RequestProject.StrictOrderNormalizationMaps

@[expose] public section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

set_option maxHeartbeats 1600000

namespace FiniteChains.Comb
open CategoryTheory AlgebraicTopology
variable {P Q : Type} [PartialOrder P] [PartialOrder Q]

/-- The stated nerve dimension bound excludes actual strictly increasing tetrahedra. -/
theorem strictOrdTet_isEmpty_of_dimension_two [(nerve P).HasDimensionLE 2] :
    IsEmpty (StrictOrdTet P) := by
  refine ⟨fun t => ?_⟩
  let s := ordTetNerveEquiv P ⟨t.1, t.2.1.le, t.2.2.1.le, t.2.2.2.le⟩
  have hs : s ∈ (nerve P).nonDegenerate 3 := by
    apply (PartialOrder.mem_nerve_nonDegenerate_iff_strictMono s).mpr
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    fin_cases i
    · exact t.2.1
    · exact t.2.2.1
    · exact t.2.2.2
  have hdim := (nerve P).dim_le_of_nonDegenerate ⟨s, hs⟩ 2
  omega

theorem normalizeOrdBoundary3_eq_zero_of_dimension_two [(nerve P).HasDimensionLE 2]
    (b : OrdTet P →₀ ℤ) : normalizeOrdChain2 (ordBoundary3 b) = 0 := by
  letI := strictOrdTet_isEmpty_of_dimension_two (P := P)
  rw (config := { transparency := .default }) [normalizeOrdChain2_ordBoundary3]
  have hz : normalizeOrdChain3 b = 0 := Subsingleton.elim _ _
  rw (config := { transparency := .default }) [hz, map_zero]

theorem strictOrderEmbedding_chain2_injective (f : P ↪o Q) :
    Function.Injective (chain2 (strictOrderCxMap f f.strictMono)) := by
  apply Finsupp.mapDomain_injective
  intro s t h
  apply Subtype.ext
  refine Prod.ext (f.injective (congrArg (fun t : StrictOrdTri Q => t.1.1) h)) ?_
  exact Prod.ext (f.injective (congrArg (fun t : StrictOrdTri Q => t.1.2.1) h))
    (f.injective (congrArg (fun t : StrictOrdTri Q => t.1.2.2) h))

/-- Subcomplex inclusions into a two-dimensional order realization are injective
on order H2; three-boundaries are handled by the explicit normalization homotopy. -/
theorem orderNerveH2Map_embedding_injective [(nerve Q).HasDimensionLE 2]
    (f : P ↪o Q) : Function.Injective (orderNerveH2Map f f.monotone) := by
  apply (injective_iff_map_eq_zero (orderNerveH2Map f f.monotone)).mpr
  intro z hz
  induction z using Submodule.Quotient.induction_on with
  | H c =>
    change orderNerveH2Map f f.monotone (orderNerveH2Class P c.val c.property) = 0 at hz
    rw (config := { transparency := .default }) [orderNerveH2Map_class] at hz
    obtain ⟨b, hb⟩ := (orderNerveH2Class_eq_zero_iff Q _ _).mp hz
    have hn := congrArg normalizeOrdChain2 hb
    rw (config := { transparency := .default }) [normalizeOrdBoundary3_eq_zero_of_dimension_two,
      normalizeOrdChain2_strict_map f f.strictMono] at hn
    have hc : normalizeOrdChain2 c.val = 0 := by
      apply strictOrderEmbedding_chain2_injective f
      rw (config := { transparency := .default }) [map_zero]
      exact hn.symm
    change orderNerveH2Class P c.val c.property = 0
    apply (orderNerveH2Class_eq_zero_iff P _ _).mpr
    refine ⟨ordNormalizationHomotopy2 c.val, ?_⟩
    have h := ordNormalization_cycle_boundary c.val c.property
    rw (config := { transparency := .default }) [hc, map_zero, sub_zero] at h
    exact h.symm

/-- The injection is for Mathlib's genuine integral singular H2. -/
theorem orderRealization_singularH2_embedding_injective [(nerve Q).HasDimensionLE 2]
    (f : P ↪o Q) :
    Function.Injective
      ((((singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj (ModuleCat.of ℤ ℤ)).map
        (orderNerveRealizationMap f f.monotone)).hom) := by
  intro x y h
  obtain ⟨c, rfl⟩ := (orderCellSingularH2Equiv P).surjective x
  obtain ⟨d, rfl⟩ := (orderCellSingularH2Equiv P).surjective y
  rw [orderCellSingularH2Equiv_natural, orderCellSingularH2Equiv_natural] at h
  exact congrArg (orderCellSingularH2Equiv P)
    (orderNerveH2Map_embedding_injective f ((orderCellSingularH2Equiv Q).injective h))

/-- The necessary Cockcroft condition follows from a genuine pi2-killing
embedding into a two-dimensional order realization. -/
theorem orderRealization_isCockcroft_of_killsPi2_embedding [(nerve Q).HasDimensionLE 2]
    (f : P ↪o Q)
    (hk : Whitehead.KillsPi2
      ⟨orderNerveRealizationMap f f.monotone, (orderNerveRealizationMap f f.monotone).hom.continuous⟩) :
    Whitehead.IsCockcroft (orderNerveRealization P) :=
  Whitehead.isCockcroft_of_killsPi2_of_homology_injective _ hk
    (orderRealization_singularH2_embedding_injective f)

end FiniteChains.Comb
