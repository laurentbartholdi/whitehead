module

public import RequestProject.GenusOldCoverSpineFaithfulness
public import RequestProject.OrderRealizationCockcroft

@[expose] public section

/-! The old-cell comparison is injective on genuine integral H2 in every cover. -/
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb Nerve CategoryTheory AlgebraicTopology
variable (q : ℕ) [NeZero q]
  {P : Type} [PartialOrder P] (f : P → QOld (cmpRel (GenusVertex q)))

/-- Source normalization is compatible with reflection of actual old-cell fillings. -/
theorem genus_old_cover_spine_weak_boundary_reflection (hf : IsPosetCover f)
    (c : OrdTri (OldCoveredSpine q f) →₀ ℤ)
    (hc : Comb.bdry2 (orderCx (OldCoveredSpine q f)) c = 0)
    (hbound : ∃ y : OrdTet P →₀ ℤ, ordBoundary3 y =
      chain2 (orderCxMap (oldCoveredSpineToOld q f) (oldCoveredSpineToOld_monotone q f)) c) :
    ∃ y : OrdTet (OldCoveredSpine q f) →₀ ℤ, ordBoundary3 y = c := by
  let g := oldCoveredSpineToOld q f
  have hg := oldCoveredSpineToOld_monotone q f
  have hn : normalizeOrdChain2 c = 0 := by
    apply genus_old_cover_spine_chain_zero_of_cellular_boundary q f hf
      (normalizeOrdChain2 c) (normalizeOrdChain2_cycle c hc)
    obtain ⟨y, hy⟩ := hbound
    refine ⟨y - Finsupp.mapDomain (ordTetMap g hg) (ordNormalizationHomotopy2 c), ?_⟩
    have hh := congrArg (chain2 (orderCxMap g hg)) (ordNormalization_cycle_boundary c hc)
    rw [map_sub, chain2_ordBoundary3] at hh
    rw [map_sub, hy, ← hh]
    abel
  refine ⟨ordNormalizationHomotopy2 c, ?_⟩
  have h := ordNormalization_cycle_boundary c hc
  rw [hn, map_zero, sub_zero] at h
  exact h.symm

theorem genus_old_cover_spine_orderH2_injective (hf : IsPosetCover f) :
    Function.Injective (orderNerveH2Map (oldCoveredSpineToOld q f)
      (oldCoveredSpineToOld_monotone q f)) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro z hz
  induction z using Submodule.Quotient.induction_on with
  | H c =>
    change orderNerveH2Map _ _ (orderNerveH2Class _ c.val c.property) = 0 at hz
    rw [orderNerveH2Map_class] at hz
    obtain ⟨b, hb⟩ := (orderNerveH2Class_eq_zero_iff P _ _).mp hz
    apply (orderNerveH2Class_eq_zero_iff _ _ _).mpr
    exact genus_old_cover_spine_weak_boundary_reflection q f hf c.val c.property ⟨b, hb⟩

/-- This is the actual singular-homology map of the geometric comparison,
not an assumed identification of second homotopy or homology groups. -/
theorem genus_old_cover_spine_singularH2_injective (hf : IsPosetCover f) :
    Function.Injective
      ((((singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj (ModuleCat.of ℤ ℤ)).map
        (orderNerveRealizationMap (oldCoveredSpineToOld q f)
          (oldCoveredSpineToOld_monotone q f))).hom) := by
  intro x y h
  obtain ⟨c, rfl⟩ := (orderCellSingularH2Equiv (OldCoveredSpine q f)).surjective x
  obtain ⟨d, rfl⟩ := (orderCellSingularH2Equiv (OldCoveredSpine q f)).surjective y
  rw [orderCellSingularH2Equiv_natural, orderCellSingularH2Equiv_natural] at h
  exact congrArg (orderCellSingularH2Equiv (OldCoveredSpine q f))
    (genus_old_cover_spine_orderH2_injective q f hf ((orderCellSingularH2Equiv P).injective h))

end FiniteChains.Davis.Genus
