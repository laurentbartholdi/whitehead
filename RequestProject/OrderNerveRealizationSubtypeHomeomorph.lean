module

public import RequestProject.OrderNerveRealizationMapCoordinates

@[expose] public section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb
open CategoryTheory Simplicial Topology
open scoped Classical

/-- A lifted simplex realizes to the original simplex under subtype inclusion. -/
theorem orderNerveRealizationSimplex_subtype {P : Type} [PartialOrder P] (A : Set P)
    {n : SimplexCategory} (s : (nerve P).obj (Opposite.op n))
    (hs : ∀ i, s.obj i ∈ A) (z : SimplexCategory.toTop.obj n) :
    orderNerveRealizationMap (Subtype.val : A → P) (fun _ _ h => h)
      (orderNerveRealizationSimplex A (orderNerveSimplexSubtype A s hs) z) =
      orderNerveRealizationSimplex P s z := by
  have ht : (nerveMap (show Monotone (Subtype.val : A → P) from
      fun _ _ h => h).functor).app _ (orderNerveSimplexSubtype A s hs) = s := by
    exact CategoryTheory.Functor.ext (fun _ => rfl)
  have he := congrArg (fun k => k z)
    (orderNerveRealizationSimplex_natural (Subtype.val : A → P)
      (fun _ _ h => h) (orderNerveSimplexSubtype A s hs))
  change orderNerveRealizationMap _ _ (orderNerveRealizationSimplex A _ z) =
    orderNerveRealizationSimplex P ((nerveMap _).app _ _) z at he
  rw (config := { transparency := .default }) [ht] at he
  exact he

/-- Induced-subposet realization inclusions are closed maps in the actual CW topology. -/
theorem orderNerveRealizationSubtype_isClosedMap {P : Type} [PartialOrder P] (A : Set P) :
    IsClosedMap (orderNerveRealizationMap (Subtype.val : A → P) (fun _ _ h => h)) := by
  intro B hB
  let f := orderNerveRealizationMap (Subtype.val : A → P) (fun _ _ h => h)
  apply (CWComplex.closed (orderNerveRealizationSubcomplex P A : Set (orderNerveRealization P))
    (f '' B) ?_).mpr
  · intro n j
    change IsClosed (f '' B ∩ orderNerveCharacteristicMap j.val '' Metric.closedBall 0 1)
    rw (config := { transparency := .default }) [orderNerveCharacteristicMap_closedCell]
    haveI : CompactSpace (SimplexCategory.toTop.obj (SimplexCategory.mk n)) :=
      inferInstanceAs (CompactSpace (ULift.{0} (Convexity.StdSimplex ℝ (Fin (n + 1)))))
    let t := orderNerveSimplexSubtype A j.val.val j.property
    have he : f '' B ∩ Set.range (orderNerveRealizationSimplex P j.val.val) =
        orderNerveRealizationSimplex P j.val.val ''
          (orderNerveRealizationSimplex A t ⁻¹' B) := by
      ext x
      constructor
      · rintro ⟨⟨y, hy, hxy⟩, ⟨z, hzx⟩⟩
        refine ⟨z, ?_, hzx⟩
        have hz : f (orderNerveRealizationSimplex A t z) = f y := by
          change orderNerveRealizationMap (Subtype.val : A → P) _
            (orderNerveRealizationSimplex A (orderNerveSimplexSubtype A j.val.val j.property) z) = _
          rw [orderNerveRealizationSimplex_subtype]
          exact hzx.trans hxy.symm
        change orderNerveRealizationSimplex A t z ∈ B
        rw (config := { transparency := .default }) [orderNerveRealizationMap_injective (Subtype.val : A → P)
          (fun _ _ h => h) Subtype.val_injective hz]
        exact hy
      · rintro ⟨z, hz, rfl⟩
        exact ⟨⟨orderNerveRealizationSimplex A t z, hz,
          orderNerveRealizationSimplex_subtype A j.val.val j.property z⟩, ⟨z, rfl⟩⟩
    rw (config := { transparency := .default }) [he]
    exact ((hB.preimage (orderNerveRealizationSimplex A t).hom.continuous).isCompact.image
      (orderNerveRealizationSimplex P j.val.val).hom.continuous).isClosed
  · rintro x ⟨y, _, rfl⟩
    have h := orderNerveRealizationMap_mem_subcomplex (Subtype.val : A → P)
      (fun _ _ h => h) y
    simpa only [Subtype.range_coe_subtype, Set.setOf_mem_eq, f] using h

/-- The actual realization inclusion of an induced subposet is a closed embedding. -/
theorem orderNerveRealizationSubtype_isClosedEmbedding {P : Type} [PartialOrder P]
    (A : Set P) :
    IsClosedEmbedding (orderNerveRealizationMap (Subtype.val : A → P) (fun _ _ h => h)) :=
  IsClosedEmbedding.of_continuous_injective_isClosedMap
    (orderNerveRealizationMap (Subtype.val : A → P) (fun _ _ h => h)).hom.continuous
    (orderNerveRealizationMap_injective (Subtype.val : A → P)
      (fun _ _ h => h) Subtype.val_injective)
    (orderNerveRealizationSubtype_isClosedMap A)

/-- The induced-subposet realization is homeomorphic to the genuine supported CW carrier. -/
noncomputable def orderNerveRealizationSubtypeHomeomorph {P : Type} [PartialOrder P]
    (A : Set P) : orderNerveRealization A ≃ₜ
      (orderNerveRealizationSubcomplex P A : Set (orderNerveRealization P)) :=
  (orderNerveRealizationSubtype_isClosedEmbedding A).isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr (orderNerveRealizationSubtype_range A))

/-- The carrier homeomorphism is the actual realized inclusion on points. -/
theorem orderNerveRealizationSubtypeHomeomorph_coe {P : Type} [PartialOrder P]
    (A : Set P) (x : orderNerveRealization A) :
    (orderNerveRealizationSubtypeHomeomorph A x).val =
      orderNerveRealizationMap (Subtype.val : A → P) (fun _ _ h => h) x := by
  rfl

/-- Realized monotone maps carry each open cell onto the open cell indexed by
its image simplex whenever that image is nondegenerate. -/
theorem orderNerveRealizationMap_openCell {P Q : Type} [PartialOrder P] [PartialOrder Q]
    (f : P → Q) (hf : Monotone f) {n : ℕ}
    (s : (nerve P).nonDegenerate n) (t : (nerve Q).nonDegenerate n)
    (ht : (nerveMap hf.functor).app _ s.val = t.val) :
    orderNerveRealizationMap f hf ''
        (orderNerveCharacteristicMap s '' Metric.ball 0 1) =
      orderNerveCharacteristicMap t '' Metric.ball 0 1 := by
  rw (config := { transparency := .default }) [orderNerveCharacteristicMap_openCell, orderNerveCharacteristicMap_openCell]
  ext x
  have hn : ∀ z : SimplexCategory.toTop.obj (SimplexCategory.mk n),
      orderNerveRealizationMap f hf (orderNerveRealizationSimplex P s.val z) =
        orderNerveRealizationSimplex Q t.val z := by
    intro z
    have he := congrArg (fun k => k z) (orderNerveRealizationSimplex_natural f hf s.val)
    change orderNerveRealizationMap f hf (orderNerveRealizationSimplex P s.val z) =
      orderNerveRealizationSimplex Q ((nerveMap hf.functor).app _ s.val) z at he
    simpa only [ht] using he
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨z, hz, (hn z).symm⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨orderNerveRealizationSimplex P s.val z, ⟨z, hz, rfl⟩, hn z⟩

/-- Subtype inclusion sends an actual nondegenerate cell to an actual nondegenerate cell. -/
def orderNerveSubtypeCell {P : Type} [PartialOrder P] (A : Set P) {n : ℕ}
    (s : (nerve A).nonDegenerate n) : (nerve P).nonDegenerate n :=
  ⟨(nerveMap (show Monotone (Subtype.val : A → P) from fun _ _ h => h).functor).app _ s.val,
    by
      apply (PartialOrder.mem_nerve_nonDegenerate_iff_strictMono _).mpr
      intro i j hij
      exact ((PartialOrder.mem_nerve_nonDegenerate_iff_strictMono s.val).mp s.property) hij⟩

/-- Every source open cell maps onto the corresponding selected ambient open cell. -/
theorem orderNerveRealizationSubtype_openCell {P : Type} [PartialOrder P] (A : Set P)
    {n : ℕ} (s : (nerve A).nonDegenerate n) :
    orderNerveRealizationMap (Subtype.val : A → P) (fun _ _ h => h) ''
        (orderNerveCharacteristicMap s '' Metric.ball 0 1) =
      orderNerveCharacteristicMap (orderNerveSubtypeCell A s) '' Metric.ball 0 1 :=
  orderNerveRealizationMap_openCell _ _ s (orderNerveSubtypeCell A s) rfl

end FiniteChains.Comb
