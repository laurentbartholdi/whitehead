import RequestProject.OrderNerveRealizationSubtypeCells

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb
open CategoryTheory Simplicial Topology
open scoped Classical

/-- Actual realization maps compose as the underlying monotone maps do. -/
theorem orderNerveRealizationMap_comp {P Q R : Type}
    [PartialOrder P] [PartialOrder Q] [PartialOrder R]
    (f : P → Q) (hf : Monotone f) (g : Q → R) (hg : Monotone g)
    (x : orderNerveRealization P) :
    orderNerveRealizationMap g hg (orderNerveRealizationMap f hf x) =
      orderNerveRealizationMap (g ∘ f) (hg.comp hf) x := by
  change (SSet.toTop.map (nerveMap hf.functor) ≫
    SSet.toTop.map (nerveMap hg.functor)) x = _
  rw (config := { transparency := .default }) [← Functor.map_comp]
  rfl

/-- The induced monotone inclusion between nested vertex subsets. -/
def orderNerveSubsetInclusion {P : Type} [PartialOrder P] {A B : Set P} (h : A ⊆ B) : A → B :=
  Set.inclusion h

/-- Carrier homeomorphisms commute with the actual nested-subcomplex inclusions. -/
theorem orderNerveRealizationSubtypeHomeomorph_inclusion {P : Type} [PartialOrder P]
    {A B : Set P} (h : A ⊆ B) (x : orderNerveRealization A) :
    Set.inclusion (orderNerveRealizationSubcomplex_mono h)
        (orderNerveRealizationSubtypeHomeomorph A x) =
      orderNerveRealizationSubtypeHomeomorph B
        (orderNerveRealizationMap (Set.inclusion h) (fun _ _ h => h) x) := by
  apply Subtype.ext
  change orderNerveRealizationMap (Subtype.val : A → P) (fun _ _ h => h) x =
    orderNerveRealizationMap (Subtype.val : B → P) (fun _ _ h => h)
      (orderNerveRealizationMap (Set.inclusion h) (fun _ _ h => h) x)
  rw (config := { transparency := .default }) [orderNerveRealizationMap_comp]
  rfl

/-- The commuting inclusion square also holds as an equality of actual continuous maps. -/
theorem orderNerveRealizationSubtypeHomeomorph_inclusion_continuousMap
    {P : Type} [PartialOrder P] {A B : Set P} (h : A ⊆ B) :
    (⟨Set.inclusion (orderNerveRealizationSubcomplex_mono h),
        continuous_inclusion (orderNerveRealizationSubcomplex_mono h)⟩ :
      C((orderNerveRealizationSubcomplex P A : Set (orderNerveRealization P)),
        (orderNerveRealizationSubcomplex P B : Set (orderNerveRealization P)))).comp
        ⟨orderNerveRealizationSubtypeHomeomorph A,
          (orderNerveRealizationSubtypeHomeomorph A).continuous⟩ =
      (⟨orderNerveRealizationSubtypeHomeomorph B,
          (orderNerveRealizationSubtypeHomeomorph B).continuous⟩ :
        C(orderNerveRealization B,
          (orderNerveRealizationSubcomplex P B : Set (orderNerveRealization P)))).comp
        ⟨orderNerveRealizationMap (Set.inclusion h) (fun _ _ h => h),
          (orderNerveRealizationMap (Set.inclusion h) (fun _ _ h => h)).hom.continuous⟩ := by
  ext x
  exact congrArg Subtype.val (orderNerveRealizationSubtypeHomeomorph_inclusion h x)

end FiniteChains.Comb
