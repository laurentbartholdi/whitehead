module

public import RequestProject.OrderNerveRealizationSubtypeHomeomorph

@[expose] public section

/-! A family of induced subposets containing every simplex realizes as
an actual quotient cover, even for infinitely many pieces. This is a
weak-topology assertion, not a finite closed-cover argument. -/

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb
open CategoryTheory Simplicial Topology
open scoped Classical

variable {P : Type} [PartialOrder P] {J : Type} (A : J → Set P)

def orderNervePieceMap (j : J) : C(orderNerveRealization (A j), orderNerveRealization P) :=
  ⟨orderNerveRealizationMap (Subtype.val : A j → P) (fun _ _ h => h),
    (orderNerveRealizationMap (Subtype.val : A j → P) (fun _ _ h => h)).hom.continuous⟩

def orderNervePieceQuotient : C((Σ j, orderNerveRealization (A j)), orderNerveRealization P) :=
  ⟨fun x => orderNervePieceMap A x.1 x.2,
    continuous_sigma (fun j => (orderNervePieceMap A j).continuous)⟩

variable (hc : ∀ (n : SimplexCategory) (s : (nerve P).obj (Opposite.op n)),
  ∃ j, ∀ i, s.obj i ∈ A j)

include hc in
theorem orderNervePieceQuotient_surjective : Function.Surjective (orderNervePieceQuotient A) := by
  intro x
  obtain ⟨n, s, z, rfl⟩ := orderNerveRealizationSimplex_jointly_surjective P x
  obtain ⟨j, hj⟩ := hc n s
  exact ⟨⟨j, orderNerveRealizationSimplex (A j) (orderNerveSimplexSubtype (A j) s hj) z⟩,
    orderNerveRealizationSimplex_subtype (A j) s hj z⟩

include hc in
theorem orderNervePieceQuotient_isQuotientMap : IsQuotientMap (orderNervePieceQuotient A) := by
  apply isQuotientMap_iff_isClosed.mpr
  refine ⟨orderNervePieceQuotient_surjective A hc, ?_⟩
  intro T
  constructor
  · exact fun hT => hT.preimage (orderNervePieceQuotient A).continuous
  · intro hT
    apply (orderNerveRealization_isClosed_iff P T).mpr
    intro n s
    obtain ⟨j, hj⟩ := hc n s
    have hjT := (isClosed_sigma_iff.mp hT) j
    have hz := hjT.preimage
      (orderNerveRealizationSimplex (A j) (orderNerveSimplexSubtype (A j) s hj)).hom.continuous
    convert hz using 1
    ext z
    exact iff_of_eq (congrArg (fun x => x ∈ T)
      (orderNerveRealizationSimplex_subtype (A j) s hj z).symm)

theorem orderNerveRealizationSupported_inter (B C : Set P) :
    orderNerveRealizationSupported P (B ∩ C) =
      orderNerveRealizationSupported P B ∩ orderNerveRealizationSupported P C := by
  ext x
  constructor
  · intro h
    exact ⟨fun p hp => h p (fun hpc => hp hpc.1),
      fun p hp => h p (fun hpc => hp hpc.2)⟩
  · rintro ⟨hB, hC⟩ p hp
    by_cases hb : p ∈ B
    · exact hC p (fun hc => hp ⟨hb, hc⟩)
    · exact hB p hb

theorem orderNerveRealizationSubtype_preimage_supported (B C : Set P) :
    (orderNerveRealizationMap (Subtype.val : B → P) (fun _ _ h => h)) ⁻¹'
        orderNerveRealizationSupported P C =
      orderNerveRealizationSupported B {b | b.val ∈ C} := by
  ext x
  constructor
  · intro hx b hb
    have h := hx b.val hb
    simpa only [orderNerveRealizationCoordinates_map_injective
      (Subtype.val : B → P) (fun _ _ h => h) Subtype.val_injective] using h
  · intro hx p hp
    by_cases hb : p ∈ B
    · have h := hx ⟨p, hb⟩ hp
      exact (orderNerveRealizationCoordinates_map_injective
        (Subtype.val : B → P) (fun _ _ h => h) Subtype.val_injective x ⟨p, hb⟩).trans h
    · exact orderNerveRealizationCoordinates_map_outside
        (Subtype.val : B → P) (fun _ _ h => h) x p (by
          simpa only [Subtype.range_coe_subtype, Set.setOf_mem_eq] using hb)

end FiniteChains.Comb
