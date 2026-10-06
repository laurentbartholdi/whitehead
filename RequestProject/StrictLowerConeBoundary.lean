module

public import RequestProject.StrictTopConeInjectivity
public import RequestProject.StrictLowerIntervalChains

@[expose] public section

/-! Vanishing of an actual top-cone internal boundary reflects lower-interval two-cycles. -/
open scoped Classical
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb
universe u
variable {P Q : Type u} [PartialOrder P] [PartialOrder Q]

theorem strictTopConeEdgeChain_filter_top (f : P → Q) (hf : StrictMono f)
    (c : Q) (hc : ∀ x, f x < c) (z : (strictOrderCx P).E →₀ ℤ) :
    (strictTopConeEdgeChain f hf c hc z).filter
      (fun t : (strictOrderCx Q).F => t.1.2.2 = c) = strictTopConeEdgeChain f hf c hc z := by
  apply (Finsupp.filter_eq_self_iff _ _).mpr
  intro t ht
  by_contra htop
  exact ht (strictTopConeEdgeChain_eq_zero_off_top f hf c hc z t htop)

theorem strictLowerChain_filter_top (c : P) (z : (strictOrderCx (Set.Iio c)).F →₀ ℤ) :
    (chain2 (strictLowerIncl c) z).filter
      (fun t : (strictOrderCx P).F => t.1.2.2 = c) = 0 := by
  induction z using Finsupp.induction_linear with
  | zero => simp [Finsupp.filter_zero]
  | add z w hz hw => rw (config := { transparency := .default }) [map_add, Finsupp.filter_add, hz, hw, add_zero]
  | single t n =>
      change (Finsupp.mapDomain (strictLowerIncl c).onF (Finsupp.single t n)).filter _ = 0
      rw (config := { transparency := .default }) [Finsupp.mapDomain_single]
      apply Finsupp.filter_single_of_neg
      exact t.1.2.2.2.ne

/-- An actual tetrahedral fan has zero internal top boundary only if its base is a two-cycle. -/
theorem strictLowerCone_internal_boundary_reflects_cycle (c : P)
    (z : (strictOrderCx (Set.Iio c)).F →₀ ℤ)
    (hz : (strictOrdBoundary3
      (strictTopConeTriangleChain Subtype.val (fun _ _ h => h) c
        (fun x : Set.Iio c => x.2) z)).filter
          (fun t : (strictOrderCx P).F => t.1.2.2 = c) = 0) :
    bdry2 (strictOrderCx (Set.Iio c)) z = 0 := by
  have hzero := strictLowerChain_filter_top c z
  simp only [strictLowerIncl] at hzero
  rw (config := { transparency := .default }) [strictTopConeTriangleChain_boundary, Finsupp.filter_sub,
    strictTopConeEdgeChain_filter_top, hzero, sub_zero] at hz
  apply strictTopConeEdgeChain_injective Subtype.val (fun _ _ h => h) c
    (fun x : Set.Iio c => x.2) Subtype.val_injective
  rwa [map_zero]

/-- Every genuine tetrahedron chain with this top vertex is the cone of an actual interval chain. -/
theorem exists_strictLowerConeChain (c : P) (y : StrictOrdTet P →₀ ℤ)
    (hy : ∀ t ∈ y.support, t.1.2.2.2 = c) :
    ∃ z : (strictOrderCx (Set.Iio c)).F →₀ ℤ,
      strictTopConeTriangleChain Subtype.val (fun _ _ h => h) c
        (fun x : Set.Iio c => x.2) z = y := by
  let f := strictTopConeTriangleTetrahedron Subtype.val (fun _ _ h => h) c
    (fun x : Set.Iio c => x.2)
  have hf : Function.Injective f := strictTopConeTriangleTetrahedron_injective _ _ _ _
    Subtype.val_injective
  refine ⟨y.comapDomain f hf.injOn, ?_⟩
  change Finsupp.mapDomain f (y.comapDomain f hf.injOn) = y
  apply Finsupp.mapDomain_comapDomain _ hf
  intro t ht
  have he := hy t ht
  obtain ⟨⟨a, b, d, e⟩, hab, hbd, hde⟩ := t
  change e = c at he
  subst e
  refine ⟨⟨(⟨a, hab.trans (hbd.trans hde)⟩, ⟨b, hbd.trans hde⟩, ⟨d, hde⟩), hab, hbd⟩, ?_⟩
  rfl

/-- A top-supported tetrahedron chain without internal boundary has an actual lower two-cycle. -/
theorem exists_strictLowerConeCycle (c : P) (y : StrictOrdTet P →₀ ℤ)
    (hy : ∀ t ∈ y.support, t.1.2.2.2 = c)
    (hint : (strictOrdBoundary3 y).filter
      (fun t : (strictOrderCx P).F => t.1.2.2 = c) = 0) :
    ∃ z : (strictOrderCx (Set.Iio c)).F →₀ ℤ,
      bdry2 (strictOrderCx (Set.Iio c)) z = 0 ∧
      strictTopConeTriangleChain Subtype.val (fun _ _ h => h) c
        (fun x : Set.Iio c => x.2) z = y := by
  obtain ⟨z, hz⟩ := exists_strictLowerConeChain c y hy
  refine ⟨z, strictLowerCone_internal_boundary_reflects_cycle c z ?_, hz⟩
  rwa [hz]

end FiniteChains.Comb
