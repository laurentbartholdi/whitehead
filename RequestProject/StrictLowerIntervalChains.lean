import RequestProject.StrictThreeBoundarySquared

/-! Actual chains in strict lower intervals and their cone fillings. -/
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb
universe u
variable {P : Type u} [PartialOrder P]

def strictLowerIncl (c : P) : Hom (strictOrderCx (Set.Iio c)) (strictOrderCx P) :=
  strictOrderCxMap Subtype.val (fun _ _ h => h)

theorem strictLowerIncl_injective_onE (c : P) :
    Function.Injective (strictLowerIncl c).onE := by
  intro e f h
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    exact congrArg (fun a : (strictOrderCx P).E => a.1.1) h
  · apply Subtype.ext
    exact congrArg (fun a : (strictOrderCx P).E => a.1.2) h

theorem strictLowerIncl_injective_onF (c : P) :
    Function.Injective (strictLowerIncl c).onF := by
  intro e f h
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    exact congrArg (fun a : (strictOrderCx P).F => a.1.1) h
  · apply Prod.ext
    · apply Subtype.ext
      exact congrArg (fun a : (strictOrderCx P).F => a.1.2.1) h
    · apply Subtype.ext
      exact congrArg (fun a : (strictOrderCx P).F => a.1.2.2) h

/-- A finite triangle chain supported strictly below a cell is an actual interval chain. -/
theorem exists_strictLowerChain (c : P) (z : (strictOrderCx P).F →₀ ℤ)
    (hz : ∀ t ∈ z.support, t.1.2.2 < c) :
    ∃ w : (strictOrderCx (Set.Iio c)).F →₀ ℤ, chain2 (strictLowerIncl c) w = z := by
  refine ⟨z.comapDomain (strictLowerIncl c).onF
    (strictLowerIncl_injective_onF c).injOn, ?_⟩
  apply Finsupp.mapDomain_comapDomain _ (strictLowerIncl_injective_onF c)
  intro t ht
  have htop := hz t ht
  exact ⟨⟨(⟨t.1.1, t.2.1.trans (t.2.2.trans htop)⟩,
    ⟨t.1.2.1, t.2.2.trans htop⟩, ⟨t.1.2.2, htop⟩), t.2⟩, rfl⟩

/-- The interval inclusion reflects genuine cellular two-cycles. -/
theorem strictLowerChain_cycle (c : P) (w : (strictOrderCx (Set.Iio c)).F →₀ ℤ)
    (hw : bdry2 (strictOrderCx P) (chain2 (strictLowerIncl c) w) = 0) :
    bdry2 (strictOrderCx (Set.Iio c)) w = 0 := by
  rw (config := { transparency := .default }) [bdry2_chain2] at hw
  apply Finsupp.mapDomain_injective (strictLowerIncl_injective_onE c)
  change chain1 (strictLowerIncl c) (bdry2 (strictOrderCx (Set.Iio c)) w) =
    chain1 (strictLowerIncl c) 0
  rwa [map_zero]

/-- A genuine strict two-cycle below a cell bounds an explicit tetrahedron chain. -/
theorem strictLowerCycle_bounds (c : P) (z : (strictOrderCx P).F →₀ ℤ)
    (hz : ∀ t ∈ z.support, t.1.2.2 < c)
    (hcycle : bdry2 (strictOrderCx P) z = 0) :
    ∃ y : StrictOrdTet P →₀ ℤ, strictOrdBoundary3 y = z := by
  obtain ⟨w, hw⟩ := exists_strictLowerChain c z hz
  refine ⟨-strictTopConeTriangleChain Subtype.val (fun _ _ h => h) c
    (fun x : Set.Iio c => x.2) w, ?_⟩
  rw (config := { transparency := .default }) [strictTopConeTriangleChain_cycle_boundary _ _ _ _ w
    (strictLowerChain_cycle c w (by rw (config := { transparency := .default }) [hw]; exact hcycle))]
  exact hw

end FiniteChains.Comb
