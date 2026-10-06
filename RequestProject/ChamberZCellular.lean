module

public import RequestProject.ChamberZDegree
public import RequestProject.OrderNerveDecoding

@[expose] public section

/-! Cellular two-cycle generation for the actual modified-chamber poset. -/

namespace FiniteChains.Davis
open RACG Mirror Comb Nerve
universe u
variable {V : Type u} [DecidableEq V] [Fintype V] {A : CommRel V}
  {X : Type u} [PartialOrder X] {M : CayGroup A → Prop} {att : NeSpx A →o X}

instance zposPartialOrder : PartialOrder (Zpos A X M att) where
  toPreorder := zposPreorder
  le_antisymm s t hst hts := by
    cases s with
    | inl p =>
      cases t with
      | inl q => exact congrArg Sum.inl (Subtype.ext (le_antisymm hst hts))
      | inr y => exact hst.elim
    | inr wx =>
      cases t with
      | inl p => exact hts.elim
      | inr vy => exact congrArg Sum.inr (Prod.ext hst.1 (le_antisymm hst.2 hts.2))

/-- Every actual cellular two-cycle of the modified chambers is a base-supported cellular
 two-cycle plus the cellular boundary of actual three-simplices. The witnesses are finitely
 supported and no relative vanishing or chain comparison is supplied as a hypothesis. -/
theorem exists_base_cellular_cycle [Nonempty X]
    (z : OrdTri (Zpos A X M att) →₀ ℤ)
    (hz : Comb.bdry2 (orderCx (Zpos A X M att)) z = 0) :
    ∃ c : OrdTri (Zpos A X M att) →₀ ℤ,
      c ∈ Finsupp.supported ℤ ℤ (ordTriOn (InZBase (A := A) (X := X)
        (M := M) (att := att))) ∧
      Comb.bdry2 (orderCx (Zpos A X M att)) c = 0 ∧
      ∃ y : OrdTet (Zpos A X M att) →₀ ℤ, z = c + ordBoundary3 y := by
  obtain ⟨c, hc, y, hy, hdegc, hdegy, hdc, hzc⟩ :=
    exists_base_cycle_of_cycle_degree 2 (ordNerveChain2_mem_inc z)
      ((ordNerveChain2_cycle_iff z).mpr hz) (ordNerveChain2_lengthProjection z)
  have hec : ordNerveChain2 (decodeOrdNerve2 c) = c :=
    (ordNerveChain2_decode (incOn_le_inc _ hc)).trans hdegc
  have hey : ordNerveChain3 (decodeOrdNerve3 y) = y :=
    (ordNerveChain3_decode hy).trans hdegy
  refine ⟨decodeOrdNerve2 c, decodeOrdNerve2_supported hc, ?_, decodeOrdNerve3 y, ?_⟩
  · apply (ordNerveChain2_cycle_iff _).mp
    rw [hec, hdc]
  · apply ordNerveChain2_injective
    rw [map_add, hec, ordNerveChain2_ordBoundary3, hey]
    exact hzc

end FiniteChains.Davis
