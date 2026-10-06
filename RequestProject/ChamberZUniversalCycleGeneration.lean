module

public import RequestProject.ChamberZCoverCellularGeneration
public import RequestProject.OrderUniversalPosetThree

@[expose] public section

/-! Base-cycle generation in the genuine path-class universal-cover cells. -/
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Davis
open RACG Mirror Comb
universe u
variable {V : Type u} [DecidableEq V] [Fintype V] {A : CommRel V}
  {X : Type u} [PartialOrder X] [Nonempty X]
  {M : CayGroup A → Prop} {att : NeSpx A →o X}

/-- Every actual universal-cover two-cycle is a cycle supported on lifted base
triangles plus the actual alternating boundary of finite lifted tetrahedra. -/
theorem exists_uCover_base_cellular_cycle (a : Zpos A X M att)
    (hconn : IsConnected (orderCx (Zpos A X M att)))
    (z : UF (orderCx (Zpos A X M att)) a →₀ ℤ)
    (hz : Comb.bdry2 (uCover (orderCx (Zpos A X M att)) a) z = 0) :
    ∃ c : UF (orderCx (Zpos A X M att)) a →₀ ℤ,
      (∀ t ∈ c.support, InZBase t.1.2.1.1 ∧ InZBase t.1.2.1.2.1 ∧
        InZBase t.1.2.1.2.2) ∧
      Comb.bdry2 (uCover (orderCx (Zpos A X M att)) a) c = 0 ∧
      ∃ y : UOrdTet (Zpos A X M att) a →₀ ℤ, z = c + uOrdBoundary3 y := by
  classical
  obtain ⟨d, ⟨hd, hdc⟩, _⟩ := exists_unique_uOrder_cycle z hz
  obtain ⟨c, hc, hcc, y, he⟩ := exists_cover_base_cellular_cycle
    (uOrderEnd_isPosetCover hconn) d hdc
  refine ⟨Finsupp.mapDomain uOrderFace c, ?_, ?_, Finsupp.mapDomain uOrderTet y, ?_⟩
  · intro t ht
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support ht)
    have hb := (Finsupp.mem_supported ℤ c).mp hc hs
    exact hb
  · exact (uOrderHom_cycle_iff c).mpr hcc
  · have h := congrArg (chain2 uOrderHom) he
    rw (config := { transparency := .default }) [hd, map_add, uOrderHom_ordBoundary3] at h
    exact h

end FiniteChains.Davis
