module

public import RequestProject.OrderUniversalPosetHom
public import RequestProject.CombCellularIso

@[expose] public section

/-! Connectivity of the actual path-class universal-cover order complex. -/
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb
universe u
variable {P : Type u} [PartialOrder P] {a : P}

noncomputable def uOrderHomInv : Hom (uCover (orderCx P) a) (orderCx (UOrder P a)) :=
  homInv uOrderHom Function.bijective_id
    ⟨uOrderEdge_injective, uOrderEdge_surjective⟩
    ⟨uOrderFace_injective, uOrderFace_surjective⟩

theorem uOrderHomInv_vertex (v : UOrder P a) : uOrderHomInv.onV v = v :=
  homInv_onV_comp uOrderHom Function.bijective_id
    ⟨uOrderEdge_injective, uOrderEdge_surjective⟩
    ⟨uOrderFace_injective, uOrderFace_surjective⟩ v

theorem uOrderHomInv_path (p : List ((orderCx (UOrder P a)).E × Bool)) :
    mapPath uOrderHomInv (mapPath uOrderHom p) = p :=
  mapPath_homInv uOrderHom Function.bijective_id
    ⟨uOrderEdge_injective, uOrderEdge_surjective⟩
    ⟨uOrderFace_injective, uOrderFace_surjective⟩ p

/-- The actual lifted-order complex is connected, without any connectivity assumption
on the original poset: path classes use only the component of the chosen base point. -/
theorem uOrder_complex_isConnected : IsConnected (orderCx (UOrder P a)) := by
  intro v w
  obtain ⟨p, hp⟩ := isConnected_univCover (X := orderCx P) (x₀ := a) v w
  refine ⟨mapPath uOrderHomInv p, ?_⟩
  simpa only [uOrderHomInv_vertex] using isPath_mapPath uOrderHomInv hp

/-- Actual loops in the lifted-order complex contract, by the inverse of the
constructed cellular comparison with the path-class universal cover. -/
theorem uOrder_complex_simplyConnected : SimplyConnected (orderCx (UOrder P a)) := by
  intro v p hp
  have h := simplyConnected_univCover (X := orderCx P) (x₀ := a) v
    (mapPath uOrderHom p) (isPath_mapPath uOrderHom hp)
  have hi := mapPath_htpy uOrderHomInv h
  change Htpy (orderCx (UOrder P a)) (uOrderHomInv.onV v) (uOrderHomInv.onV v)
    (mapPath uOrderHomInv (mapPath uOrderHom p)) [] at hi
  rw [uOrderHomInv_path p] at hi
  simpa only [uOrderHomInv_vertex] using hi

end FiniteChains.Comb
