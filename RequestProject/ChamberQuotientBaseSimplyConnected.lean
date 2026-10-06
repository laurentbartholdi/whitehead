module

public import RequestProject.ChamberQuotientBaseCover
public import RequestProject.OrderUniversalPosetConnected

@[expose] public section

/-! Each actual lifted base component is simply connected, proved from the
genuine covering and the proved injection of the base fundamental group. -/
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Davis
open RACG Mirror Comb
universe u
variable {V : Type u} [DecidableEq V] [Fintype V] {A : CommRel V}
  {X : Type u} [PartialOrder X] {att : NeSpx A →o X}

omit [Fintype V] in
theorem qBaseCover_path_projection (a : Qpos A X att)
    (hc : IsConnected (orderCx (Qpos A X att)))
    (l : List ((orderCx (QLiftedBase a)).E × Bool)) :
    mapPath (orderCxMap (qNew (A := A) (X := X) (att := att)) qNew_monotone)
      (mapPath (orderCxMap (qBaseCoverEnd a) (qBaseCoverEnd_isPosetCover a hc).mono) l) =
    mapPath (orderCxMap (uOrderEnd (P := Qpos A X att) (a := a)) uOrderEnd_monotone)
      (mapPath (orderCxMap (Subtype.val : QLiftedBase a → UOrder (Qpos A X att) a)
        (fun _ _ h => h)) l) := by
  induction l with
  | nil => rfl
  | cons e l ih =>
    simp only [mapPath, List.map_cons] at ih ⊢
    rw (config := { transparency := .default }) [ih]
    congr 1
    apply Prod.ext
    · apply Subtype.ext
      exact Prod.ext (qBaseCoverEnd_spec a e.1.1.1) (qBaseCoverEnd_spec a e.1.1.2)
    · rfl

/-- All edge loops of the actual full lifted base are null-homotopic. Its
different components are not identified with one another. -/
theorem qLiftedBase_simplyConnected (a : Qpos A X att)
    (hc : IsConnected (orderCx (Qpos A X att))) :
    SimplyConnected (orderCx (QLiftedBase a)) := by
  let beta := orderCxMap (qBaseCoverEnd a) (qBaseCoverEnd_isPosetCover a hc).mono
  have hcov : IsCovering beta := isCovering_orderCxMap (qBaseCoverEnd_isPosetCover a hc)
  let incl := orderCxMap (Subtype.val : QLiftedBase a → UOrder (Qpos A X att) a)
    (fun _ _ h => h)
  let proj := orderCxMap (uOrderEnd (P := Qpos A X att) (a := a)) uOrderEnd_monotone
  intro b p hp
  have hi := uOrder_complex_simplyConnected (P := Qpos A X att) (a := a)
    b.1 (mapPath incl p) (isPath_mapPath incl hp)
  have hnull := mapPath_htpy proj hi
  have hq : Htpy (orderCx (Qpos A X att)) (qNew (A := A) (att := att) (qBaseCoverEnd (X := X) a b))
      (qNew (A := A) (att := att) (qBaseCoverEnd (X := X) a b))
      (mapPath (orderCxMap (qNew (A := A) (X := X) (att := att)) qNew_monotone)
        (mapPath beta p)) [] := by
    rw (config := { transparency := .default }) [qBaseCover_path_projection a hc, qBaseCoverEnd_spec]
    exact hnull
  let l : Loop (orderCx X) (qBaseCoverEnd (X := X) a b) := ⟨mapPath beta p, isPath_mapPath beta hp⟩
  have hcl : Pi1.mk l = 1 := by
    apply pi1Map_qNew_injective (A := A) (att := att) (qBaseCoverEnd (X := X) a b)
    rw (config := { transparency := .default }) [map_one]
    exact Quotient.sound hq
  have hl : Htpy (orderCx X) (qBaseCoverEnd (X := X) a b) (qBaseCoverEnd (X := X) a b)
      (mapPath beta p) [] := Quotient.exact hcl
  obtain ⟨m, _, hmap, hpm⟩ := lift_htpy hcov hp hl
  have hm : m = [] := List.map_eq_nil_iff.mp hmap
  rwa [hm] at hpm

end FiniteChains.Davis
