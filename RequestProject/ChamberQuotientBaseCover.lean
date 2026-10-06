module

public import RequestProject.ChamberQuotientCycleGeneration
public import RequestProject.PosetCoverTargetIso
public import RequestProject.UniversalCoverPi1Injection

@[expose] public section

/-! The actual lifted inserted base covers the original base poset. -/
namespace FiniteChains.Davis
open RACG Mirror Comb
universe u
variable {V : Type u} [DecidableEq V] [Fintype V] {A : CommRel V}
  {X : Type u} [PartialOrder X] {att : NeSpx A →o X}

noncomputable def qBaseOrderIso : {q : Qpos A X att // InQBase q} ≃o X where
  toFun q := Classical.choose q.2
  invFun x := ⟨qNew x, ⟨x, rfl⟩⟩
  left_inv q := Subtype.ext (Classical.choose_spec q.2)
  right_inv x := Sum.inr.inj (Classical.choose_spec (show InQBase (qNew x) from ⟨x, rfl⟩))
  map_rel_iff' {q r} := by
    change Classical.choose q.2 ≤ Classical.choose r.2 ↔ q.1 ≤ r.1
    have h : qNew (A := A) (att := att) (Classical.choose q.2) ≤
        qNew (A := A) (att := att) (Classical.choose r.2) ↔ q.1 ≤ r.1 := by
      rw [Classical.choose_spec q.2, Classical.choose_spec r.2]
    exact h

abbrev QLiftedBase (a : Qpos A X att) :=
  {p : UOrder (Qpos A X att) a // InQBase (uOrderEnd p)}

noncomputable def qBaseCoverEnd (a : Qpos A X att) (p : QLiftedBase a) : X :=
  qBaseOrderIso ⟨uOrderEnd p.1, p.2⟩

omit [Fintype V] in
theorem qBaseCoverEnd_isPosetCover (a : Qpos A X att)
    (hc : IsConnected (orderCx (Qpos A X att))) : IsPosetCover (qBaseCoverEnd a) := by
  let S : Set (Qpos A X att) := {q | InQBase q}
  have h := IsPosetCover.restriction (uOrderEnd (P := Qpos A X att) (a := a)) S
    (uOrderEnd_isPosetCover hc)
  exact h.postcompose_orderIso qBaseOrderIso

omit [Fintype V] in
theorem qBaseCoverEnd_spec (a : Qpos A X att) (p : QLiftedBase a) :
    qNew (qBaseCoverEnd a p) = uOrderEnd p.1 := Classical.choose_spec p.2

theorem qBase_universal_vertices_injective (x : X) :
    Function.Injective (univLiftV x
      (orderCxMap (qNew (A := A) (X := X) (att := att)) qNew_monotone)) := by
  apply univLiftV_injective_of_pi1Map_injective
  · intro a b h
    exact Sum.inr.inj h
  · exact pi1Map_qNew_injective x

end FiniteChains.Davis
