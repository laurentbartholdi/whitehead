module

public import RequestProject.ChamberZCellular
public import RequestProject.PosetCoverDownTransform
public import RequestProject.PosetCoverRestriction
public import RequestProject.OrderUniversalPosetCover

@[expose] public section

/-! The actual marked-chamber retraction on covering posets. -/
namespace FiniteChains.Davis
open RACG Mirror Comb Nerve
universe u
variable {V : Type u} [DecidableEq V] {A : CommRel V}
  {X : Type u} [PartialOrder X] {M : CayGroup A → Prop} {att : NeSpx A →o X}
  {P : Type u} [PartialOrder P] {f : P → Zpos A X M att}

/-- The actual preimage of a marked chamber in a poset covering is acyclic relative
to the actual preimage of the inserted base. The retraction is constructed by unique
downward interval lifts of the geometric chamber retraction. -/
theorem acyclicRelIn_cover_marked_chamber [Nonempty X] (hf : IsPosetCover f)
    (w : CayGroup A) (hw : M w) :
    AcyclicRelIn (fun p => InZChamber w (f p)) (fun p => InZBase (f p)) := by
  let S : Set (Zpos A X M att) := {z | InZChamber w z}
  let fc := posetCoverRestriction f S
  have hfc : IsPosetCover fc := IsPosetCover.restriction f S hf
  let g : S → S := zChamberRetr (att := att) hw
  have hgle : ∀ q, g q ≤ q := zChamberRetr_le hw
  let ρ := hfc.downTransform g hgle
  have hmono : Monotone ρ := hfc.downTransform_monotone g (zChamberRetr_monotone hw) hgle
  have hρle : ∀ q, ρ q ≤ q := hfc.downTransform_le g hgle
  have hbase : ∀ q, InZBase (f (ρ q).1) := by
    intro q
    have he := congrArg Subtype.val (hfc.downTransform_spec g hgle q).2
    obtain ⟨x, hx⟩ := zChamberRetr_mem hw (fc q)
    have hb : InZBase (g (fc q)).1 := by
      change InZBase (zChamberRetr (att := att) hw (fc q)).1
      rw [hx]
      trivial
    change f (ρ q).1 = (g (fc q)).1 at he
    rw [he]
    exact hb
  have hne : ∃ p : P, InZChamber w (f p) := by
    let x : X := Classical.choice inferInstance
    obtain ⟨p, hp⟩ := hf.surj (zNew (att := att) ⟨w, hw⟩ x)
    refine ⟨p, ?_⟩
    rw [hp]
    rfl
  exact acyclicRelIn_of_retraction hne ρ hmono hρle hbase

/-- In particular this relative chamber retraction is proved on the actual
path-class universal-cover poset, without a supplied retraction premise. -/
theorem acyclicRelIn_uOrder_marked_chamber [Nonempty X]
    (a : Zpos A X M att) (hc : IsConnected (orderCx (Zpos A X M att)))
    (w : CayGroup A) (hw : M w) :
    AcyclicRelIn (fun p : UOrder (Zpos A X M att) a => InZChamber w (uOrderEnd p))
      (fun p => InZBase (uOrderEnd p)) :=
  acyclicRelIn_cover_marked_chamber (uOrderEnd_isPosetCover hc) w hw

end FiniteChains.Davis
