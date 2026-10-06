module

public import RequestProject.RoseCoverBaseCoordinates

@[expose] public section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.PresModel
open Comb
universe u
variable {α P : Type u} [PartialOrder P] (f : P → Rose α) (hf : IsPosetCover f)

/-- The actual incidence from a lifted midpoint to its chosen end. -/
noncomputable def roseCoverMidpointEndEdge (p : roseCoverMidpoints f) (b : Bool) :
    StrictOrdEdge P := hf.strictEdgeLiftFrom (roseMidEdge p.val.2 b) p.val.1 p.property

/-- The actual incidence from a lifted base vertex to the same lifted end. -/
noncomputable def roseCoverMidpointBaseEdge (p : roseCoverMidpoints f) (b : Bool) :
    StrictOrdEdge P := hf.strictEdgeLiftTo (roseBaseEdge p.val.2 b)
      (roseCoverMidpointEndEdge f hf p b).val.2
      (congrArg (fun e : StrictOrdEdge (Rose α) => e.val.2)
        (hf.strictEdgeLiftFrom_projection (roseMidEdge p.val.2 b) p.val.1 p.property))

/-- The genuine four-incidence lift of a rose generator. -/
noncomputable def roseCoverGeneratorChain (p : roseCoverMidpoints f) : StrictOrdEdge P →₀ ℤ :=
  Finsupp.single (roseCoverMidpointBaseEdge f hf p false) 1 -
    Finsupp.single (roseCoverMidpointEndEdge f hf p false) 1 +
    Finsupp.single (roseCoverMidpointEndEdge f hf p true) 1 -
    Finsupp.single (roseCoverMidpointBaseEdge f hf p true) 1

/-- The lifted generator chain has precisely the difference of its actual base endpoints as boundary. -/
theorem roseCoverGeneratorChain_boundary (p : roseCoverMidpoints f) :
    FiniteChains.Comb.bdry1 (strictOrderCx P) (roseCoverGeneratorChain f hf p) =
      Finsupp.single (roseCoverMidpointBaseEdge f hf p true).val.1 1 -
        Finsupp.single (roseCoverMidpointBaseEdge f hf p false).val.1 1 := by
  unfold roseCoverGeneratorChain
  rw [map_sub, map_add, map_sub]
  rw [bdry1_single (X := strictOrderCx P), bdry1_single (X := strictOrderCx P),
    bdry1_single (X := strictOrderCx P), bdry1_single (X := strictOrderCx P)]
  simp only [one_smul]
  change (Finsupp.single (roseCoverMidpointEndEdge f hf p false).val.2 1 -
      Finsupp.single (roseCoverMidpointBaseEdge f hf p false).val.1 1) -
    (Finsupp.single (roseCoverMidpointEndEdge f hf p false).val.2 1 -
      Finsupp.single p.val.1 1) +
    (Finsupp.single (roseCoverMidpointEndEdge f hf p true).val.2 1 -
      Finsupp.single p.val.1 1) -
    (Finsupp.single (roseCoverMidpointEndEdge f hf p true).val.2 1 -
      Finsupp.single (roseCoverMidpointBaseEdge f hf p true).val.1 1) = _
  abel

/-- The selected incidence coordinates of the genuine generator chain are a unit vector. -/
theorem roseCoverGeneratorChain_coordinates (p : roseCoverMidpoints f) :
    roseCoverGeneratorCoordinates f hf (roseCoverGeneratorChain f hf p) =
      Finsupp.single (roseCoverMidpointEdge f hf p) 1 := by
  classical
  ext e
  obtain ⟨i, hi⟩ := e.property
  have hn : ∀ b, roseCoverMidpointBaseEdge f hf p b ≠ e.val := by
    intro b he
    have hp := (hf.strictEdgeLiftTo_projection (roseBaseEdge p.val.2 b)
      (roseCoverMidpointEndEdge f hf p b).val.2 _).symm.trans
        ((congrArg ((strictOrderCxMap f hf.strictMono).onE) he).trans hi)
    have hs := congrArg (fun r : StrictOrdEdge (Rose α) => r.val.1) hp
    cases hs
  have hm : roseCoverMidpointEndEdge f hf p false ≠ e.val := by
    intro he
    have hp := (hf.strictEdgeLiftFrom_projection (roseMidEdge p.val.2 false)
      p.val.1 p.property).symm.trans
        ((congrArg ((strictOrderCxMap f hf.strictMono).onE) he).trans hi)
    have ht := congrArg (fun r : StrictOrdEdge (Rose α) => r.val.2) hp
    exact Bool.noConfusion (Rose.edg.inj ht).2
  change (roseCoverGeneratorChain f hf p) e.val =
    (Finsupp.single (roseCoverMidpointEdge f hf p) 1) e
  unfold roseCoverGeneratorChain
  simp only [Finsupp.sub_apply, Finsupp.add_apply]
  rw [Finsupp.single_eq_of_ne (Ne.symm (hn false)), Finsupp.single_eq_of_ne (Ne.symm hm),
    Finsupp.single_eq_of_ne (Ne.symm (hn true))]
  simp only [sub_zero, zero_add]
  have heq : (roseCoverMidpointEndEdge f hf p true = e.val) ↔
      (roseCoverMidpointEdge f hf p = e) := by
    constructor
    · intro h
      exact Subtype.ext h
    · intro h
      exact congrArg Subtype.val h
  simp only [Finsupp.single_apply, heq]

end FiniteChains.PresModel
