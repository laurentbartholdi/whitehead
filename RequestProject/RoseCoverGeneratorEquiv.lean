module

public import RequestProject.RoseCoverCycleCoordinates

@[expose] public section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.PresModel
open Comb
universe u
variable {α P : Type u} [PartialOrder P] (f : P → Rose α) (hf : IsPosetCover f)

/-- Actual lifted midpoint vertices, with their actual generator label. -/
def roseCoverMidpoints := {p : P × α // f p.1 = Rose.mid p.2}

/-- The actual positive selected incidence leaving a lifted midpoint. -/
noncomputable def roseCoverMidpointEdge (p : roseCoverMidpoints f) :
    roseCoverGeneratorEdges f hf :=
  ⟨hf.strictEdgeLiftFrom (roseMidEdge p.val.2 true) p.val.1 p.property,
    p.val.2, hf.strictEdgeLiftFrom_projection _ _ _⟩

theorem roseCoverMidpointEdge_injective : Function.Injective (roseCoverMidpointEdge f hf) := by
  intro p q h
  have he := congrArg Subtype.val h
  apply Subtype.ext
  apply Prod.ext
  · exact congrArg (fun e : StrictOrdEdge P => e.val.1) he
  · have hp := congrArg ((strictOrderCxMap f hf.strictMono).onE) he
    change (strictOrderCxMap f hf.strictMono).onE
      (hf.strictEdgeLiftFrom (roseMidEdge p.val.2 true) p.val.1 p.property) =
      (strictOrderCxMap f hf.strictMono).onE
        (hf.strictEdgeLiftFrom (roseMidEdge q.val.2 true) q.val.1 q.property) at hp
    rw [hf.strictEdgeLiftFrom_projection, hf.strictEdgeLiftFrom_projection] at hp
    exact Rose.mid.inj (congrArg (fun e : StrictOrdEdge (Rose α) => e.val.1) hp)

theorem roseCoverMidpointEdge_surjective : Function.Surjective (roseCoverMidpointEdge f hf) := by
  rintro ⟨e, i, he⟩
  have hv : f e.val.1 = Rose.mid i :=
    congrArg (fun r : StrictOrdEdge (Rose α) => r.val.1) he
  refine ⟨⟨(e.val.1, i), hv⟩, ?_⟩
  apply Subtype.ext
  exact (hf.strictEdgeLiftFrom_unique (roseMidEdge i true) e.val.1 hv e he rfl).symm

/-- A proved equivalence between actual midpoint vertices and selected actual incidence edges. -/
noncomputable def roseCoverMidpointEdgeEquiv :
    roseCoverMidpoints f ≃ roseCoverGeneratorEdges f hf :=
  Equiv.ofBijective (roseCoverMidpointEdge f hf)
    ⟨roseCoverMidpointEdge_injective f hf, roseCoverMidpointEdge_surjective f hf⟩

/-- Finite generator coordinates indexed by actual lifted midpoint vertices. -/
noncomputable def roseCoverMidpointCoordinates :
    (StrictOrdEdge P →₀ ℤ) →ₗ[ℤ] (roseCoverMidpoints f →₀ ℤ) :=
  (Finsupp.domLCongr (R := ℤ) (M := ℤ) (roseCoverMidpointEdgeEquiv f hf).symm).toLinearMap.comp
    (roseCoverGeneratorCoordinates f hf)

/-- Actual midpoint coordinates remain injective on genuine one-cycles. -/
theorem roseCoverMidpointCoordinates_cycle_injective :
    Function.Injective ((roseCoverMidpointCoordinates f hf).comp
      (LinearMap.ker (FiniteChains.Comb.bdry1 (strictOrderCx P))).subtype) := by
  intro c d h
  apply roseCoverGeneratorCoordinates_cycle_injective f hf
  apply (Finsupp.domLCongr (R := ℤ) (M := ℤ) (roseCoverMidpointEdgeEquiv f hf).symm).injective
  exact h

end FiniteChains.PresModel
