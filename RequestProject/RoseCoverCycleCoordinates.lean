import RequestProject.RoseCoverBoundary

namespace FiniteChains.PresModel
open Comb
universe u
variable {α P : Type u} [PartialOrder P] (f : P → Rose α) (hf : IsPosetCover f)

/-- Actual incidence edges over the positive selected half of each rose generator. -/
def roseCoverGeneratorEdges : Set (StrictOrdEdge P) :=
  {e | ∃ i, (strictOrderCxMap f hf.strictMono).onE e = roseMidEdge i true}

/-- Restrict the actual finite chain to its selected generator incidences. -/
noncomputable def roseCoverGeneratorCoordinates :
    (StrictOrdEdge P →₀ ℤ) →ₗ[ℤ] (roseCoverGeneratorEdges f hf →₀ ℤ) :=
  Finsupp.lsubtypeDomain (roseCoverGeneratorEdges f hf)

@[simp] theorem roseCoverGeneratorCoordinates_apply (c : StrictOrdEdge P →₀ ℤ)
    (e : roseCoverGeneratorEdges f hf) : roseCoverGeneratorCoordinates f hf c e = c e.val := rfl

/-- Selected generator coordinates are injective on the actual kernel of the boundary. -/
theorem roseCoverGeneratorCoordinates_cycle_injective :
    Function.Injective ((roseCoverGeneratorCoordinates f hf).comp
      (LinearMap.ker (FiniteChains.Comb.bdry1 (strictOrderCx P))).subtype) := by
  intro c d h
  apply Subtype.ext
  apply roseCover_cycle_ext f hf c.val d.val c.property d.property
  intro e i he
  exact congrArg (fun z : roseCoverGeneratorEdges f hf →₀ ℤ => z ⟨e, i, he⟩) h

end FiniteChains.PresModel
