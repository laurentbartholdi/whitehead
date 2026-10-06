module

public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Topology.ContinuousMap.Basic

@[expose] public section

/-! The bundled continuous map underlying a homeomorphism. -/

namespace Homeomorph

abbrev toContinuousMap {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) : C(X, Y) := ⟨e, e.continuous⟩

end Homeomorph
