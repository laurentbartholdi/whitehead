module

public import RequestProject.OrderConstructionPartialOrder
public import RequestProject.PosetCoverRestriction
public import RequestProject.PosetCoverTargetIso

@[expose] public section

namespace FiniteChains.Comb
universe u
variable {P T R : Type u} [PartialOrder P] [PartialOrder R] {S : T → P → Prop}

def coneAdjBaseSet : Set (ConeAdj S) := Set.range (ConeAdj.inc (S := S))

theorem coneAdjBaseSet_down_closed {p q : ConeAdj S}
    (hq : q ∈ coneAdjBaseSet) (hpq : p ≤ q) : p ∈ coneAdjBaseSet := by
  obtain ⟨r, rfl⟩ := hq
  cases p with
  | inl p => exact ⟨p, rfl⟩
  | inr t => exact hpq.elim

noncomputable def coneAdjBaseOrderIso : coneAdjBaseSet (S := S) ≃o P where
  toFun q := Classical.choose q.2
  invFun p := ⟨ConeAdj.inc p, ⟨p, rfl⟩⟩
  left_inv q := Subtype.ext (Classical.choose_spec q.2)
  right_inv p := Sum.inl.inj (Classical.choose_spec
    (show ConeAdj.inc (S := S) p ∈ coneAdjBaseSet from ⟨p, rfl⟩))
  map_rel_iff' {q r} := by
    change Classical.choose q.2 ≤ Classical.choose r.2 ↔ q.1 ≤ r.1
    have h : ConeAdj.inc (S := S) (Classical.choose q.2) ≤
        ConeAdj.inc (S := S) (Classical.choose r.2) ↔ q.1 ≤ r.1 := by
      rw [Classical.choose_spec q.2, Classical.choose_spec r.2]
    exact h

noncomputable def coneAdjCoverBaseEnd (f : R → ConeAdj S) :
    {r : R // f r ∈ coneAdjBaseSet} → P :=
  fun r => coneAdjBaseOrderIso ⟨f r.1, r.2⟩

theorem coneAdjCoverBaseEnd_isPosetCover (f : R → ConeAdj S) (hf : IsPosetCover f) :
    IsPosetCover (coneAdjCoverBaseEnd f) :=
  (hf.restriction f coneAdjBaseSet).postcompose_orderIso coneAdjBaseOrderIso

omit [PartialOrder R] in
theorem coneAdjCoverBaseEnd_spec (f : R → ConeAdj S)
    (r : {r : R // f r ∈ coneAdjBaseSet}) :
    ConeAdj.inc (coneAdjCoverBaseEnd f r) = f r.1 := Classical.choose_spec r.2

end FiniteChains.Comb
