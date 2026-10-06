import RequestProject.PosetCoverUpTransform
import RequestProject.StrictTopLinkChains

namespace FiniteChains.Comb
universe u
variable {P Q : Type u} [PartialOrder P] [PartialOrder Q] {f : P → Q}
def strictBelowCongr {a b : P} (h : a = b) : StrictBelow a ≃o StrictBelow b := by
  cases h
  exact OrderIso.refl _

namespace IsPosetCover
variable (hf : IsPosetCover f)
include hf

/-- The order in a common lower interval is reflected by an actual covering projection. -/
theorem le_of_le_below {a b v : P} (ha : a ≤ v) (hb : b ≤ v) (h : f a ≤ f b) : a ≤ b := by
  obtain ⟨c, ⟨hcb, hfc⟩, _⟩ := hf.down b (f a) h
  have hc : c = a := hf.down_inj (hcb.trans hb) ha hfc
  exact hc ▸ hcb

noncomputable def lowerIntervalLift (v : P) (q : StrictBelow (f v)) : StrictBelow v := by
  let a := Classical.choose (hf.down v q.1 q.2.le)
  have hs : a ≤ v ∧ f a = q.1 := (Classical.choose_spec (hf.down v q.1 q.2.le)).1
  exact ⟨a, lt_of_le_of_ne hs.1 (by
    intro he
    exact (ne_of_lt q.2) (hs.2.symm.trans (congrArg f he)))⟩

theorem lowerIntervalLift_projection (v : P) (q : StrictBelow (f v)) :
    f (hf.lowerIntervalLift v q).1 = q.1 :=
  (Classical.choose_spec (hf.down v q.1 q.2.le)).1.2

/-- Genuine lower intervals of a poset cover are isomorphic to their projected intervals. -/
noncomputable def lowerIntervalOrderIso (v : P) : StrictBelow v ≃o StrictBelow (f v) where
  toFun p := ⟨f p.1, hf.strictMono p.2⟩
  invFun := hf.lowerIntervalLift v
  left_inv p := Subtype.ext (hf.down_inj (hf.lowerIntervalLift v _).2.le p.2.le
    (hf.lowerIntervalLift_projection v _))
  right_inv q := Subtype.ext (hf.lowerIntervalLift_projection v q)
  map_rel_iff' {a b} := ⟨fun h => hf.le_of_le_below a.2.le b.2.le h, fun h => hf.mono h⟩

end IsPosetCover
end FiniteChains.Comb
