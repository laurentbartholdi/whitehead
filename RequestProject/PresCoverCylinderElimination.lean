import RequestProject.PresCylinderCoverCycles
import RequestProject.ConeAdjBaseCover
import RequestProject.StrictSubposetChains

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.PresModel
open Comb
universe u
variable {α J P : Type u} [PartialOrder P] (w : J → List (α × Bool))
  (f : P → PresPos w) (hf : IsPosetCover f)
include hf

/-- The actual preimage of the cylinder has no strict two-cycles. -/
theorem presCover_cylinder_preimage_cycle_zero
    (c : StrictOrdTri {p : P // f p ∈ coneAdjBaseSet (S := circSet w)} →₀ ℤ)
    (hc : Comb.bdry2
      (strictOrderCx {p : P // f p ∈ coneAdjBaseSet (S := circSet w)}) c = 0) : c = 0 :=
  cylinderCover_two_cycle_zero w (coneAdjCoverBaseEnd_isPosetCover f hf) c hc

/-- A genuine presentation-cover cycle whose triangles avoid the relator cone
vertices is zero. Thus relator-cone triangles detect every actual two-cycle. -/
theorem presCover_cycle_zero_of_cylinder_support (c : StrictOrdTri P →₀ ℤ)
    (hc : Comb.bdry2 (strictOrderCx P) c = 0)
    (hs : ∀ t ∈ c.support, f t.1.2.2 ∈ coneAdjBaseSet (S := circSet w)) : c = 0 := by
  let S : Set P := {p | f p ∈ coneAdjBaseSet (S := circSet w)}
  have hsup : ∀ t ∈ c.support, t.1.1 ∈ S ∧ t.1.2.1 ∈ S ∧ t.1.2.2 ∈ S := by
    intro t ht
    have hlast := hs t ht
    exact ⟨coneAdjBaseSet_down_closed hlast (hf.mono (t.2.1.le.trans t.2.2.le)),
      coneAdjBaseSet_down_closed hlast (hf.mono t.2.2.le), hlast⟩
  obtain ⟨d, hd, hdc⟩ := exists_strictSubposet_cycle S c hsup hc
  have hz : d = 0 := presCover_cylinder_preimage_cycle_zero w f hf d hdc
  rw (config := { transparency := .default }) [hz, map_zero] at hd
  exact hd.symm

/-- Equality of relator-cone triangle coefficients detects equality of actual cover cycles. -/
theorem presCover_cycles_eq_of_cone_coefficients (c d : StrictOrdTri P →₀ ℤ)
    (hc : Comb.bdry2 (strictOrderCx P) c = 0)
    (hd : Comb.bdry2 (strictOrderCx P) d = 0)
    (he : ∀ t, f t.1.2.2 ∉ coneAdjBaseSet (S := circSet w) → c t = d t) : c = d := by
  classical
  have hcd : Comb.bdry2 (strictOrderCx P) (c - d) = 0 := by
    rw (config := { transparency := .default }) [map_sub, hc, hd, sub_self]
  have hs : ∀ t ∈ (c - d).support, f t.1.2.2 ∈ coneAdjBaseSet (S := circSet w) := by
    intro t ht
    by_contra hn
    have hz : (c - d) t = 0 := by simp only [Finsupp.sub_apply, he t hn, sub_self]
    exact (Finsupp.mem_support_iff.mp ht) hz
  exact sub_eq_zero.mp (presCover_cycle_zero_of_cylinder_support w f hf (c - d) hcd hs)

end FiniteChains.PresModel
