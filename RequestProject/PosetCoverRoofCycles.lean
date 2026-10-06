import RequestProject.PosetCoverRoofTransform
import RequestProject.OrderComparableCycleHomotopy
import RequestProject.OrderComparableOneHomotopy

/-! Finite positive-degree fillings for covered posets with a two-leg contraction. -/
namespace FiniteChains.Comb
universe u
variable {P Q : Type u} [PartialOrder P] [PartialOrder Q] {f : P → Q}

theorem strict_oneCycle_cover_roof (hf : IsPosetCover f) (g : Q → Q)
    (hmono : Monotone g) (hg : ∀ q, g q ≤ q) (b : Q) (hb : ∀ q, g q ≤ b)
    (c : StrictOrdEdge P →₀ ℤ) (hc : bdry1 (strictOrderCx P) c = 0) :
    ∃ y : StrictOrdTri P →₀ ℤ, bdry2 (strictOrderCx P) y = c := by
  exact strict_oneCycle_boundary_of_roof_collapse
    (hf.downTransform g hg) (hf.roofTransform g hg b hb)
    (hf.downTransform_monotone g hmono hg)
    (hf.roofTransform_monotone g hg b hb hmono)
    (hf.downTransform_le g hg)
    (fun a => (hf.roofTransform_spec g hg b hb a).1)
    (fun {_ _} h => hf.roofTransform_comparable_equal g hg b hb hmono h) c hc

theorem strict_twoCycle_cover_roof (hf : IsPosetCover f) (g : Q → Q)
    (hmono : Monotone g) (hg : ∀ q, g q ≤ q) (b : Q) (hb : ∀ q, g q ≤ b)
    (c : StrictOrdTri P →₀ ℤ) (hc : bdry2 (strictOrderCx P) c = 0) :
    ∃ y : StrictOrdTet P →₀ ℤ, strictOrdBoundary3 y = c := by
  exact strict_cycle_boundary_of_roof_collapse
    (hf.downTransform g hg) (hf.roofTransform g hg b hb)
    (hf.downTransform_monotone g hmono hg)
    (hf.roofTransform_monotone g hg b hb hmono)
    (hf.downTransform_le g hg)
    (fun a => (hf.roofTransform_spec g hg b hb a).1)
    (fun {_ _} h => hf.roofTransform_comparable_equal g hg b hb hmono h) c hc

end FiniteChains.Comb
