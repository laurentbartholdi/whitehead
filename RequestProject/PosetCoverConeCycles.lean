import RequestProject.OrderComparableCollapse
import RequestProject.OrderComparableEdgeFan
import RequestProject.PosetCoverDownTransform

/-! Genuine strict cycle fillings in arbitrary covers of a lower cone. -/
namespace FiniteChains.Comb
universe u
variable {P Q : Type u} [PartialOrder P] [PartialOrder Q] {f : P → Q}

theorem strict_oneCycle_cover_lower_cone (hf : IsPosetCover f) (b : Q)
    (hb : ∀ q, b ≤ q) (c : StrictOrdEdge P →₀ ℤ)
    (hc : bdry1 (strictOrderCx P) c = 0) :
    ∃ d : StrictOrdTri P →₀ ℤ, bdry2 (strictOrderCx P) d = c := by
  let g := hf.downTransform (fun _ => b) hb
  have hgle : ∀ x, g x ≤ x := hf.downTransform_le _ hb
  have he : ∀ {v w : P}, v ≤ w → g v = g w := by
    intro v w hvw
    have hv := hf.downTransform_spec (fun _ => b) hb v
    have hw := hf.downTransform_spec (fun _ => b) hb w
    exact hf.down_inj (hv.1.trans hvw) hw.1 (hv.2.trans hw.2.symm)
  exact ⟨downwardEdgeFan g hgle c, downwardEdgeFan_cycle_boundary g hgle he c hc⟩

theorem strict_twoCycle_cover_lower_cone (hf : IsPosetCover f) (b : Q)
    (hb : ∀ q, b ≤ q) (c : StrictOrdTri P →₀ ℤ)
    (hc : bdry2 (strictOrderCx P) c = 0) :
    ∃ y : StrictOrdTet P →₀ ℤ, strictOrdBoundary3 y = c := by
  let g := hf.downTransform (fun _ => b) hb
  have hg : Monotone g := hf.downTransform_monotone _ (fun _ _ _ => le_refl _) hb
  have hgle : ∀ x, g x ≤ x := hf.downTransform_le _ hb
  have he : ∀ {v w : P}, v ≤ w → g v = g w := by
    intro v w hvw
    have hv := hf.downTransform_spec (fun _ => b) hb v
    have hw := hf.downTransform_spec (fun _ => b) hb w
    exact hf.down_inj (hv.1.trans hvw) hw.1 (hv.2.trans hw.2.symm)
  exact strict_cycle_boundary_of_downward_collapse g hg hgle he c hc

end FiniteChains.Comb
