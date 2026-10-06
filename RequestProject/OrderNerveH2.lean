module

public import RequestProject.OrderNormalizationHomotopy

@[expose] public section

namespace FiniteChains.Comb
universe u
variable (P : Type u) [PartialOrder P]

/-- The actual order-nerve three-boundary with codomain its genuine two-cycle module. -/
noncomputable def ordBoundary3Cycles : (OrdTet P →₀ ℤ) →ₗ[ℤ]
    LinearMap.ker (bdry2 (orderCx P)) :=
  (ordBoundary3 (P := P)).codRestrict (LinearMap.ker (bdry2 (orderCx P)))
    (fun y => bdry2_ordBoundary3 y)

/-- Second integral homology of the genuine order nerve, defined by its actual boundaries. -/
abbrev OrderNerveH2 :=
  (LinearMap.ker (bdry2 (orderCx P))) ⧸ LinearMap.range (ordBoundary3Cycles P)

/-- The actual homology class of an actual finite order-nerve two-cycle. -/
noncomputable def orderNerveH2Class (c : OrdTri P →₀ ℤ)
    (hc : bdry2 (orderCx P) c = 0) : OrderNerveH2 P :=
  Submodule.Quotient.mk ⟨c, hc⟩

/-- An actual order-nerve cycle class vanishes exactly when the cycle has an actual finite three-filling. -/
theorem orderNerveH2Class_eq_zero_iff (c : OrdTri P →₀ ℤ)
    (hc : bdry2 (orderCx P) c = 0) :
    orderNerveH2Class P c hc = 0 ↔ ∃ y : OrdTet P →₀ ℤ, ordBoundary3 y = c := by
  rw [orderNerveH2Class, Submodule.Quotient.mk_eq_zero, LinearMap.mem_range]
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨y, congrArg Subtype.val hy⟩
  · rintro ⟨y, hy⟩
    exact ⟨y, Subtype.ext hy⟩

end FiniteChains.Comb
