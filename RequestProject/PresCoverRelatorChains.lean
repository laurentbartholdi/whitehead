import RequestProject.PresCoverCycleCoordinates

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.PresModel
open Comb
universe u
variable {α J P : Type u} [PartialOrder P] (w : J → List (α × Bool))
  (f : P → PresPos w) (hf : IsPosetCover f) (hpos : ∀ j, 0 < (w j).length)

/-- Actual lifted relator apices, with their actual relator label. -/
def PresCoverRelator := {p : P × J // f p.1 = apexOf w p.2}

/-- The distinguished actual cone triangle over the first left attaching-circle incidence. -/
noncomputable def presCoverRelatorTriangle (p : PresCoverRelator w f) : StrictOrdTri P :=
  strictConeTriangle p.1.1
    ((strictOrderEdgeEquiv
      (presCoverConeCircleOrderIso w f hf p.1.1 p.1.2 p.2)).symm
      (relatorCircleEdge0 w p.1.2 ⟨0, hpos p.1.2⟩))

theorem presCoverRelatorTriangle_injective :
    Function.Injective (presCoverRelatorTriangle w f hf hpos) := by
  intro p q he
  have hv : p.1.1 = q.1.1 := congrArg (fun t : StrictOrdTri P => t.1.2.2) he
  have hj : p.1.2 = q.1.2 := by
    apply Sum.inr_injective
    exact p.2.symm.trans ((congrArg f hv).trans q.2)
  apply Subtype.ext
  exact Prod.ext hv hj

/-- A genuine finite triangle chain yields a genuine finitely supported relator chain. -/
noncomputable def presCoverRelatorChain :
    (StrictOrdTri P →₀ ℤ) →ₗ[ℤ] (PresCoverRelator w f →₀ ℤ) :=
  (Finsupp.comapDomain.addMonoidHom
    (presCoverRelatorTriangle_injective w f hf hpos)).toIntLinearMap

theorem presCoverRelatorChain_apply (c : StrictOrdTri P →₀ ℤ)
    (p : PresCoverRelator w f) :
    presCoverRelatorChain w f hf hpos c p = c (presCoverRelatorTriangle w f hf hpos p) := rfl

theorem presCoverRelatorChain_circle (c : StrictOrdTri P →₀ ℤ)
    (p : PresCoverRelator w f) :
    presCoverRelatorChain w f hf hpos c p =
      presCoverConeCircleChain w f hf p.1.1 p.1.2 p.2 c
        (relatorCircleEdge0 w p.1.2 ⟨0, hpos p.1.2⟩) := by
  let e := strictOrderEdgeEquiv (presCoverConeCircleOrderIso w f hf p.1.1 p.1.2 p.2)
  have he := presCoverConeCircleChain_apply w f hf p.1.1 p.1.2 p.2 c
    (e.symm (relatorCircleEdge0 w p.1.2 ⟨0, hpos p.1.2⟩))
  change _ = c (presCoverRelatorTriangle w f hf hpos p) at he
  rw [presCoverRelatorChain_apply]
  rw [← he]
  change presCoverConeCircleChain w f hf p.1.1 p.1.2 p.2 c
    (e (e.symm (relatorCircleEdge0 w p.1.2 ⟨0, hpos p.1.2⟩))) = _
  rw [e.apply_symm_apply]

/-- The actual relator coordinates detect genuine two-cycles. -/
theorem presCoverRelatorChain_cycle_injective (c d : StrictOrdTri P →₀ ℤ)
    (hc : Comb.bdry2 (strictOrderCx P) c = 0)
    (hd : Comb.bdry2 (strictOrderCx P) d = 0)
    (he : presCoverRelatorChain w f hf hpos c = presCoverRelatorChain w f hf hpos d) :
    c = d := by
  apply presCover_cycles_eq_of_first_coefficients w f hf hpos c d hc hd
  intro v j hv
  have h := congrArg (fun z => z (⟨(v, j), hv⟩ : PresCoverRelator w f)) he
  simpa only [presCoverRelatorChain_circle] using h

/-- The genuine strict two-cycle module embeds linearly in actual lifted-relator chains. -/
noncomputable def presCoverCycleRelatorLinear :
    LinearMap.ker (Comb.bdry2 (strictOrderCx P)) →ₗ[ℤ] (PresCoverRelator w f →₀ ℤ) :=
  (presCoverRelatorChain w f hf hpos).comp
    (LinearMap.ker (Comb.bdry2 (strictOrderCx P))).subtype

theorem presCoverCycleRelatorLinear_injective :
    Function.Injective (presCoverCycleRelatorLinear w f hf hpos) := by
  intro c d he
  apply Subtype.ext
  exact presCoverRelatorChain_cycle_injective w f hf hpos c.val d.val
    (LinearMap.mem_ker.mp c.property) (LinearMap.mem_ker.mp d.property) he

end FiniteChains.PresModel
