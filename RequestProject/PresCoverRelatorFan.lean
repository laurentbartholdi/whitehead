import RequestProject.RelatorConeFundamentalChain

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.PresModel
open Comb
universe u
variable {α J P : Type u} [PartialOrder P] (w : J → List (α × Bool))
  (f : P → PresPos w) (hf : IsPosetCover f)

noncomputable def presCoverCircleInclusion (p : PresCoverRelator w f)
    (x : RelatorCircle w p.1.2) : P :=
  ((presCoverConeCircleOrderIso w f hf p.1.1 p.1.2 p.2).symm x).val

theorem presCoverCircleInclusion_strictMono (p : PresCoverRelator w f) :
    StrictMono (presCoverCircleInclusion w f hf p) :=
  fun _ _ h => (presCoverConeCircleOrderIso w f hf p.1.1 p.1.2 p.2).symm.strictMono h

theorem presCoverCircleInclusion_injective (p : PresCoverRelator w f) :
    Function.Injective (presCoverCircleInclusion w f hf p) := by
  intro x y h
  exact (presCoverConeCircleOrderIso w f hf p.1.1 p.1.2 p.2).symm.injective (Subtype.ext h)

theorem presCoverCircleInclusion_lt_apex (p : PresCoverRelator w f)
    (x : RelatorCircle w p.1.2) : presCoverCircleInclusion w f hf p x < p.1.1 :=
  ((presCoverConeCircleOrderIso w f hf p.1.1 p.1.2 p.2).symm x).property

/-- The genuine finite triangle fan at an actual lifted relator apex. -/
noncomputable def presCoverRelatorFan (p : PresCoverRelator w f) : StrictOrdTri P →₀ ℤ :=
  strictTopConeEdgeChain (presCoverCircleInclusion w f hf p)
    (presCoverCircleInclusion_strictMono w f hf p) p.1.1
    (presCoverCircleInclusion_lt_apex w f hf p) (relatorCircleFundamentalChain w p.1.2)

theorem presCoverRelatorFan_boundary (p : PresCoverRelator w f) :
    Comb.bdry2 (strictOrderCx P) (presCoverRelatorFan w f hf p) =
      chain1 (strictOrderCxMap (presCoverCircleInclusion w f hf p)
        (presCoverCircleInclusion_strictMono w f hf p)) (relatorCircleFundamentalChain w p.1.2) :=
  strictTopConeEdgeChain_cycle_boundary _ _ _ _ _
    (relatorCircleFundamentalChain_cycle w p.1.2)

theorem presCoverRelatorFan_first (hpos : ∀ j, 0 < (w j).length)
    (p : PresCoverRelator w f) :
    presCoverRelatorFan w f hf p (presCoverRelatorTriangle w f hf hpos p) = 1 := by
  rw (config := { transparency := .default }) [presCoverRelatorFan, strictTopConeEdgeChain_eq_mapDomain]
  have he := Finsupp.mapDomain_apply_of_injective
    (strictTopConeEdgeTriangle_injective (presCoverCircleInclusion w f hf p)
      (presCoverCircleInclusion_strictMono w f hf p) p.1.1
      (presCoverCircleInclusion_lt_apex w f hf p) (presCoverCircleInclusion_injective w f hf p))
    (relatorCircleFundamentalChain w p.1.2)
    (relatorCircleEdge0 w p.1.2 ⟨0, hpos p.1.2⟩)
  exact he.trans (relatorCircleFundamentalChain_edge0 w p.1.2 _)

/-- A genuine lifted fan has precisely the corresponding single relator coordinate. -/
theorem presCoverRelatorChain_fan (hpos : ∀ j, 0 < (w j).length)
    (p : PresCoverRelator w f) :
    presCoverRelatorChain w f hf hpos (presCoverRelatorFan w f hf p) = Finsupp.single p 1 := by
  classical
  ext q
  rw (config := { transparency := .default }) [presCoverRelatorChain_apply]
  by_cases h : q = p
  · subst q
    rw (config := { transparency := .default }) [presCoverRelatorFan_first]
    simp
  · have hv : q.1.1 ≠ p.1.1 := by
      intro he
      apply h
      apply Subtype.ext
      apply Prod.ext he
      apply Sum.inr_injective
      exact q.2.symm.trans ((congrArg f he).trans p.2)
    have hz := strictTopConeEdgeChain_eq_zero_off_top (presCoverCircleInclusion w f hf p)
      (presCoverCircleInclusion_strictMono w f hf p) p.1.1
      (presCoverCircleInclusion_lt_apex w f hf p) (relatorCircleFundamentalChain w p.1.2)
      (presCoverRelatorTriangle w f hf hpos q) hv
    rw (config := { transparency := .default }) [show presCoverRelatorFan w f hf p (presCoverRelatorTriangle w f hf hpos q) = 0 from hz]
    simp [h]

/-- A genuine integer-linear realization of finite lifted-relator chains by actual cone fans. -/
noncomputable def presCoverRelatorFanChain :
    (PresCoverRelator w f →₀ ℤ) →ₗ[ℤ] (StrictOrdTri P →₀ ℤ) :=
  Finsupp.linearCombination ℤ (presCoverRelatorFan w f hf)

/-- Actual finite cone-fan realization is a section of actual relator coordinates. -/
theorem presCoverRelatorChain_fanChain (hpos : ∀ j, 0 < (w j).length)
    (c : PresCoverRelator w f →₀ ℤ) :
    presCoverRelatorChain w f hf hpos (presCoverRelatorFanChain w f hf c) = c := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => rw (config := { transparency := .default }) [map_add, map_add, hc, hd]
  | single p n =>
    rw (config := { transparency := .default }) [presCoverRelatorFanChain, Finsupp.linearCombination_single, map_smul,
      presCoverRelatorChain_fan]
    simp

/-- Actual finite relator chains have distinct actual cone-fan realizations. -/
theorem presCoverRelatorFanChain_injective (hpos : ∀ j, 0 < (w j).length) :
    Function.Injective (presCoverRelatorFanChain w f hf) := by
  intro c d he
  have h := congrArg (presCoverRelatorChain w f hf hpos) he
  simpa only [presCoverRelatorChain_fanChain] using h

end FiniteChains.PresModel
