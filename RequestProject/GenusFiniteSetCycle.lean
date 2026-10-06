module

public import RequestProject.GenusCellularFundamental
public import RequestProject.StrictSimplicialCoordinates
public import RequestProject.GenusChainCollapse

@[expose] public section

/-! The actual oriented genus cycle in the coordinates of the cubical collapse. -/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Davis.Genus
open Comb
variable (q : ℕ) [NeZero q]

/-- The finite-set chain is the image of the explicit nondegenerate polygon cycle. -/
noncomputable def genusFiniteSetChain : Finset (GenusVertex q) →₀ ℤ :=
  @strictTriangleCoordinateChain (GenusVertex q) (GenusVertex q)
    (instPartialOrderSCell (gc q)) inferInstance
    id (genusStrictFundamentalChain q)

theorem genusFiniteSetChain_cycle : simpBdry (fun σ => genusFiniteSetChain q σ) = 0 := by
  exact simpBdry_strictTriangleCoordinateChain id (genus_coordinate_strictMono q)
    (genusStrictFundamentalChain q) (genusStrictFundamentalChain_cycle q)

theorem genusFiniteSetChain_ne_zero : genusFiniteSetChain q ≠ 0 := by
  intro h
  apply genusStrictFundamentalChain_ne_zero q
  apply strictTriangleCoordinateChain_injective id (genus_coordinate_strictMono q)
    Function.injective_id
  simpa only [genusFiniteSetChain, map_zero] using h

theorem genusFiniteSetChain_supported (σ : Finset (GenusVertex q)) (hσ : σ.card ≠ 3) :
    genusFiniteSetChain q σ = 0 :=
  strictTriangleCoordinateChain_eq_zero_of_card id (genus_coordinate_strictMono q)
    (genusStrictFundamentalChain q) σ hσ

theorem genusFiniteSetChain_supported_faces (σ : Finset (GenusVertex q))
    (hσ : σ ∉ (ASC.orderComplex (GenusVertex q)).faces) : genusFiniteSetChain q σ = 0 := by
  apply strictTriangleCoordinateChain_eq_zero_of_not_face id
    (ASC.orderComplex (GenusVertex q)) _ (genusStrictFundamentalChain q) σ hσ
  intro t
  change IsChain (· ≤ ·)
    (↑({t.1.1, t.1.2.1, t.1.2.2} : Finset (GenusVertex q)) : Set (GenusVertex q))
  intro x hx y hy _
  change x ∈ ({t.1.1, t.1.2.1, t.1.2.2} : Finset (GenusVertex q)) at hx
  change y ∈ ({t.1.1, t.1.2.1, t.1.2.2} : Finset (GenusVertex q)) at hy
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  have hab := t.2.1.le
  have hbc := t.2.2.le
  have hac := hab.trans hbc
  rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
  all_goals first
    | exact Or.inl (le_refl _)
    | exact Or.inl hab
    | exact Or.inr hab
    | exact Or.inl hbc
    | exact Or.inr hbc
    | exact Or.inl hac
    | exact Or.inr hac

/-- The constructed geometric collapse kills this actual oriented cut-surface cycle. -/
theorem genusFiniteSetChain_cutSurface_eq_zero :
    CollapseChain.cmap (cubeBdry (V := GenusVertex q)) (genusChainCollapse q)
      (Sum.elim 0 (fun τ => -genusFiniteSetChain q τ)) = 0 :=
  genusChainCollapse_cutSurface_eq_zero q (fun σ => genusFiniteSetChain q σ)
    (genusFiniteSetChain_cycle q) (genusFiniteSetChain_supported q)
    (genusFiniteSetChain_supported_faces q)

/-- The cut cycle bounds the explicit signed sum of three-cubes before collapsing. -/
theorem genusFiniteSetChain_cutSurface_boundary :
    bdryT (cubeChain (fun σ => genusFiniteSetChain q σ), 0) =
      (0, fun σ => -genusFiniteSetChain q σ) :=
  cutSurface_isBoundary (genusFiniteSetChain_cycle q) (genusFiniteSetChain_supported q)

/-- The cut cycle being killed is nonzero, rather than an unspecified or zero witness. -/
theorem genusFiniteSetChain_cutSurface_ne_zero :
    (Sum.elim 0 (fun τ => -genusFiniteSetChain q τ) :
      Cube (GenusVertex q) ⊕ Finset (GenusVertex q) → ℤ) ≠ 0 := by
  intro h
  apply genusFiniteSetChain_ne_zero q
  ext σ
  have he := congrFun h (Sum.inr σ)
  change -genusFiniteSetChain q σ = 0 at he
  exact neg_eq_zero.mp he

end FiniteChains.Davis.Genus
