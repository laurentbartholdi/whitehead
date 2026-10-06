module

public import RequestProject.GenusSpineFamilyGeneration
public import RequestProject.GenusReceivedSpineCover

@[expose] public section

/-! Exact sheet and marking coordinates of the normalized reference after
arbitrary substitutions. Pending final Lean verification. -/
noncomputable section
open scoped Classical

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb.ReceivedTree
universe u
variable {G H E : Type u} [Group G] [Group H] (φ : G →* H)

/-- Changing the receiving group retains each cell coordinate and pushes
forward its full group-ring coefficient, including coincident sheets. -/
theorem cellCoefficient_mapSheets (e : E) (c : (G × E) →₀ ℤ) :
    cellCoefficient e (Finsupp.mapDomain (fun x : G × E => (φ x.1, x.2)) c) =
      MonoidAlgebra.mapDomainRingHom ℤ φ (cellCoefficient e c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [Finsupp.mapDomain_add, map_add, hc, hd]
  | single x n =>
    obtain ⟨g, j⟩ := x
    rw (config := { transparency := .default }) [Finsupp.mapDomain_single, cellCoefficient_single, cellCoefficient_single]
    by_cases hj : j = e
    · rw [if_pos hj, if_pos hj]
      change MonoidAlgebra.single (φ g) n = MonoidAlgebra.mapDomain φ (MonoidAlgebra.single g n)
      exact MonoidAlgebra.mapDomain_single.symm
    · rw [if_neg hj, if_neg hj, map_zero]

theorem cellCoordinates_symm_mapSheets [Fintype E] (v : E → MonoidAlgebra ℤ G) :
    (cellCoordinates E).symm (fun e => MonoidAlgebra.mapDomainRingHom ℤ φ (v e)) =
      Finsupp.mapDomain (fun x : G × E => (φ x.1, x.2)) ((cellCoordinates E).symm v) := by
  apply (cellCoordinates E).injective
  funext e
  rw (config := { transparency := .default }) [LinearEquiv.apply_symm_apply, ← cellCoefficient_eq_coordinates,
    cellCoefficient_mapSheets, cellCoefficient_coordinates_symm]

end FiniteChains.Comb.ReceivedTree

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb BlockFamily
variable {α Jr S : Type} (ρ : Jr ⊕ S → FreeGroup α)
  (q : S → ℕ) [∀ s, NeZero (q s)] (u : ∀ s, Fin (q s) × Bool → FreeGroup α)

theorem finiteSpineFamilyFilling_named_coeff (s : S) (m : NamedSpineRel (q s)) :
    finiteSpineFamilyFilling ρ q u s m =
      MonoidAlgebra.mapDomainRingHom ℤ (familySpineHom ρ q u s)
        (normalizedNamedSpineVector (q s) (normalizedSpineReference (q s)) m) := by
  change MonoidAlgebra.mapDomainRingHom ℤ (finiteSpineFamilyMarkedHom ρ q u s)
    (markedSpineFilling (q s) m) = _
  rw (config := { transparency := .default }) [markedSpineFilling_named_coeff, BlockMor.mapDomainRingHom_comp']
  rfl

theorem finiteSpineFamilyFilling_faceChain (s : S) :
    receivedSpineFaceChain ρ q u s (finiteSpineFamilyFilling ρ q u s) =
      Finsupp.mapDomain
        (fun x : PresGroup (namedSpinePresentation (q s)) × SpinePresentationRel (q s) =>
          (familySpineHom ρ q u s x.1, x.2)) (normalizedSpineReference (q s)) := by
  apply (ReceivedTree.cellCoordinates (SpinePresentationRel (q s))).injective
  funext j
  rw (config := { transparency := .default }) [← ReceivedTree.cellCoefficient_eq_coordinates,
    receivedSpineFaceChain_coefficient, ← ReceivedTree.cellCoefficient_eq_coordinates,
    ReceivedTree.cellCoefficient_mapSheets, finiteSpineFamilyFilling_named_coeff]
  rfl

theorem finiteSpineFamilyFilling_markingChain (s : S) :
    (ReceivedTree.cellCoordinates (Fin (q s) × Bool)).symm
      (fun i => finiteSpineFamilyFilling ρ q u s (Sum.inr i)) =
      Finsupp.mapDomain
        (fun x : PresGroup (namedSpinePresentation (q s)) × (Fin (q s) × Bool) =>
          (familySpineHom ρ q u s x.1, x.2)) (universalReferenceMarkingCoefficients (q s)) := by
  simp only [finiteSpineFamilyFilling_named_coeff, normalizedNamedSpineVector, Sum.elim_inr]
  exact ReceivedTree.cellCoordinates_symm_mapSheets (familySpineHom ρ q u s)
    (namedSpineSurfaceMarkingCoefficient (q s))

/-- The individual factor is the same specialization at the singleton
index, including every actual group coefficient. -/
theorem finiteSpineIndividualFilling_named_coeff (s : S) (m : NamedSpineRel (q s)) :
    finiteSpineIndividualFilling ρ q u s m =
      MonoidAlgebra.mapDomainRingHom ℤ
        (familySpineHom (oneRel ρ s) (fun _ : PUnit.{1} => q s) (fun _ => u s) PUnit.unit)
        (normalizedNamedSpineVector (q s) (normalizedSpineReference (q s)) m) := by
  exact finiteSpineFamilyFilling_named_coeff (oneRel ρ s)
    (fun _ : PUnit.{1} => q s) (fun _ => u s) PUnit.unit m

theorem finiteSpineIndividualFilling_faceChain (s : S) :
    receivedSpineFaceChain (oneRel ρ s) (fun _ : PUnit.{1} => q s) (fun _ => u s) PUnit.unit
      (finiteSpineIndividualFilling ρ q u s) =
      Finsupp.mapDomain
        (fun x : PresGroup (namedSpinePresentation (q s)) × SpinePresentationRel (q s) =>
          (familySpineHom (oneRel ρ s) (fun _ : PUnit.{1} => q s) (fun _ => u s) PUnit.unit x.1,
            x.2)) (normalizedSpineReference (q s)) := by
  exact finiteSpineFamilyFilling_faceChain (oneRel ρ s)
    (fun _ : PUnit.{1} => q s) (fun _ => u s) PUnit.unit

theorem finiteSpineIndividualFilling_markingChain (s : S) :
    (ReceivedTree.cellCoordinates (Fin (q s) × Bool)).symm
      (fun i => finiteSpineIndividualFilling ρ q u s (Sum.inr i)) =
      Finsupp.mapDomain
        (fun x : PresGroup (namedSpinePresentation (q s)) × (Fin (q s) × Bool) =>
          (familySpineHom (oneRel ρ s) (fun _ : PUnit.{1} => q s) (fun _ => u s) PUnit.unit x.1,
            x.2)) (universalReferenceMarkingCoefficients (q s)) := by
  simp only [finiteSpineIndividualFilling_named_coeff, normalizedNamedSpineVector, Sum.elim_inr]
  exact ReceivedTree.cellCoordinates_symm_mapSheets
    (familySpineHom (oneRel ρ s) (fun _ : PUnit.{1} => q s) (fun _ => u s) PUnit.unit)
    (namedSpineSurfaceMarkingCoefficient (q s))

end FiniteChains.Davis.Genus
