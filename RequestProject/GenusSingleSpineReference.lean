module

public import RequestProject.GenusNormalizedSpineBaseChange

@[expose] public section

/-! The fixed normalized reference in one actual substituted spine, and its
compatibility with the arbitrary-family reference. Awaiting Lean verification. -/
noncomputable section
open scoped Classical
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb PresModel BlockFamily
variable {α Jr : Type} (ρ : Jr ⊕ PUnit.{1} → FreeGroup α)
  (q : ℕ) [NeZero q] (u : Fin q × Bool → FreeGroup α)

def singleFiniteSpineReference : NamedSpineRel q →₀
    MonoidAlgebra ℤ (PresGroup (substPresF ρ (finiteSpineWordBlock q u))) :=
  finiteSpineFamilyFilling ρ (fun _ : PUnit.{1} => q) (fun _ => u) PUnit.unit

theorem singleFiniteSpineReference_internal
    (hrho : ρ (Sum.inr PUnit.unit) = commWord u (finitePairs q))
    (z : SpinePresentationGen q) :
    (∑ m, singleFiniteSpineReference ρ q u m *
      foxMatrixPres (substPresF ρ (finiteSpineWordBlock q u))
        (Sum.inr ⟨PUnit.unit, z⟩) (Sum.inr ⟨PUnit.unit, m⟩)) = 0 := by
  letI : DecidableEq PUnit.{1} := Classical.decEq _
  have h := (finiteSpineFamilyFilling_isFilling ρ
    (fun _ : PUnit.{1} => q) (fun _ => u) (fun s => by cases s; exact hrho)).internal
      PUnit.unit z
  rw [Finsupp.sum_fintype _ _ (fun _ => zero_mul _)] at h
  have hwords : familyFiniteSpineWordBlock (fun _ : PUnit.{1} => q) (fun _ => u) =
      finiteSpineWordBlock q u := by
    funext s
    cases s
    rfl
  with_reducible
    convert h using 1
    apply Finset.sum_congr rfl
    intro m hm
    congr 2
    all_goals first
      | exact Subsingleton.elim _ _
      | (unfold singleFiniteSpineReference; rfl)
      | exact (congrArg (substPresF ρ) hwords).symm
      | exact congrArg (fun r => NamedSpineRel q →₀ MonoidAlgebra ℤ (PresGroup r))
          (congrArg (substPresF ρ) hwords).symm
      | exact congrArg (fun r => fun _ : NamedSpineRel q => MonoidAlgebra ℤ (PresGroup r))
          (congrArg (substPresF ρ) hwords).symm

theorem singleFiniteSpineReference_faceChain :
    receivedSpineFaceChain ρ (fun _ : PUnit.{1} => q) (fun _ => u) PUnit.unit
      (singleFiniteSpineReference ρ q u) =
    Finsupp.mapDomain
      (fun x : PresGroup (namedSpinePresentation q) × SpinePresentationRel q =>
        (familySpineHom ρ (fun _ : PUnit.{1} => q) (fun _ => u) PUnit.unit x.1, x.2))
      (normalizedSpineReference q) :=
  finiteSpineFamilyFilling_faceChain ρ (fun _ : PUnit.{1} => q) (fun _ => u) PUnit.unit

theorem singleFiniteSpineReference_markingChain :
    (ReceivedTree.cellCoordinates (Fin q × Bool)).symm
      (fun i => singleFiniteSpineReference ρ q u (Sum.inr i)) =
    Finsupp.mapDomain
      (fun x : PresGroup (namedSpinePresentation q) × (Fin q × Bool) =>
        (familySpineHom ρ (fun _ : PUnit.{1} => q) (fun _ => u) PUnit.unit x.1, x.2))
      (universalReferenceMarkingCoefficients q) :=
  finiteSpineFamilyFilling_markingChain ρ (fun _ : PUnit.{1} => q) (fun _ => u) PUnit.unit

variable {S : Type} (σ : Jr ⊕ S → FreeGroup α)
  (qs : S → ℕ) [∀ s, NeZero (qs s)] (us : ∀ s, Fin (qs s) × Bool → FreeGroup α)

theorem singleFiniteSpineReference_oneRel (s : S) :
    singleFiniteSpineReference (oneRel σ s) (qs s) (us s) =
      finiteSpineIndividualFilling σ qs us s := rfl

end FiniteChains.Davis.Genus
