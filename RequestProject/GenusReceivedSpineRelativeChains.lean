module

public import RequestProject.GenusReceivedSpineCover
public import RequestProject.ReceivedTreeMarkedChains

@[expose] public section

/-! The internal B2 equations imply an exact relative boundary in a genuine cover. -/
namespace FiniteChains.Davis.Genus
open RACG Mirror Comb BlockFamily
open scoped Classical
variable {A Jr S : Type} (ρ : Jr ⊕ S → FreeGroup A)
  (q : S → ℕ) [∀ s, NeZero (q s)] (u : ∀ s, Fin (q s) × Bool → FreeGroup A)

noncomputable def receivedSpineMarkedChain (s : S)
    (γ : (Fin (q s) × Bool) → MonoidAlgebra ℤ
      (PresGroup (substPresF ρ (familyFiniteSpineWordBlock q u)))) :
    (receivedSpineCover ρ q u s).E →₀ ℤ :=
  ReceivedTree.markedChain (markedSpineTree (q s)) (receivedSpineWordReceiver ρ q u s)
    (treeMarkedSpineLoop (q s)) γ

/-- The actual B2 internal-coordinate condition yields equality of full edge
chains. In particular, there is no additional cycle or tree-coordinate premise. -/
theorem receivedSpineFaceChain_boundary_eq_marked (s : S)
    (β : NamedSpineRel (q s) → MonoidAlgebra ℤ
      (PresGroup (substPresF ρ (familyFiniteSpineWordBlock q u))))
    (hβ : ∀ z : SpinePresentationGen (q s),
      (∑ m, β m * foxMatrixPres (substPresF ρ (familyFiniteSpineWordBlock q u))
        (Sum.inr ⟨s, z⟩) (Sum.inr ⟨s, m⟩)) = 0) :
    Comb.bdry2 (receivedSpineCover ρ q u s) (receivedSpineFaceChain ρ q u s β) =
      receivedSpineMarkedChain ρ q u s (fun i => β (Sum.inr i)) := by
  apply ReceivedTree.bdry2_eq_markedChain_of_coordinates
  intro z
  rw [receivedSpineFaceChain_relative_boundary ρ q u s β hβ z]
  apply Finset.sum_congr rfl
  intro i _
  apply congrArg (fun a => β (Sum.inr i) * a)
  exact (receivedSpineWordReceiver_coeff ρ q u s
    (fox z (spinePresentationMarkedWord (q s) i))).symm

end FiniteChains.Davis.Genus
