module

public import RequestProject.PresSubcomplex
public import RequestProject.CombPi2RetractionSquares

@[expose] public section

/-! Literal cellular isomorphisms for a bijective change of generator
labels, with two-cell labels fixed. Pending final Lean verification. -/

noncomputable section
open scoped Classical
namespace FiniteChains.Comb.PresGeneratorRelabel
universe u
variable {A B J : Type u} [DecidableEq A] [DecidableEq B]
  (e : A ≃ B) (ρ : J → FreeGroup A) (σ : J → FreeGroup B)
  (hrel : ∀ j, σ j = FreeGroup.map e (ρ j))

def forward : Hom (presComplex ρ) (presComplex σ) :=
  presInclHom e e.injective ρ σ id hrel

omit [DecidableEq A] [DecidableEq B] in
include hrel in
theorem inverse_rel (j : J) : ρ j = FreeGroup.map e.symm (σ j) := by
  rw [hrel j, FreeGroup.map.comp]
  have h : (e.symm : B → A) ∘ e = id := funext e.symm_apply_apply
  rw [h, FreeGroup.map.id]

def backward : Hom (presComplex σ) (presComplex ρ) :=
  presInclHom e.symm e.symm.injective σ ρ id (inverse_rel e ρ σ hrel)

theorem backward_forward_V (x : (presComplex ρ).V) :
    (backward e ρ σ hrel).onV ((forward e ρ σ hrel).onV x) = x :=
  Subsingleton.elim _ _

theorem backward_forward_E (x : A) :
    (backward e ρ σ hrel).onE ((forward e ρ σ hrel).onE x) = x :=
  e.symm_apply_apply x

theorem backward_forward_F (x : J) :
    (backward e ρ σ hrel).onF ((forward e ρ σ hrel).onF x) = x := rfl

end FiniteChains.Comb.PresGeneratorRelabel
