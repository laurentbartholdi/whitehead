module

public import RequestProject.RelativeH2
public import RequestProject.CellCancellation

@[expose] public section

/-!
# Assembling the generation lemma for the block

`RequestProject/RelativeH2.lean` proves steps 2–3 of the generation lemma
(`lem:geometric-pushout`) at the level of equivariant chain complexes, and
`RequestProject/CellCancellation.lean` proves the cancellation of the polygon-cylinder
three-cell against the replaced two-cell.  This file puts the two together into the single
statement which property (B2) needs:

> the two-cycles of the two-complex obtained from the double mapping cylinder are spanned,
> over `ℤ[π₁(W)]`, by the images of the two-cycles of the chosen copy of `X`.

`FiniteChains.block_generation_of_relative_vanishing` is that statement.  Its hypotheses are:

* the equivariant chain model: three-chains `B₃` of `W̃`, two-chains `P × Q` (the retained
  two-cells `P` and the replaced two-cell `Q`), one-chains `B₁`, the boundary `∂₃ = (α, β)`
  with `β` invertible, and `d p = ∂₂ (p, 0)` the boundary of the cancelled two-complex;
* the subcomplex `U` (the full inverse image of `X`), its components, the transitivity of the
  deck action on them, and the exactness of `0 → C_*(U) → C_*(W̃) → C_*(W̃, U) → 0` in the
  degrees that are used;
* the vanishing `H₂(W̃, U) = 0`.

The last item is the only geometric input left in this chain of reasoning: in the paper it
comes from `H₂(V) = 0` for the space `V` obtained by collapsing the components of `U`, which
in turn comes from the cubical curvature criterion for `V` (its vertex links are disjoint
unions of covers of the flag complex `L_q`, and that flagness is proved in
`RequestProject/CoveringFlag.lean` and `RequestProject/SurfaceBlockCollapse.lean`).  The
identification `H₂(W̃, U) ≅ H₂(V, V₀) = H₂(V)` is `FiniteChains.h2_quotient_vanishing_of_h2_vanishing`.
-/

namespace FiniteChains

open MonoidAlgebra

section Block

variable {Λ : Type*} [Group Λ] {ι : Type*}
variable {A₂ A₁ B₃ P Q B₁ Q₃ Q₂ Q₁ : Type*}
  [AddCommGroup A₂] [Module (MonoidAlgebra ℤ Λ) A₂]
  [AddCommGroup A₁] [Module (MonoidAlgebra ℤ Λ) A₁]
  [AddCommGroup B₃] [Module (MonoidAlgebra ℤ Λ) B₃]
  [AddCommGroup P] [Module (MonoidAlgebra ℤ Λ) P]
  [AddCommGroup Q] [Module (MonoidAlgebra ℤ Λ) Q]
  [AddCommGroup B₁] [Module (MonoidAlgebra ℤ Λ) B₁]
  [AddCommGroup Q₃] [Module (MonoidAlgebra ℤ Λ) Q₃]
  [AddCommGroup Q₂] [Module (MonoidAlgebra ℤ Λ) Q₂]
  [AddCommGroup Q₁] [Module (MonoidAlgebra ℤ Λ) Q₁]

/-- **The generation statement of property (B2) for the chain model of the block.**

Every two-cycle of the cancelled two-complex lies in the span, over `ℤ[π₁(W)]`, of the
cancelled images of the two-cycles of the chosen component of the inverse image of `X`. -/
theorem block_generation_of_relative_vanishing
    -- the chain model of the double mapping cylinder
    (bdry₂ : P × Q →ₗ[MonoidAlgebra ℤ Λ] B₁)
    (a₃ : B₃ →ₗ[MonoidAlgebra ℤ Λ] P) (b₃ : B₃ ≃ₗ[MonoidAlgebra ℤ Λ] Q)
    -- the subcomplex `U` and the relative complex
    (dA₂ : A₂ →ₗ[MonoidAlgebra ℤ Λ] A₁)
    (dQ₃ : Q₃ →ₗ[MonoidAlgebra ℤ Λ] Q₂) (dQ₂ : Q₂ →ₗ[MonoidAlgebra ℤ Λ] Q₁)
    (f₂ : A₂ →ₗ[MonoidAlgebra ℤ Λ] P × Q) (f₁ : A₁ →ₗ[MonoidAlgebra ℤ Λ] B₁)
    (g₃ : B₃ →ₗ[MonoidAlgebra ℤ Λ] Q₃) (g₂ : P × Q →ₗ[MonoidAlgebra ℤ Λ] Q₂)
    (g₁ : B₁ →ₗ[MonoidAlgebra ℤ Λ] Q₁)
    (hf₁ : Function.Injective f₁)
    (hexB₂ : ∀ z : P × Q, g₂ z = 0 → ∃ a : A₂, f₂ a = z)
    (hg₃ : Function.Surjective g₃)
    (hchainF₂ : ∀ a : A₂, bdry₂ (f₂ a) = f₁ (dA₂ a))
    (hchainG₃ : ∀ y : B₃, g₂ (Cancel.bdry₃ a₃ b₃ y) = dQ₃ (g₃ y))
    (hchainG₂ : ∀ z : P × Q, g₁ (bdry₂ z) = dQ₂ (g₂ z))
    (hdd : ∀ y : B₃, bdry₂ (Cancel.bdry₃ a₃ b₃ y) = 0)
    -- `H₂(W̃, U) = 0`
    (hQvanish : ∀ q : Q₂, dQ₂ q = 0 → ∃ q₃ : Q₃, dQ₃ q₃ = q)
    -- the components of `U` and the transitivity of the deck action
    (A : ι → AddSubgroup A₂) (i₀ : ι)
    (hdecomp : ∀ a : A₂, dA₂ a = 0 → ∃ (s : Finset ι) (f : ι → A₂),
      (∀ i ∈ s, f i ∈ A i) ∧ a = ∑ i ∈ s, f i)
    (htrans : ∀ i : ι, ∃ g : Λ, ∀ x ∈ A i, ∃ y ∈ A i₀,
      x = (MonoidAlgebra.single g (1 : ℤ) : MonoidAlgebra ℤ Λ) • y)
    (p : P) (hp : bdry₂ (p, 0) = 0) :
    (p, 0) ∈ Submodule.span (MonoidAlgebra ℤ Λ)
      (Cancel.cancelMap a₃ b₃ '' (f₂ '' (A i₀ : Set A₂))) := by
  refine Cancel.generation_after_cancellation a₃ b₃ bdry₂ (f₂ '' (A i₀ : Set A₂))
    (fun z hz => ?_) p hp
  -- every two-cycle of `W̃` is, modulo three-boundaries, a cycle of the chosen component
  obtain ⟨a, y, ha, hzy⟩ :=
    h2_surjective_of_relative_vanishing dA₂ (Cancel.bdry₃ a₃ b₃) bdry₂ dQ₃ dQ₂ f₂ f₁ g₃ g₂ g₁
      hf₁ hexB₂ hg₃ hchainF₂ hchainG₃ hchainG₂ hdd hQvanish z hz
  refine ⟨y, ?_⟩
  have : z - Cancel.bdry₃ a₃ b₃ y = f₂ a := by rw [hzy]; abel
  rw [this]
  obtain ⟨s, fc, hfc, hsum⟩ := hdecomp a ha
  have hmem : a ∈ Submodule.span (MonoidAlgebra ℤ Λ) (A i₀ : Set A₂) :=
    mem_span_chosen_component A i₀ htrans s fc hfc hsum
  have himg : Submodule.map f₂ (Submodule.span (MonoidAlgebra ℤ Λ) (A i₀ : Set A₂))
      ≤ Submodule.span (MonoidAlgebra ℤ Λ) (f₂ '' (A i₀ : Set A₂)) := by
    rw [Submodule.map_span]
  exact himg ⟨a, hmem, rfl⟩

end Block

end FiniteChains
