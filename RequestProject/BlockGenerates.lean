import RequestProject.BlockGeneration
import RequestProject.GenerationStep

/-!
# From the homology of the double mapping cylinder to equation (3.3)

`RequestProject/BlockGeneration.lean` proves, for the equivariant chain model of the double
mapping cylinder, that the two-cycles of the cancelled two-complex are spanned over
`ℤ[π₁(W)]` by the cancelled images of the two-cycles of the chosen copy of `X`.  Property
(B2) is stated in the language of presentations: for the structural map `f : E → E'` of the
substitution (3.4),

  `π₂(E') = ℤ[G(E')] · f_* π₂(E)`,

i.e. every **Fox cycle** of `E'` is a `ℤ[G(E')]`-combination of images of Fox cycles of `E`
(`FiniteChains.Generates`).  This file proves that the two statements agree: the surjectivity
obtained from the relative homology *is* the generation of all Fox cycles by the images of
the old ones.

* `FiniteChains.foxBdry` — the Fox boundary of a presentation as a map of `ℤ[G]`-modules, and
  `FiniteChains.isFoxCycle_iff_foxBdry_eq_zero`: Fox cycles are exactly its kernel, so the
  two-chains of the universal cover of a presentation complex form a chain complex in the
  sense used by the homological lemmas;
* `FiniteChains.generates_of_block_chain_model` — **the passage to presentations**: given the
  chain model of the double mapping cylinder for the substitution, the vanishing of
  `H₂(W̃, U)`, the transitive deck action on the components of `U` and the identification of
  the cancelled images with the images of the structural map, equation (3.3) holds for that
  structural map.

As everywhere in this part of the development, the single geometric input that is not proved
is the vanishing `H₂(W̃, U) = 0`, which the paper obtains from the cubical curvature criterion
for the collapsed space `V`.
-/

namespace FiniteChains

open MonoidAlgebra

universe u

section FoxBoundary

variable {α J : Type u} [DecidableEq α] [Fintype J] (ρ : J → FreeGroup α)

/-- The Fox boundary `∂₂` of a presentation, as a map of `ℤ[G]`-modules from the two-chains
to the one-chains of the universal cover of the presentation complex. -/
noncomputable def foxBdry :
    (J → MonoidAlgebra ℤ (PresGroup ρ)) →ₗ[MonoidAlgebra ℤ (PresGroup ρ)]
      (α → MonoidAlgebra ℤ (PresGroup ρ)) where
  toFun v := fun i => ∑ j, v j * foxMatrixPres ρ i j
  map_add' v w := by
    funext i
    simp [Finset.sum_add_distrib, add_mul]
  map_smul' c v := by
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum, mul_assoc]

@[simp] theorem foxBdry_apply (v : J → MonoidAlgebra ℤ (PresGroup ρ)) (i : α) :
    foxBdry ρ v i = ∑ j, v j * foxMatrixPres ρ i j := rfl

/-- Fox cycles are exactly the kernel of the Fox boundary. -/
theorem isFoxCycle_iff_foxBdry_eq_zero (v : J → MonoidAlgebra ℤ (PresGroup ρ)) :
    IsFoxCycle ρ v ↔ foxBdry ρ v = 0 := by
  constructor
  · intro h
    funext i
    simpa using h i
  · intro h i
    have := congrFun h i
    simpa using this

end FoxBoundary

section Bridge

variable {α J α' J' : Type u}
  [DecidableEq α] [Fintype J] [Fintype α'] [DecidableEq α'] [Fintype J']
  {ρ : J → FreeGroup α} {ρ' : J' → FreeGroup α'}

variable {ι : Type*} {A₂ A₁ Q Q₃ Q₂ Q₁ B₃ : Type*}
  [AddCommGroup A₂] [Module (MonoidAlgebra ℤ (PresGroup ρ')) A₂]
  [AddCommGroup A₁] [Module (MonoidAlgebra ℤ (PresGroup ρ')) A₁]
  [AddCommGroup Q] [Module (MonoidAlgebra ℤ (PresGroup ρ')) Q]
  [AddCommGroup B₃] [Module (MonoidAlgebra ℤ (PresGroup ρ')) B₃]
  [AddCommGroup Q₃] [Module (MonoidAlgebra ℤ (PresGroup ρ')) Q₃]
  [AddCommGroup Q₂] [Module (MonoidAlgebra ℤ (PresGroup ρ')) Q₂]
  [AddCommGroup Q₁] [Module (MonoidAlgebra ℤ (PresGroup ρ')) Q₁]

omit [Fintype α'] in
/-- **Equation (3.3) from the chain model of the double mapping cylinder.**

The two-chains of `W̃` are `P × Q`, where `P` is the module of two-chains of the substituted
presentation complex and `Q` the free module on the replaced two-cell; `bdry₂` restricted to
`P` is the Fox boundary of `ρ'` (hypothesis `hbdry`), and the three-cells are cancelled
against the replaced two-cell as in `RequestProject/CellCancellation.lean`.  With the
relative vanishing `H₂(W̃, U) = 0`, the transitive deck action on the components of `U`, and
the identification of the cancelled component cycles with the images of Fox cycles of `ρ`
under the structural map, the generation property (3.3) — property (B2) — holds. -/
theorem generates_of_block_chain_model (f : PresMor ρ ρ')
    (bdry₂ : (J' → MonoidAlgebra ℤ (PresGroup ρ')) × Q →ₗ[MonoidAlgebra ℤ (PresGroup ρ')]
      (α' → MonoidAlgebra ℤ (PresGroup ρ')))
    (a₃ : B₃ →ₗ[MonoidAlgebra ℤ (PresGroup ρ')] (J' → MonoidAlgebra ℤ (PresGroup ρ')))
    (b₃ : B₃ ≃ₗ[MonoidAlgebra ℤ (PresGroup ρ')] Q)
    (dA₂ : A₂ →ₗ[MonoidAlgebra ℤ (PresGroup ρ')] A₁)
    (dQ₃ : Q₃ →ₗ[MonoidAlgebra ℤ (PresGroup ρ')] Q₂)
    (dQ₂ : Q₂ →ₗ[MonoidAlgebra ℤ (PresGroup ρ')] Q₁)
    (f₂ : A₂ →ₗ[MonoidAlgebra ℤ (PresGroup ρ')]
      (J' → MonoidAlgebra ℤ (PresGroup ρ')) × Q)
    (f₁ : A₁ →ₗ[MonoidAlgebra ℤ (PresGroup ρ')] (α' → MonoidAlgebra ℤ (PresGroup ρ')))
    (g₃ : B₃ →ₗ[MonoidAlgebra ℤ (PresGroup ρ')] Q₃)
    (g₂ : (J' → MonoidAlgebra ℤ (PresGroup ρ')) × Q →ₗ[MonoidAlgebra ℤ (PresGroup ρ')] Q₂)
    (g₁ : (α' → MonoidAlgebra ℤ (PresGroup ρ')) →ₗ[MonoidAlgebra ℤ (PresGroup ρ')] Q₁)
    (hf₁ : Function.Injective f₁)
    (hexB₂ : ∀ z, g₂ z = 0 → ∃ a : A₂, f₂ a = z)
    (hg₃ : Function.Surjective g₃)
    (hchainF₂ : ∀ a : A₂, bdry₂ (f₂ a) = f₁ (dA₂ a))
    (hchainG₃ : ∀ y : B₃, g₂ (Cancel.bdry₃ a₃ b₃ y) = dQ₃ (g₃ y))
    (hchainG₂ : ∀ z, g₁ (bdry₂ z) = dQ₂ (g₂ z))
    (hdd : ∀ y : B₃, bdry₂ (Cancel.bdry₃ a₃ b₃ y) = 0)
    (hQvanish : ∀ q : Q₂, dQ₂ q = 0 → ∃ q₃ : Q₃, dQ₃ q₃ = q)
    (A : ι → AddSubgroup A₂) (i₀ : ι)
    (hdecomp : ∀ a : A₂, dA₂ a = 0 → ∃ (s : Finset ι) (fc : ι → A₂),
      (∀ i ∈ s, fc i ∈ A i) ∧ a = ∑ i ∈ s, fc i)
    (htrans : ∀ i : ι, ∃ g : PresGroup ρ', ∀ x ∈ A i, ∃ y ∈ A i₀,
      x = (MonoidAlgebra.single g (1 : ℤ) : MonoidAlgebra ℤ (PresGroup ρ')) • y)
    -- the boundary of the cancelled complex is the Fox boundary of the substituted
    -- presentation
    (hbdry : ∀ p : J' → MonoidAlgebra ℤ (PresGroup ρ'), bdry₂ (p, 0) = foxBdry ρ' p)
    -- the cancelled cycles of the chosen copy of `X` are the images of the Fox cycles of `ρ`
    (himage : ∀ z ∈ Cancel.cancelMap a₃ b₃ '' (f₂ '' (A i₀ : Set A₂)),
      ∃ y, IsFoxCycle ρ y ∧ z = (f.cells y, 0)) :
    Generates f := by
  intro v hv
  have hvz : bdry₂ (v, 0) = 0 := by
    rw [hbdry v, ← isFoxCycle_iff_foxBdry_eq_zero ρ' v]
    exact hv
  have hmem := block_generation_of_relative_vanishing bdry₂ a₃ b₃ dA₂ dQ₃ dQ₂ f₂ f₁ g₃ g₂ g₁
    hf₁ hexB₂ hg₃ hchainF₂ hchainG₃ hchainG₂ hdd hQvanish A i₀ hdecomp htrans v hvz
  -- the cancelled cycles are the images of the old Fox cycles, placed in the first
  -- coordinate
  set T : Set (J' → MonoidAlgebra ℤ (PresGroup ρ')) :=
    {w | ∃ y, IsFoxCycle ρ y ∧ w = f.cells y}
  have hsub : Cancel.cancelMap a₃ b₃ '' (f₂ '' (A i₀ : Set A₂))
      ⊆ (LinearMap.inl (MonoidAlgebra ℤ (PresGroup ρ'))
          (J' → MonoidAlgebra ℤ (PresGroup ρ')) Q) '' T := by
    intro z hz
    obtain ⟨y, hy, rfl⟩ := himage z hz
    exact ⟨f.cells y, ⟨y, hy, rfl⟩, rfl⟩
  have hspan := Submodule.span_mono hsub hmem
  rw [← Submodule.map_span] at hspan
  obtain ⟨w, hw, hwv⟩ := hspan
  have : w = v := congrArg Prod.fst hwv
  rwa [this] at hw

end Bridge

end FiniteChains
