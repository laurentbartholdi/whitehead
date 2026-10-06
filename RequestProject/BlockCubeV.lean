module

public import RequestProject.BlockRelativeQuotient
public import RequestProject.CubeMedianGraph

@[expose] public section

/-!
# The collapsed space `V` as a cube complex, and the relative vanishing it gives

Step 2 of the article's Lemma "Generation in the pushout" collapses each component of the
preimage `U ⊆ W̃` of `X` separately to a vertex.  The resulting space `V` (with `V₀` the set of
new vertices) is a three-dimensional cube complex whose vertex links are flag, hence CAT(0),
so `H₂(V) = 0`; Step 3 then reads

  `H₂(W̃, U) ≅ H₂(V, V₀) = H₂(V) = 0`.

The cells of `V` in degrees `1, 2, 3` are exactly the cells of `W̃` that do not lie in `U`,
i.e. the generators of the relative chain complex of the pair; the collapse changes cells only
in degree `0`, where it creates the vertices `V₀`.  Accordingly this file relates the relative
chain complex **constructed** in `RequestProject/BlockQuotientModel.lean` — the quotient
`C_*(W̃)/C_*(U)` — with the cellular chain complex of a cube complex as axiomatised in
`RequestProject/CubeCartanHadamard.lean`, and applies the proved combinatorial
Cartan–Hadamard theorem to it.

## The object

`FiniteChains.BlockFox.VCubeModel` is the datum of a realisation of `V` as a
three-dimensional cube complex with the descending-cube property, *together with* the
identification of its cells with the relative cells of the pair:

* `S : DescCubeStr Vx` — the cube complex `V` seen from a base vertex; the descending-cube
  axioms are the combinatorial form of the CAT(0) conclusion of Step 2, and they are available
  as soon as the one-skeleton of `V` is a median graph
  (`FiniteChains.MedianGraph.toDescCubeStr`);
* `cell₂`, `cell₁`, `cell₃` — bases of the relative two-, one- and three-chains indexed by the
  squares, edges and cubes of `V`.  A basis is exactly a cell-by-cell identification together
  with a choice of orientation for each cell, so these fields carry both the cells and their
  orientations;
* `bdry₂`, `bdry₃` — the boundary maps agree under those identifications: the relative
  boundary of the pair is the cellular boundary of `V`.

Nothing here is assumed about the homology of `V`: the vanishing is *proved* from the
descending-cube structure.

## What is proved

* `FiniteChains.BlockFox.VCubeModel.relative_vanishing` — **`H₂(W̃, U) = 0`**: every relative
  two-cycle is the relative boundary of a three-chain.  The proof reads the cycle as an
  integral cellular two-cycle of `V`, applies
  `FiniteChains.DescCubeStr.exists_d₃_eq`, and reads the resulting three-chain back;
* `FiniteChains.BlockFox.generates_of_cubeV` — **property (B2) with the geometric input in
  the article's place**: equation (3.3) for the structural map, the homological input being
  the cube structure of `V` and not any vanishing for `W̃`;
* `FiniteChains.BlockFox.generates_of_medianV` — the same with the CAT(0) input in its proved
  combinatorial form: it suffices that the one-skeleton of `V` is a median graph.

The remaining unproved inputs of (B2) are therefore *geometric*, and explicitly so: the
`π₁`-injectivity of the substitution (Step 1, the radial retraction) and the existence of a
`VCubeModel`, i.e. that the collapse of the components of `U` produces a three-dimensional
cube complex with the descending-cube property whose cells are the relative cells of the pair
(Step 2).
-/

namespace FiniteChains

namespace BlockFox

open MonoidAlgebra

universe u

variable {α J α' J' : Type u}
  [Fintype α] [DecidableEq α] [Fintype J] [DecidableEq J]
  [Fintype α'] [DecidableEq α'] [Fintype J']
  {ρ : J → FreeGroup α} {ρ' : J' → FreeGroup α'}

section CubeV

variable {Q B₃ : Type u}
  [AddCommGroup Q] [Module (MonoidAlgebra ℤ (PresGroup ρ')) Q]
  [AddCommGroup B₃] [Module (MonoidAlgebra ℤ (PresGroup ρ')) B₃]

variable {f : PresMor ρ ρ'}
  {bq : Q →ₗ[MonoidAlgebra ℤ (PresGroup ρ')] (α' → MonoidAlgebra ℤ (PresGroup ρ'))}
  {f₁ : (α → MonoidAlgebra ℤ (PresGroup ρ')) →ₗ[MonoidAlgebra ℤ (PresGroup ρ')]
    (α' → MonoidAlgebra ℤ (PresGroup ρ'))}

/-- **The collapsed space `V`, realised as a three-dimensional cube complex.**  See the module
docstring for the meaning of the fields. -/
structure VCubeModel
    (hchainF₂ : ∀ a, bdry₂model (Q := Q) bq (inclModel f a) = f₁ (foxBdryPush f a))
    (a₃ : B₃ →ₗ[MonoidAlgebra ℤ (PresGroup ρ')] (J' → MonoidAlgebra ℤ (PresGroup ρ')))
    (b₃ : B₃ ≃ₗ[MonoidAlgebra ℤ (PresGroup ρ')] Q) where
  /-- The vertices of the cube complex `V`. -/
  Vx : Type u
  [vxOrder : LinearOrder Vx]
  /-- The descending-cube structure on `V`: the combinatorial CAT(0) input of Step 2. -/
  S : DescCubeStr Vx
  /-- The relative two-cells of the pair are the squares of `V`, with orientations. -/
  cell₂ : Module.Basis S.SqC ℤ (RelTwo (Q := Q) f)
  /-- The relative one-cells of the pair are the edges of `V`, with orientations. -/
  cell₁ : Module.Basis S.EdgeC ℤ (RelOne (α := α) f₁)
  /-- The three-cells of `W̃` are the cubes of `V`, with orientations. -/
  cell₃ : Module.Basis S.CbC ℤ B₃
  /-- The relative boundary `C₂(W̃, U) → C₁(W̃, U)` is the cellular boundary of `V`. -/
  bdry₂ : ∀ q, cell₁.repr (relBdry₂ (bq := bq) hchainF₂ q) = S.d₂ (cell₂.repr q)
  /-- The relative boundary `C₃(W̃) → C₂(W̃, U)` is the cellular boundary of `V`. -/
  bdry₃ : ∀ y, cell₂.repr (relBdry₃ (Q := Q) (f := f) a₃ b₃ y) = S.d₃ (cell₃.repr y)

attribute [instance] VCubeModel.vxOrder

namespace VCubeModel

variable {hchainF₂ : ∀ a, bdry₂model (Q := Q) bq (inclModel f a) = f₁ (foxBdryPush f a)}
  {a₃ : B₃ →ₗ[MonoidAlgebra ℤ (PresGroup ρ')] (J' → MonoidAlgebra ℤ (PresGroup ρ'))}
  {b₃ : B₃ ≃ₗ[MonoidAlgebra ℤ (PresGroup ρ')] Q}

omit [Fintype α] [Fintype α'] in
/-- **`H₂(W̃, U) = 0`.**  If the collapsed space `V` is realised as a three-dimensional cube
complex with the descending-cube property, and its cells in degrees `1, 2, 3` are the relative
cells of the pair `(W̃, U)` with matching boundary maps, then every relative two-cycle is the
relative boundary of a three-chain.  This is the identification
`H₂(W̃, U) ≅ H₂(V, V₀) = H₂(V) = 0` of Step 3 of the article's proof, with `H₂(V) = 0` supplied
by the combinatorial Cartan–Hadamard theorem. -/
theorem relative_vanishing (C : VCubeModel hchainF₂ a₃ b₃) (q : RelTwo (Q := Q) f)
    (hq : relBdry₂ (bq := bq) hchainF₂ q = 0) :
    ∃ y : B₃, relBdry₃ (Q := Q) (f := f) a₃ b₃ y = q := by
  have h2 : C.S.d₂ (C.cell₂.repr q) = 0 := by
    rw [← C.bdry₂ q, hq, map_zero]
  obtain ⟨c, hc⟩ := C.S.exists_d₃_eq (C.cell₂.repr q) h2
  refine ⟨C.cell₃.repr.symm c, C.cell₂.repr.injective ?_⟩
  rw [C.bdry₃, LinearEquiv.apply_symm_apply, hc]

end VCubeModel

omit [Fintype α] [Fintype α'] in
/-- **Property (B2) from the cube structure of the collapsed space `V`.**  Equation (3.3) for
the structural map of the substitution: the homological input is the realisation of `V` — the
universal cover of the double mapping cylinder with each component of the preimage of `X`
collapsed to a vertex — as a three-dimensional cube complex with the descending-cube property.
No vanishing of `H₂(W̃)` is used; it is false in general. -/
theorem generates_of_cubeV (hinj : Function.Injective f.hom)
    (a₃ : B₃ →ₗ[MonoidAlgebra ℤ (PresGroup ρ')] (J' → MonoidAlgebra ℤ (PresGroup ρ')))
    (b₃ : B₃ ≃ₗ[MonoidAlgebra ℤ (PresGroup ρ')] Q)
    (hf₁ : Function.Injective f₁)
    (hchainF₂ : ∀ a, bdry₂model (Q := Q) bq (inclModel f a) = f₁ (foxBdryPush f a))
    (hdd : ∀ y, bdry₂model (Q := Q) bq (Cancel.bdry₃ a₃ b₃ y) = 0)
    (C : VCubeModel hchainF₂ a₃ b₃) :
    Generates f :=
  generates_of_quotient_relative hinj a₃ b₃ hf₁ hchainF₂ hdd (VCubeModel.relative_vanishing C)

omit [Fintype α] [Fintype α'] in
/-- **Property (B2) with the CAT(0) input in its proved combinatorial form.**  It suffices
that the one-skeleton of the collapsed space `V` is a median graph: the descending-cube
structure is then `FiniteChains.MedianGraph.toDescCubeStr`. -/
theorem generates_of_medianV (hinj : Function.Injective f.hom)
    (a₃ : B₃ →ₗ[MonoidAlgebra ℤ (PresGroup ρ')] (J' → MonoidAlgebra ℤ (PresGroup ρ')))
    (b₃ : B₃ ≃ₗ[MonoidAlgebra ℤ (PresGroup ρ')] Q)
    (hf₁ : Function.Injective f₁)
    (hchainF₂ : ∀ a, bdry₂model (Q := Q) bq (inclModel f a) = f₁ (foxBdryPush f a))
    (hdd : ∀ y, bdry₂model (Q := Q) bq (Cancel.bdry₃ a₃ b₃ y) = 0)
    {Vx : Type u} [LinearOrder Vx] (G : MedianGraph Vx)
    (cell₂ : Module.Basis (G.toDescCubeStr).SqC ℤ (RelTwo (Q := Q) f))
    (cell₁ : Module.Basis (G.toDescCubeStr).EdgeC ℤ (RelOne (α := α) f₁))
    (cell₃ : Module.Basis (G.toDescCubeStr).CbC ℤ B₃)
    (bdry₂ : ∀ q, cell₁.repr (relBdry₂ (bq := bq) hchainF₂ q)
      = (G.toDescCubeStr).d₂ (cell₂.repr q))
    (bdry₃ : ∀ y, cell₂.repr (relBdry₃ (Q := Q) (f := f) a₃ b₃ y)
      = (G.toDescCubeStr).d₃ (cell₃.repr y)) :
    Generates f :=
  generates_of_cubeV hinj a₃ b₃ hf₁ hchainF₂ hdd
    { Vx := Vx, S := G.toDescCubeStr, cell₂ := cell₂, cell₁ := cell₁, cell₃ := cell₃,
      bdry₂ := bdry₂, bdry₃ := bdry₃ }

end CubeV

end BlockFox

end FiniteChains
