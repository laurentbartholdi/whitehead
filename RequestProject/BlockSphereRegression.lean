module

public import RequestProject.BlockRelativeQuotient
public import RequestProject.TietzeElimination

@[expose] public section

/-!
# A regression case: a nonaspherical `X`, where `H₂(W̃) = 0` is false

The article's Lemma "Generation in the pushout" allows **any** connected two-complex `X`.  Its
Step 1 (the radial retraction) produces a retraction of a cover of `W` onto one lifted copy of
`X`; on `π₂` this is a left inverse of `π₂(X) → π₂(W)`, so `π₂(X)` injects into `π₂(W)`.  For a
nonaspherical `X` this means

  `H₂(W̃) = π₂(W) ≠ 0`,

and the absolute-vanishing route of `RequestProject/BlockRelativeVanishing.lean`,
`RequestProject/FoxBaseChangeExact.lean` and `RequestProject/BlockQuotientModel.lean` — whose
homological hypothesis `habs` is exactly `H₂(W̃) = 0` — is *not applicable*.  The article's own
input is the relative vanishing `H₂(W̃, U) = 0`, which it obtains from the collapsed space `V`;
this is the hypothesis of `FiniteChains.BlockFox.generates_of_quotient_relative`.

This file records the distinction on a concrete instance in which every object is computable.

## The instance

`X` is the presentation complex of `⟨x ∣ 1⟩` (`FiniteChains.SphereRegression.rhoSphere`): one
one-cell and one two-cell attached along the empty word, i.e. by a **constant** map.  So
`X ≃ S¹ ∨ S²`, `π₁(X) = ℤ` and `π₂(X) ≠ 0`: `X` is not aspherical, exactly as in the test case
"take `X = S²` and `a : Σ_q → X` constant".  The substitution is one elementary move of rule 1
in its Tietze form, `FiniteChains.extMor rhoSphere (tietzeWord 1)`: a new generator `z` and the
new relator `z`.  Its double mapping cylinder `W` has no three-cells, so the faithful chain
model of `W̃` has no three-chains.

## What is proved

* `FiniteChains.SphereRegression.source_not_aspherical` — `π₂(X) ≠ 0`: the two-cell is a Fox
  cycle, and it is nonzero;
* `FiniteChains.SphereRegression.absolute_vanishing_fails` — **`H₂(W̃) ≠ 0`**: the hypothesis
  `habs` of `FiniteChains.BlockFox.generates_of_quotient_model` is false for this faithful
  chain model of `W̃`, so the absolute-vanishing route does not apply here;
* `FiniteChains.SphereRegression.relative_vanishing` — **`H₂(W̃, U) = 0`** for the same model:
  the relative complex of the pair is `ℤ[G'] → ℤ[G']` given by the Fox derivative
  `∂z/∂z = 1`, so its only relative two-cycle is zero;
* `FiniteChains.SphereRegression.generates_sphere` — **equation (3.3) holds**, proved through
  `FiniteChains.BlockFox.generates_of_quotient_relative`, i.e. through the article's relative
  route, in a case where the absolute route is unavailable.

The conclusion of the file is therefore the audit point: the implication "absolute vanishing
plus injectivity of `H₁(U) → H₁(W̃)` gives relative vanishing" is correct but its hypothesis is
strictly stronger than what the article's argument supplies, and an example with an aspherical
`X` (such as `⟨x ∣ x⟩` in `RequestProject/BlockAbsoluteExample.lean`) cannot exhibit the
difference.
-/

namespace FiniteChains

namespace SphereRegression

open MonoidAlgebra

/-- The presentation `⟨x ∣ 1⟩` of `X`: one generator, one relator equal to the empty word.  The
two-cell is attached by a constant map, so `X ≃ S¹ ∨ S²`; the presented group is `ℤ` and `X` is
**not** aspherical. -/
abbrev rhoSphere : Fin 1 → FreeGroup (Fin 1) := fun _ => 1

/-- The relator of the substitution: the new generator `z` itself (`tietzeWord 1 = z`). -/
noncomputable abbrev wZ : FreeGroup (Option (Fin 1)) := tietzeWord (1 : FreeGroup (Fin 1))

/-- The substituted presentation `⟨x, z ∣ 1, z⟩`. -/
noncomputable abbrev rhoBig : Option (Fin 1) → FreeGroup (Option (Fin 1)) := extRel rhoSphere wZ

/-- The structural map of the substitution: one elementary move of rule 1. -/
noncomputable abbrev fSphere : PresMor rhoSphere rhoBig := extMor rhoSphere wZ

/-- The group ring of `π₁(W)`. -/
abbrev RB : Type := MonoidAlgebra ℤ (PresGroup rhoBig)

/-- The degenerate module standing for "no replaced two-cell" and "no three-cells": the double
mapping cylinder of this instance has neither. -/
abbrev TrivB : Type := Fin 0 → RB

theorem trivB_eq_zero (x : TrivB) : x = 0 := by
  funext i
  exact i.elim0

/-- The three-chains of `W̃` (there are none), as a map into the two-chains. -/
noncomputable abbrev a₃Triv : TrivB →ₗ[RB] (Option (Fin 1) → RB) := 0

/-! ### The Fox matrices -/

/-- The Fox matrix of `⟨x ∣ 1⟩` is zero: the relator is the empty word. -/
theorem foxMatrix_sphere (i j : Fin 1) : foxMatrixPres rhoSphere i j = 0 := by
  have h : fox i (rhoSphere j) = 0 := by
    show fox i (1 : FreeGroup (Fin 1)) = 0
    simp [fox_one]
  rw [foxMatrixPres, h, map_zero]

/-- The new relator is the new generator. -/
theorem wZ_eq : wZ = FreeGroup.of (none : Option (Fin 1)) := by
  show tietzeWord (1 : FreeGroup (Fin 1)) = _
  rw [tietzeWord]
  simp

/-- `∂z/∂z = 1`: the Fox derivative of the new relator with respect to the new generator. -/
theorem foxMatrix_big_none_none : foxMatrixPres rhoBig none none = 1 := by
  have h : fox (none : Option (Fin 1)) (rhoBig none) = 1 := by
    show fox (none : Option (Fin 1)) wZ = 1
    rw [wZ_eq, fox_of]
    simp
  rw [foxMatrixPres, h, map_one]

/-- The old two-cell keeps a zero column: its relator is still the empty word. -/
theorem foxMatrix_big_some (i : Option (Fin 1)) (j : Fin 1) :
    foxMatrixPres rhoBig i (some j) = 0 := by
  cases i with
  | none => exact foxMatrix_ext_none_some rhoSphere wZ j
  | some i =>
      have h : foxMatrixPres rhoBig (some i) (some j)
          = extRingHom rhoSphere wZ (foxMatrixPres rhoSphere i j) :=
        foxMatrix_ext_some_some rhoSphere wZ i j
      rw [h, foxMatrix_sphere i j, map_zero]

/-! ### The source is not aspherical -/

/-- The two-cell of `X` is a Fox cycle: `π₂(X) ≠ 0`, i.e. `X` is not aspherical.  This is the
feature that makes the absolute vanishing `H₂(W̃) = 0` unavailable. -/
theorem source_not_aspherical :
    ∃ y : Fin 1 → MonoidAlgebra ℤ (PresGroup rhoSphere), IsFoxCycle rhoSphere y ∧ y ≠ 0 := by
  refine ⟨fun _ => 1, fun i => ?_, ?_⟩
  · exact Finset.sum_eq_zero fun j _ => by rw [foxMatrix_sphere i j, mul_zero]
  · intro h
    have h0 : (1 : MonoidAlgebra ℤ (PresGroup rhoSphere)) = 0 := congrFun h 0
    exact one_ne_zero h0

/-! ### The chain model of `W̃` and of the pair -/

/-- The inclusion of the one-chains of the preimage `U` of `X` into the one-chains of `W̃`: the
old one-cell goes to the old one-cell, the new one-cell `z` is not in `U`. -/
noncomputable def f1Sphere : (Fin 1 → RB) →ₗ[RB] (Option (Fin 1) → RB) where
  toFun w := fun i => Option.elim i 0 w
  map_add' w v := by
    funext i
    cases i with
    | none => exact (add_zero (0 : RB)).symm
    | some a => rfl
  map_smul' c w := by
    funext i
    cases i with
    | none => exact (mul_zero c).symm
    | some a => rfl

@[simp] theorem f1Sphere_none (w : Fin 1 → RB) : f1Sphere w none = 0 := rfl

@[simp] theorem f1Sphere_some (w : Fin 1 → RB) (a : Fin 1) : f1Sphere w (some a) = w a := rfl

theorem f1Sphere_injective : Function.Injective f1Sphere := by
  intro w v h
  funext a
  exact congrFun h (some a)

/-- The two-chains of the preimage of `X`, included into the two-chains of `W̃`: the old
two-cell keeps its coefficient, the new two-cell gets `0`. -/
theorem cellsBase_sphere (a : Fin 1 → RB) :
    fSphere.cellsBase a = fun i => Option.elim i 0 a := by
  have h : fSphere.cellsBase a
      = a 0 • fSphere.cells (Pi.single (0 : Fin 1)
          (1 : MonoidAlgebra ℤ (PresGroup rhoSphere))) := by
    rw [PresMor.cellsBase, Finset.univ_unique]
    simp
  funext i
  rw [h]
  cases i with
  | none =>
      show a 0 * (0 : RB) = 0
      rw [mul_zero]
  | some b =>
      show a 0 * extRingHom rhoSphere wZ
        ((Pi.single (0 : Fin 1) (1 : MonoidAlgebra ℤ (PresGroup rhoSphere)) :
          Fin 1 → MonoidAlgebra ℤ (PresGroup rhoSphere)) b) = a b
      rw [Subsingleton.elim b (0 : Fin 1)]
      simp

/-- The inclusion of the preimage of `X` is a chain map in degree two: both sides vanish, the
Fox matrix column of the old two-cell being zero. -/
theorem hchainF₂_sphere (a : Fin 1 → RB) :
    BlockFox.bdry₂model (Q := TrivB) 0 (BlockFox.inclModel fSphere a)
      = f1Sphere (BlockFox.foxBdryPush fSphere a) := by
  have hR : BlockFox.foxBdryPush fSphere a = 0 := by
    funext i
    simp only [BlockFox.foxBdryPush_apply, Pi.zero_apply]
    exact Finset.sum_eq_zero fun j _ => by rw [foxMatrix_sphere i j, map_zero, mul_zero]
  rw [hR, map_zero, BlockFox.inclModel_apply]
  show BlockFox.bdry₂model (Q := TrivB) 0 (fSphere.cellsBase a, 0) = 0
  rw [BlockFox.bdry₂model_inl]
  funext i
  simp only [foxBdry_apply, Pi.zero_apply]
  refine Finset.sum_eq_zero fun j _ => ?_
  cases j with
  | none =>
      rw [cellsBase_sphere]
      show (0 : RB) * _ = 0
      rw [zero_mul]
  | some j => rw [foxMatrix_big_some i j, mul_zero]

/-- The boundary of the (absent) three-cells vanishes. -/
theorem hdd_sphere (y : TrivB) :
    BlockFox.bdry₂model (Q := TrivB) 0
      (Cancel.bdry₃ a₃Triv (LinearEquiv.refl RB TrivB) y) = 0 := by
  rw [trivB_eq_zero y, map_zero, map_zero]

/-! ### `H₂(W̃) ≠ 0`: the absolute route does not apply -/

/-- The two-chain carrying the sphere of `X` once, in the coordinates of `W̃`. -/
noncomputable def sphereChain : Option (Fin 1) → RB := fun i => Option.elim i 0 (fun _ => 1)

/-- The sphere of `X` is a two-cycle of `W̃`. -/
theorem sphereChain_cycle :
    BlockFox.bdry₂model (Q := TrivB) 0 (sphereChain, (0 : TrivB)) = 0 := by
  rw [BlockFox.bdry₂model_inl]
  funext i
  simp only [foxBdry_apply, Pi.zero_apply]
  refine Finset.sum_eq_zero fun j _ => ?_
  cases j with
  | none =>
      show (0 : RB) * _ = 0
      rw [zero_mul]
  | some j => rw [foxMatrix_big_some i j, mul_zero]

/-- **`H₂(W̃) ≠ 0`.**  For the faithful chain model of this instance — in which `W` has no
three-cells — the hypothesis `habs` of the absolute-vanishing route is false: the sphere of `X`
is a two-cycle of `W̃` which is not a boundary.  The absolute route of
`FiniteChains.BlockFox.generates_of_quotient_model` therefore cannot be used to prove (3.3)
here, although (3.3) is true (`FiniteChains.SphereRegression.generates_sphere`). -/
theorem absolute_vanishing_fails :
    ¬ (∀ z : (Option (Fin 1) → RB) × TrivB, BlockFox.bdry₂model (Q := TrivB) 0 z = 0 →
        ∃ y : TrivB, Cancel.bdry₃ a₃Triv (LinearEquiv.refl RB TrivB) y = z) := by
  intro h
  obtain ⟨y, hy⟩ := h (sphereChain, (0 : TrivB)) sphereChain_cycle
  have h0 : Cancel.bdry₃ a₃Triv (LinearEquiv.refl RB TrivB) y = 0 := by
    rw [trivB_eq_zero y, map_zero]
  have h1 : sphereChain (some 0) = 0 := by
    have h2 := congrArg (fun z : (Option (Fin 1) → RB) × TrivB => z.1 (some (0 : Fin 1)))
      (h0.symm.trans hy)
    simpa using h2.symm
  exact one_ne_zero h1

/-! ### `H₂(W̃, U) = 0`, and equation (3.3) -/

/-- The preimage of `X` is spanned by the old two-cell: a two-chain of `W̃` whose coefficient on
the new two-cell vanishes is a chain of the preimage. -/
theorem mem_range_inclModel (p : Option (Fin 1) → RB) (hp : p none = 0) :
    ∃ a, BlockFox.inclModel (Q := TrivB) fSphere a = (p, (0 : TrivB)) := by
  refine ⟨fun _ => p (some 0), ?_⟩
  rw [BlockFox.inclModel_apply, cellsBase_sphere]
  refine Prod.ext ?_ (trivB_eq_zero _)
  funext i
  cases i with
  | none => exact hp.symm
  | some b => exact congrArg p (congrArg some (Subsingleton.elim (0 : Fin 1) b))

/-- **`H₂(W̃, U) = 0`.**  The relative chain complex of the pair `(W̃, U)` is here the free
module on the new two-cell mapping to the free module on the new one-cell by `∂z/∂z = 1`, so
its only relative two-cycle is zero.  (Geometrically: the collapsed space `V` of the article is
a cylinder over the new cell, with `H₂(V) = 0`.) -/
theorem relative_vanishing (q : BlockFox.RelTwo (Q := TrivB) fSphere)
    (hq : BlockFox.relBdry₂ (bq := 0) hchainF₂_sphere q = 0) :
    ∃ y : TrivB, BlockFox.relBdry₃ (Q := TrivB) (f := fSphere) a₃Triv
      (LinearEquiv.refl RB TrivB) y = q := by
  classical
  refine ⟨0, ?_⟩
  rw [map_zero]
  obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective (BlockFox.subTwo (Q := TrivB) fSphere) q
  have hmem : BlockFox.bdry₂model (Q := TrivB) 0 z
      ∈ BlockFox.subOne (α := Fin 1) f1Sphere := (Submodule.Quotient.mk_eq_zero _).1 hq
  obtain ⟨w, hw⟩ := hmem
  -- the coefficient of the new two-cell is killed by `∂z/∂z = 1`
  have hnone : BlockFox.bdry₂model (Q := TrivB) 0 z none = z.1 none := by
    have hz : BlockFox.bdry₂model (Q := TrivB) 0 z = foxBdry rhoBig z.1 := by
      simp [BlockFox.bdry₂model]
    rw [hz, foxBdry_apply, Fintype.sum_option, foxMatrix_big_none_none, mul_one]
    have hrest : ∑ j : Fin 1, z.1 (some j) * foxMatrixPres rhoBig none (some j) = 0 :=
      Finset.sum_eq_zero fun j _ => by rw [foxMatrix_big_some none j, mul_zero]
    rw [hrest, add_zero]
  have hz1 : z.1 none = 0 := by
    rw [← hnone, ← hw]
    exact f1Sphere_none w
  have hz2 : z.2 = 0 := trivB_eq_zero z.2
  obtain ⟨a, ha⟩ := mem_range_inclModel z.1 hz1
  have hzmem : z ∈ BlockFox.subTwo (Q := TrivB) fSphere := by
    show z ∈ LinearMap.range (BlockFox.inclModel (Q := TrivB) fSphere)
    exact ⟨a, ha.trans (Prod.ext rfl hz2.symm)⟩
  exact ((Submodule.Quotient.mk_eq_zero _).2 hzmem).symm

/-- The substitution is injective on fundamental groups: the Tietze retraction that kills the
new generator is a left inverse. -/
theorem hom_injective : Function.Injective fSphere.hom := by
  have h : ∀ g : PresGroup rhoSphere,
      tietzeRetract rhoSphere (1 : FreeGroup (Fin 1)) (fSphere.hom g) = g := by
    intro g
    induction g using QuotientGroup.induction_on with
    | H v =>
        show tietzeRetract rhoSphere 1 (QuotientGroup.mk (FreeGroup.map Option.some v)) = _
        show (QuotientGroup.mk (tietzeLift (1 : FreeGroup (Fin 1))
          (FreeGroup.map Option.some v)) : PresGroup rhoSphere) = _
        rw [tietzeLift_map_some]
  exact Function.LeftInverse.injective h

/-- **Equation (3.3) for the substitution, through the article's relative route.**  All the
hypotheses of `FiniteChains.BlockFox.generates_of_quotient_relative` hold for this instance —
in particular the relative vanishing `H₂(W̃, U) = 0` — while the absolute vanishing `H₂(W̃) = 0`
of the alternative route is false (`FiniteChains.SphereRegression.absolute_vanishing_fails`),
because `X` is not aspherical. -/
theorem generates_sphere : Generates fSphere :=
  BlockFox.generates_of_quotient_relative (Q := TrivB) (B₃ := TrivB) (bq := 0) (f₁ := f1Sphere)
    hom_injective a₃Triv (LinearEquiv.refl RB TrivB) f1Sphere_injective hchainF₂_sphere
    hdd_sphere relative_vanishing

end SphereRegression

end FiniteChains
