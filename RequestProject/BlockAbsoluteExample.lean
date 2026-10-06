module

public import RequestProject.BlockQuotientModel
public import RequestProject.BlockFoxModelExample

@[expose] public section

/-!
# The hypotheses of the absolute form of the block model are satisfiable

`RequestProject/BlockRelativeVanishing.lean`, `RequestProject/FoxBaseChangeExact.lean` and
`RequestProject/BlockQuotientModel.lean` replace the relative hypothesis `H₂(W̃, U) = 0` of
property (B2) by the absolute one, `H₂(W̃) = 0`, and turn the structural hypotheses about the
relative complex into theorems.  The absolute hypothesis is genuinely stronger than the
degenerate situation of `RequestProject/BlockFoxModelExample.lean` allows (for the identity
substitution over an arbitrary presentation the second homology of the cover is `π₂`, which need
not vanish), so its consistency is checked here on the smallest aspherical presentation:
`⟨x ∣ x⟩`, whose group is trivial and whose universal cover is a disk.

* `FiniteChains.BlockAbsoluteExample.generates_id_disk` — all the hypotheses of
  `FiniteChains.BlockFox.generates_of_absolute_chainMap`, `H₂(W̃) = 0` included;
* `FiniteChains.BlockAbsoluteExample.generates_id_disk_quotient` — the same for the form with the
  relative complex constructed, `FiniteChains.BlockFox.generates_of_quotient_model`.
## Scope of this route (applicability warning)

The implication proved here is correct, but its hypothesis `habs` is **stronger than what the
article's Lemma "Generation in the pushout" supplies**.  That lemma allows an arbitrary
connected two-complex `X`, and its own Step 1 (the radial retraction) shows that `π₂(X)` injects
into `π₂(W)`; for a nonaspherical `X` this makes `H₂(W̃) = π₂(W) ≠ 0`, so `habs` is false.  A
concrete instance is `RequestProject/BlockSphereRegression.lean`.  The article's geometric input
is the *relative* vanishing `H₂(W̃, U) ≅ H₂(V, V₀) = H₂(V) = 0`, obtained from the space `V` in
which each component of `U` is collapsed to a vertex; property (B2) in that form is
`FiniteChains.BlockFox.generates_of_quotient_relative`
(`RequestProject/BlockRelativeQuotient.lean`), and the input is discharged from a cube-complex
model of `V` in `RequestProject/BlockCubeV.lean`.  The statements of this file should therefore
be read as an auxiliary implication, not as the article's argument.
-/

namespace FiniteChains
namespace BlockAbsoluteExample

open MonoidAlgebra

/-- The presentation `⟨x ∣ x⟩`: one generator, one relator equal to it.  The presented group is
trivial and the universal cover of the presentation complex is a disk, so its second homology
vanishes. -/
def rhoDisk : Fin 1 → FreeGroup (Fin 1) := fun _ => FreeGroup.of 0

/-- The degenerate module used for the replaced two-cell and the three-chains. -/
abbrev TrivD : Type := BlockFoxExample.Triv rhoDisk

/-- The image of the generator is trivial in the presented group. -/
theorem mk_of_eq_one : (QuotientGroup.mk (FreeGroup.of 0) : PresGroup rhoDisk) = 1 :=
  (QuotientGroup.eq_one_iff _).2 (Subgroup.subset_normalClosure (Set.mem_range_self 0))

/-- The Fox matrix of `⟨x ∣ x⟩` is the identity. -/
theorem foxMatrixPres_disk (i j : Fin 1) : foxMatrixPres rhoDisk i j = 1 := by
  have h : fox i (rhoDisk j) = 1 := by
    rw [rhoDisk]
    simp [fox_of, Subsingleton.elim i (0 : Fin 1)]
  rw [foxMatrixPres, h, map_one]

/-- The boundary of the one-cell vanishes: the generator is trivial in the presented group. -/
theorem pushEdge_disk (a : Fin 1) : BlockFox.pushEdge (PresMor.id rhoDisk) a = 0 := by
  have h : qgrp (relSub rhoDisk) (FreeGroup.of a) = 1 := by
    rw [qgrp, Subsingleton.elim a (0 : Fin 1), mk_of_eq_one]
    rfl
  rw [BlockFox.pushEdge, h, sub_self, map_zero]

theorem bdry1Push_disk (w : Fin 1 → MonoidAlgebra ℤ (PresGroup rhoDisk)) :
    BlockFox.bdry1Push (PresMor.id rhoDisk) w = 0 := by
  rw [BlockFox.bdry1Push]
  exact Finset.sum_eq_zero fun a _ => by rw [pushEdge_disk a, mul_zero]

/-- **`H₂` of the universal cover of the presentation complex of `⟨x ∣ x⟩` vanishes.**  A Fox
cycle is killed by the identity matrix, hence zero. -/
theorem foxBdry_eq_zero_imp (p : Fin 1 → MonoidAlgebra ℤ (PresGroup rhoDisk))
    (hp : foxBdry rhoDisk p = 0) : p = 0 := by
  funext j
  have h := congrFun hp j
  rw [foxBdry_apply] at h
  simpa [foxMatrixPres_disk, Subsingleton.elim j (0 : Fin 1)] using h

/-- The inclusion of the preimage is a chain map in degree one (both sides vanish). -/
theorem hchain₁_disk (w : Fin 1 → MonoidAlgebra ℤ (PresGroup rhoDisk)) :
    BlockFox.bdry1PushL (PresMor.id rhoDisk) w
      = BlockFox.bdry1Push (PresMor.id rhoDisk) w :=
  BlockFox.bdry1PushL_apply _ w

/-- The boundary of a boundary vanishes in degree one. -/
theorem hdd₁_disk (z : (Fin 1 → MonoidAlgebra ℤ (PresGroup rhoDisk)) × TrivD) :
    BlockFox.bdry1PushL (PresMor.id rhoDisk) (BlockFox.bdry₂model (Q := TrivD) 0 z) = 0 := by
  rw [BlockFox.bdry1PushL_apply, bdry1Push_disk]

/-- **`H₂(W̃) = 0`** for the identity substitution of `⟨x ∣ x⟩`. -/
theorem habs_disk (z : (Fin 1 → MonoidAlgebra ℤ (PresGroup rhoDisk)) × TrivD)
    (hz : BlockFox.bdry₂model (Q := TrivD) 0 z = 0) :
    ∃ y : TrivD, Cancel.bdry₃ (0 : TrivD →ₗ[MonoidAlgebra ℤ (PresGroup rhoDisk)]
      (Fin 1 → MonoidAlgebra ℤ (PresGroup rhoDisk))) (LinearEquiv.refl _ TrivD) y = z := by
  refine ⟨0, ?_⟩
  have h1 : z.1 = 0 := by
    refine foxBdry_eq_zero_imp z.1 ?_
    have h : BlockFox.bdry₂model (Q := TrivD) 0 z = foxBdry rhoDisk z.1 := by
      simp [BlockFox.bdry₂model]
    rw [← h, hz]
  have h2 : z.2 = 0 := BlockFoxExample.triv_eq_zero rhoDisk z.2
  rw [map_zero]
  exact (Prod.ext h1 h2).symm

/-- The inclusion of the preimage is a chain map in degree two. -/
theorem hchainF₂_disk (a : Fin 1 → MonoidAlgebra ℤ (PresGroup rhoDisk)) :
    BlockFox.bdry₂model (Q := TrivD) 0 (BlockFox.inclModel (PresMor.id rhoDisk) a)
      = BlockFox.foxBdryPush (PresMor.id rhoDisk) a := by
  rw [BlockFox.inclModel_apply, BlockFoxExample.cellsBase_id]
  show BlockFox.bdry₂model (Q := TrivD) 0 (a, 0) = _
  rw [BlockFox.bdry₂model_inl]
  funext i
  show ∑ j, a j * foxMatrixPres rhoDisk i j
    = ∑ j, a j * (PresMor.id rhoDisk).pushRing (foxMatrixPres rhoDisk i j)
  exact Finset.sum_congr rfl fun j _ => by rw [BlockFoxExample.pushRing_id]

/-- The boundary of the cancelled three-cells vanishes. -/
theorem hdd_disk (y : TrivD) :
    BlockFox.bdry₂model (Q := TrivD) 0
      (Cancel.bdry₃ (0 : TrivD →ₗ[MonoidAlgebra ℤ (PresGroup rhoDisk)]
        (Fin 1 → MonoidAlgebra ℤ (PresGroup rhoDisk))) (LinearEquiv.refl _ TrivD) y) = 0 := by
  simp [BlockFox.bdry₂model]

/-- **The hypotheses of `FiniteChains.BlockFox.generates_of_absolute_chainMap` are
satisfiable**, the vanishing of `H₂(W̃)` included: for the identity substitution of the
aspherical presentation `⟨x ∣ x⟩` they all hold, and the conclusion is equation (3.3). -/
theorem generates_id_disk : Generates (PresMor.id rhoDisk) := by
  classical
  refine BlockFox.generates_of_absolute_chainMap
    (Q := TrivD) (B₃ := TrivD) (Q₃ := TrivD) (Q₂ := TrivD) (Q₁ := TrivD)
    (PresMor.id rhoDisk) (fun _ _ h => h) 0 0 (LinearEquiv.refl _ _) 0 0 LinearMap.id
    LinearMap.id 0 0
    (BlockFox.bdry1PushL (PresMor.id rhoDisk)) LinearMap.id (fun _ _ h => h) ?_
    (fun y => ⟨y, rfl⟩) (fun y => ⟨0, by simpa using (BlockFoxExample.triv_eq_zero rhoDisk y).symm⟩)
    (fun _ => rfl) (fun y _ => ⟨y, rfl⟩) (fun _ _ h => h)
    hchain₁_disk hdd₁_disk habs_disk hchainF₂_disk (fun _ => rfl) (fun _ => rfl) hdd_disk
  · -- exactness of the pair: the preimage of `X` is everything
    intro z _
    refine ⟨z.1, ?_⟩
    rw [BlockFox.inclModel_apply, BlockFoxExample.cellsBase_id]
    exact Prod.ext rfl (BlockFoxExample.triv_eq_zero rhoDisk z.2).symm

/-- **The hypotheses of `FiniteChains.BlockFox.generates_of_quotient_model` are satisfiable**:
the same check for the form in which the relative complex of the pair is constructed as a
quotient rather than assumed. -/
theorem generates_id_disk_quotient : Generates (PresMor.id rhoDisk) :=
  BlockFox.generates_of_quotient_model (Q := TrivD) (B₃ := TrivD) (bq := 0) (f₁ := LinearMap.id)
    (fun _ _ h => h) 0 (LinearEquiv.refl _ _) (BlockFox.bdry1PushL (PresMor.id rhoDisk))
    LinearMap.id (fun _ _ h => h) (fun _ _ h => h) hchain₁_disk hdd₁_disk habs_disk
    hchainF₂_disk hdd_disk

end BlockAbsoluteExample
end FiniteChains
