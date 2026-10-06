import RequestProject.StabilizedDiskPresentation
import RequestProject.DiskFamilyMap

/-! The filled-circle stabilization is natural for literal disk
inclusions. This includes its actual forward homotopy equivalence,
so stabilization preserves a chain's zero-on-pi2 maps. Unverified. -/

noncomputable section
namespace FiniteChains.ClassicalGraphModel
open RelativeAttachment
variable {A B D : Type}

theorem diskRoseMap_comp (f : A → B) (g : B → D) :
    (diskRoseMap g).comp (diskRoseMap f) = diskRoseMap (g ∘ f) := by
  apply hom_ext (roseAttaching A) (boundaryFamilyInclusion A (Fin 1 → ℝ))
  · intro u
    cases u
    rfl
  · rintro ⟨a, x⟩
    change diskRoseMap g (diskRoseMap f (cell _ _ ⟨a, x⟩)) = _
    rw [diskRoseMap_cell, diskRoseMap_cell, diskRoseMap_cell]
    rfl

theorem diskRoseMap_id : diskRoseMap (id : A → A) = ContinuousMap.id _ := by
  apply hom_ext (roseAttaching A) (boundaryFamilyInclusion A (Fin 1 → ℝ))
  · intro u
    cases u
    rfl
  · rintro ⟨a, x⟩
    exact diskRoseMap_cell id ⟨a, x⟩

end FiniteChains.ClassicalGraphModel

namespace FiniteChains.RelativeAttachment.StabilizedDiskPresentation
open ClassicalGraphModel
variable {A B J K : Type}

def withDummy (f : A ↪ B) : A ⊕ PUnit ↪ B ⊕ PUnit where
  toFun := Sum.map f id
  inj' := by
    intro a b hab
    cases a <;> cases b <;> simp_all [f.injective.eq_iff]

variable (f : A ↪ B) (c : J ↪ K)
  (r : C(BoundaryFamily J (Fin 2 → ℝ), Rose A))
  (s : C(BoundaryFamily K (Fin 2 → ℝ), Rose B))
  (h : ∀ z, diskRoseMap f (r z) = s ⟨c z.1, z.2⟩)

include h in
theorem attaching_natural (z : BoundaryFamily (J ⊕ PUnit) (Fin 2 → ℝ)) :
    diskRoseMap (withDummy f) (attaching r z) =
      attaching s ⟨withDummy c z.1, z.2⟩ := by
  rcases z with ⟨j | u, a⟩
  · change diskRoseMap (withDummy f) (diskRoseMap Sum.inl (r ⟨j, a⟩)) =
      diskRoseMap Sum.inl (s ⟨c j, a⟩)
    rw [← h ⟨j, a⟩]
    exact congrArg (fun m => m (r ⟨j, a⟩))
      ((diskRoseMap_comp Sum.inl (withDummy f)).trans
        (diskRoseMap_comp f Sum.inl).symm)
  · change diskRoseMap (withDummy f) (diskRoseMap Sum.inr (dummyCircleBoundaryHomeomorph a)) =
      diskRoseMap Sum.inr (dummyCircleBoundaryHomeomorph a)
    exact congrArg (fun m => m (dummyCircleBoundaryHomeomorph a))
      (diskRoseMap_comp Sum.inr (withDummy f))

def map : C(Model r, Model s) :=
  diskFamilyMap (attaching r) (attaching s) (diskRoseMap (withDummy f))
    (withDummy c) (fun j a => attaching_natural f c r s h ⟨j, a⟩)

theorem homotopyEquiv_natural :
    (map f c r s h).comp (homotopyEquiv r).toFun =
      (homotopyEquiv s).toFun.comp
        (DiskPresentationExtension.sourceMap f c r s h) := by
  rw [homotopyEquiv_toFun, homotopyEquiv_toFun]
  apply hom_ext r (boundaryFamilyInclusion J (Fin 2 → ℝ))
  · intro x
    change map f c r s h (DiskPresentationExtension.sourceMap oldGenerator oldRelator
      r (attaching r) (attaching_old r) (old r (boundaryFamilyInclusion J (Fin 2 → ℝ)) x)) =
      DiskPresentationExtension.sourceMap oldGenerator oldRelator s (attaching s) (attaching_old s)
        (DiskPresentationExtension.sourceMap f c r s h (old r (boundaryFamilyInclusion J (Fin 2 → ℝ)) x))
    rw [DiskPresentationExtension.sourceMap_old]
    change diskFamilyMap (attaching r) (attaching s) (diskRoseMap (withDummy f))
      (withDummy c) (fun j a => attaching_natural f c r s h ⟨j, a⟩)
        (old (attaching r) (boundaryFamilyInclusion (J ⊕ PUnit) (Fin 2 → ℝ))
          (diskRoseMap oldGenerator x)) = _
    rw [diskFamilyMap_old, DiskPresentationExtension.sourceMap_old,
      DiskPresentationExtension.sourceMap_old]
    exact congrArg (old (attaching s) (boundaryFamilyInclusion (K ⊕ PUnit) (Fin 2 → ℝ)))
      (congrArg (fun m => m x)
      ((diskRoseMap_comp Sum.inl (withDummy f)).trans
        (diskRoseMap_comp f Sum.inl).symm))
  · rintro ⟨j, x⟩
    change map f c r s h (DiskPresentationExtension.sourceMap oldGenerator oldRelator
      r (attaching r) (attaching_old r) (cell r (boundaryFamilyInclusion J (Fin 2 → ℝ)) ⟨j, x⟩)) =
      DiskPresentationExtension.sourceMap oldGenerator oldRelator s (attaching s) (attaching_old s)
        (DiskPresentationExtension.sourceMap f c r s h
          (cell r (boundaryFamilyInclusion J (Fin 2 → ℝ)) ⟨j, x⟩))
    rw [DiskPresentationExtension.sourceMap_cell]
    change diskFamilyMap (attaching r) (attaching s) (diskRoseMap (withDummy f))
      (withDummy c) (fun j a => attaching_natural f c r s h ⟨j, a⟩)
        (cell (attaching r) (boundaryFamilyInclusion (J ⊕ PUnit) (Fin 2 → ℝ))
          ⟨oldRelator j, x⟩) = _
    rw [diskFamilyMap_cell, DiskPresentationExtension.sourceMap_cell,
      DiskPresentationExtension.sourceMap_cell]
    rfl

theorem map_killsPi2_iff : Whitehead.KillsPi2 (map f c r s h) ↔
    Whitehead.KillsPi2 (DiskPresentationExtension.sourceMap f c r s h) := by
  apply Whitehead.killsPi2_homotopyEquiv_square_iff (homotopyEquiv r) (homotopyEquiv s)
  rw [homotopyEquiv_natural]

end FiniteChains.RelativeAttachment.StabilizedDiskPresentation
