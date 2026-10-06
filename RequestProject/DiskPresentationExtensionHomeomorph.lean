module

public import RequestProject.DiskPresentationExtension

@[expose] public section

noncomputable section
namespace FiniteChains.RelativeAttachment.DiskPresentationExtension
open ClassicalGraphModel
open scoped Classical

variable {A B J K : Type} (f : A ↪ B) (c : J ↪ K)
    (r : C(BoundaryFamily J (Fin 2 → ℝ), Rose A))
    (s : C(BoundaryFamily K (Fin 2 → ℝ), Rose B))
    (h : ∀ z, diskRoseMap f (r z) = s ⟨c z.1, z.2⟩)

def sourceIntoExtension : C(DiskAttachment r, DiskAttachment (twoAttaching f c r s)) :=
  (⟨old (twoAttaching f c r s) (boundaryFamilyInclusion (NewRelators c) _),
    old_continuous _ _⟩ : C(DiskAttachment (oneAttaching f r), _)).comp
      ⟨old (oneAttaching f r) (boundaryFamilyInclusion (NewGenerators f) _), old_continuous _ _⟩

def relatorDiskIntoExtension :
    C(DiskFamily K (Fin 2 → ℝ), DiskAttachment (twoAttaching f c r s)) where
  toFun d := if hk : d.1 ∈ Set.range c then
    sourceIntoExtension f c r s (cell r (boundaryFamilyInclusion J _) ⟨Classical.choose hk, d.2⟩)
    else cell (twoAttaching f c r s) (boundaryFamilyInclusion (NewRelators c) _) ⟨⟨d.1, hk⟩, d.2⟩
  continuous_toFun := by
    apply continuous_sigma
    intro k
    by_cases hk : k ∈ Set.range c
    · simp only [dif_pos hk]
      exact (sourceIntoExtension f c r s).continuous.comp
        ((cell_continuous r _).comp
          (continuous_sigmaMk (σ := fun _ : J => ClosedUnitBall (Fin 2 → ℝ))
            (i := Classical.choose hk)))
    · simp only [dif_neg hk]
      exact (cell_continuous _ _).comp
        (continuous_sigmaMk (σ := fun _ : NewRelators c => ClosedUnitBall (Fin 2 → ℝ))
          (i := ⟨k, hk⟩))

def targetToExtension : C(DiskAttachment s, DiskAttachment (twoAttaching f c r s)) :=
  desc s (boundaryFamilyInclusion K _)
    ((⟨old (twoAttaching f c r s) (boundaryFamilyInclusion (NewRelators c) _),
      old_continuous _ _⟩ : C(DiskAttachment (oneAttaching f r), _)).comp (roseIntoOne f r))
    (relatorDiskIntoExtension f c r s) (by
      rintro ⟨k, a⟩
      change old (twoAttaching f c r s) _ (roseIntoOne f r (s ⟨k, a⟩)) =
        if hk : k ∈ Set.range c then _ else _
      split_ifs with hk
      · have hj : c (Classical.choose hk) = k := Classical.choose_spec hk
        have hs : s ⟨k, a⟩ = diskRoseMap f (r ⟨Classical.choose hk, a⟩) := by
          rw [h ⟨Classical.choose hk, a⟩, hj]
        rw [hs, roseIntoOne_map]
        exact congrArg (sourceIntoExtension f c r s)
          (cell_boundary r _ (boundaryFamilyInclusion_isClosedEmbedding J _).injective
            ⟨Classical.choose hk, a⟩).symm
      · exact (cell_boundary (twoAttaching f c r s) _
          (boundaryFamilyInclusion_isClosedEmbedding (NewRelators c) _).injective
          ⟨⟨k, hk⟩, a⟩).symm)

@[simp] theorem targetToExtension_old (x : Rose B) :
    targetToExtension f c r s h (old s (boundaryFamilyInclusion K _) x) =
      old (twoAttaching f c r s) (boundaryFamilyInclusion (NewRelators c) _)
        (roseIntoOne f r x) := rfl

theorem targetToExtension_cell_image (j : J) (d : ClosedUnitBall (Fin 2 → ℝ)) :
    targetToExtension f c r s h (cell s (boundaryFamilyInclusion K _) ⟨c j, d⟩) =
      sourceIntoExtension f c r s (cell r (boundaryFamilyInclusion J _) ⟨j, d⟩) := by
  change desc _ _ _ _ _ (cell _ _ _) = _
  rw [desc_cell]
  have hk : c j ∈ Set.range c := ⟨j, rfl⟩
  have hj : Classical.choose hk = j := c.injective (Classical.choose_spec hk)
  simp only [relatorDiskIntoExtension, ContinuousMap.coe_mk, dif_pos hk, hj]

theorem targetToExtension_cell_new (k : NewRelators c) (d : ClosedUnitBall (Fin 2 → ℝ)) :
    targetToExtension f c r s h (cell s (boundaryFamilyInclusion K _) ⟨k.val, d⟩) =
      cell (twoAttaching f c r s) (boundaryFamilyInclusion (NewRelators c) _) ⟨k, d⟩ := by
  change desc _ _ _ _ _ (cell _ _ _) = _
  rw [desc_cell]
  simp only [relatorDiskIntoExtension, ContinuousMap.coe_mk, dif_neg k.property]

theorem targetToExtension_source (x : DiskAttachment r) :
    targetToExtension f c r s h (sourceMap f c r s h x) = sourceIntoExtension f c r s x := by
  obtain ⟨z, rfl⟩ := quotientMap_surjective r (boundaryFamilyInclusion J _) x
  cases z with
  | inl x =>
      change targetToExtension f c r s h (sourceMap f c r s h (old r _ x)) = _
      rw [sourceMap_old, targetToExtension_old, roseIntoOne_map]
      rfl
  | inr d =>
      change targetToExtension f c r s h (sourceMap f c r s h (cell r _ d)) = _
      rw [sourceMap_cell, targetToExtension_cell_image]
      rfl

theorem extensionToTarget_source (x : DiskAttachment r) :
    extensionToTarget f c r s h (sourceIntoExtension f c r s x) = sourceMap f c r s h x := rfl

theorem extensionToTarget_inverse (x : DiskAttachment s) :
    extensionToTarget f c r s h (targetToExtension f c r s h x) = x := by
  obtain ⟨z, rfl⟩ := quotientMap_surjective s (boundaryFamilyInclusion K _) x
  cases z with
  | inl x =>
      change extensionToTarget f c r s h (targetToExtension f c r s h (old s _ x)) = _
      rw [targetToExtension_old, extensionToTarget_old, oneToTarget_rose]
      rfl
  | inr d =>
      rcases d with ⟨k, d⟩
      by_cases hk : k ∈ Set.range c
      · obtain ⟨j, rfl⟩ := hk
        change extensionToTarget f c r s h (targetToExtension f c r s h (cell s _ ⟨c j, d⟩)) = _
        rw [targetToExtension_cell_image, extensionToTarget_source, sourceMap_cell]
        rfl
      · change extensionToTarget f c r s h (targetToExtension f c r s h (cell s _ ⟨k, d⟩)) = _
        rw [targetToExtension_cell_new f c r s h ⟨k, hk⟩ d, extensionToTarget_cell]
        rfl

theorem targetToExtension_inverse (x : DiskAttachment (twoAttaching f c r s)) :
    targetToExtension f c r s h (extensionToTarget f c r s h x) = x := by
  obtain ⟨z, rfl⟩ := quotientMap_surjective (twoAttaching f c r s)
    (boundaryFamilyInclusion (NewRelators c) _) x
  cases z with
  | inl x =>
      obtain ⟨z, rfl⟩ := quotientMap_surjective (oneAttaching f r)
        (boundaryFamilyInclusion (NewGenerators f) _) x
      cases z with
      | inl x =>
          change targetToExtension f c r s h
            (extensionToTarget f c r s h (sourceIntoExtension f c r s x)) = _
          rw [extensionToTarget_source, targetToExtension_source]
          rfl
      | inr d =>
          change targetToExtension f c r s h (extensionToTarget f c r s h
            (old (twoAttaching f c r s) _ (cell (oneAttaching f r) _ d))) = _
          rw [extensionToTarget_old, oneToTarget_cell, targetToExtension_old,
            roseIntoOne_cell_new]
          rfl
  | inr d =>
      change targetToExtension f c r s h
        (extensionToTarget f c r s h (cell (twoAttaching f c r s) _ d)) = _
      rw [extensionToTarget_cell, targetToExtension_cell_new]
      rfl

def extensionHomeomorph : DiskAttachment (twoAttaching f c r s) ≃ₜ DiskAttachment s where
  toFun := extensionToTarget f c r s h
  invFun := targetToExtension f c r s h
  left_inv := targetToExtension_inverse f c r s h
  right_inv := extensionToTarget_inverse f c r s h
  continuous_toFun := (extensionToTarget f c r s h).continuous
  continuous_invFun := (targetToExtension f c r s h).continuous

@[simp] theorem extensionHomeomorph_old (x : DiskAttachment r) :
    extensionHomeomorph f c r s h (sourceIntoExtension f c r s x) = sourceMap f c r s h x := rfl

theorem sourceMap_injective : Function.Injective (sourceMap f c r s h) := by
  intro x y hxy
  have he := congrArg (targetToExtension f c r s h) hxy
  rw [targetToExtension_source, targetToExtension_source] at he
  exact (old_injective (oneAttaching f r) (boundaryFamilyInclusion (NewGenerators f) _))
    ((old_injective (twoAttaching f c r s) (boundaryFamilyInclusion (NewRelators c) _)) he)

def extensionModel : Whitehead.DiskExtensionModel (DiskAttachment r) (DiskAttachment s) where
  oneCells := NewGenerators f
  twoCells := NewRelators c
  oneAttaching := oneAttaching f r
  twoAttaching := twoAttaching f c r s
  comparison := (extensionHomeomorph f c r s h).toHomotopyEquiv

theorem extensionModel_map : (extensionModel f c r s h).map = sourceMap f c r s h := by
  apply ContinuousMap.ext
  intro x
  rfl

end FiniteChains.RelativeAttachment.DiskPresentationExtension
