module

public import RequestProject.ClassicalCellAttachmentMaps

@[expose] public section

/-! Partition an arbitrary disk family and attach its two parts successively.
The homeomorphism is constructed directly from both quotient universal maps. -/

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.RelativeAttachment
open scoped Topology Classical

variable {X J E : Type} [TopologicalSpace X]
  [NormedAddCommGroup E]
  (r : BoundaryFamily J E → X) (p : J → Prop)

def partitionFirstAttaching : BoundaryFamily {j : J // p j} E → X :=
  fun a => r ⟨a.1.val, a.2⟩

def partitionRestAttaching : BoundaryFamily {j : J // ¬p j} E →
    DiskAttachment (partitionFirstAttaching r p) :=
  fun a => old (partitionFirstAttaching r p) (boundaryFamilyInclusion {j // p j} E)
    (r ⟨a.1.val, a.2⟩)

abbrev PartitionAttachment := DiskAttachment (partitionRestAttaching r p)

def partitionDiskForget (s : J → Prop) :
    C(DiskFamily {j : J // s j} E, DiskFamily J E) where
  toFun d := ⟨d.1.val, d.2⟩
  continuous_toFun := continuous_sigma (fun j =>
    continuous_sigmaMk (σ := fun _ : J => ClosedUnitBall E) (i := j.val))

def partitionFirstInto :
    C(DiskAttachment (partitionFirstAttaching r p), DiskAttachment r) :=
  desc (partitionFirstAttaching r p) (boundaryFamilyInclusion {j // p j} E)
    ⟨old r (boundaryFamilyInclusion J E), old_continuous _ _⟩
    ((⟨cell r (boundaryFamilyInclusion J E), cell_continuous _ _⟩ : C(DiskFamily J E, _)).comp
      (partitionDiskForget p))
    (fun a => (cell_boundary r _ (boundaryFamilyInclusion_isClosedEmbedding J E).injective
      ⟨a.1.val, a.2⟩).symm)

def partitionFlatten : C(PartitionAttachment r p, DiskAttachment r) :=
  desc (partitionRestAttaching r p) (boundaryFamilyInclusion {j // ¬p j} E)
    (partitionFirstInto r p)
    ((⟨cell r (boundaryFamilyInclusion J E), cell_continuous _ _⟩ : C(DiskFamily J E, _)).comp
      (partitionDiskForget (fun j => ¬p j)))
    (fun a => (cell_boundary r _ (boundaryFamilyInclusion_isClosedEmbedding J E).injective
      ⟨a.1.val, a.2⟩).symm)

@[simp] theorem partitionFlatten_old (x : X) :
    partitionFlatten r p
      (old (partitionRestAttaching r p) (boundaryFamilyInclusion {j // ¬p j} E)
        (old (partitionFirstAttaching r p) (boundaryFamilyInclusion {j // p j} E) x)) =
      old r (boundaryFamilyInclusion J E) x := rfl

@[simp] theorem partitionFlatten_firstCell (d : DiskFamily {j // p j} E) :
    partitionFlatten r p
      (old (partitionRestAttaching r p) (boundaryFamilyInclusion {j // ¬p j} E)
        (cell (partitionFirstAttaching r p) (boundaryFamilyInclusion {j // p j} E) d)) =
      cell r (boundaryFamilyInclusion J E) ⟨d.1.val, d.2⟩ := by
  change partitionFirstInto r p
    (cell (partitionFirstAttaching r p) (boundaryFamilyInclusion {j // p j} E) d) = _
  unfold partitionFirstInto
  rw [desc_cell]
  rfl

@[simp] theorem partitionFlatten_restCell (d : DiskFamily {j // ¬p j} E) :
    partitionFlatten r p
      (cell (partitionRestAttaching r p) (boundaryFamilyInclusion {j // ¬p j} E) d) =
      cell r (boundaryFamilyInclusion J E) ⟨d.1.val, d.2⟩ := by
  unfold partitionFlatten
  rw [desc_cell]
  rfl

def partitionCellMap : C(DiskFamily J E, PartitionAttachment r p) where
  toFun d := if h : p d.1 then
    old (partitionRestAttaching r p) (boundaryFamilyInclusion {j // ¬p j} E)
      (cell (partitionFirstAttaching r p) (boundaryFamilyInclusion {j // p j} E)
        ⟨⟨d.1, h⟩, d.2⟩)
    else cell (partitionRestAttaching r p) (boundaryFamilyInclusion {j // ¬p j} E)
      ⟨⟨d.1, h⟩, d.2⟩
  continuous_toFun := by
    apply continuous_sigma
    intro j
    by_cases hj : p j
    · simp only [dif_pos hj]
      exact (old_continuous _ _).comp ((cell_continuous _ _).comp
        (continuous_sigmaMk (σ := fun _ : {j : J // p j} => ClosedUnitBall E) (i := ⟨j, hj⟩)))
    · simp only [dif_neg hj]
      exact (cell_continuous _ _).comp
        (continuous_sigmaMk (σ := fun _ : {j : J // ¬p j} => ClosedUnitBall E) (i := ⟨j, hj⟩))

theorem partitionCellMap_boundary (a : BoundaryFamily J E) :
    old (partitionRestAttaching r p) (boundaryFamilyInclusion {j // ¬p j} E)
      (old (partitionFirstAttaching r p) (boundaryFamilyInclusion {j // p j} E) (r a)) =
      partitionCellMap r p (boundaryFamilyInclusion J E a) := by
  rcases a with ⟨j, a⟩
  by_cases hj : p j
  · simp only [partitionCellMap, ContinuousMap.coe_mk, boundaryFamilyInclusion, dif_pos hj]
    exact congrArg (old (partitionRestAttaching r p) (boundaryFamilyInclusion {j // ¬p j} E))
      (cell_boundary (partitionFirstAttaching r p) _
        (boundaryFamilyInclusion_isClosedEmbedding {j // p j} E).injective
        ⟨⟨j, hj⟩, a⟩).symm
  · simp only [partitionCellMap, ContinuousMap.coe_mk, boundaryFamilyInclusion, dif_neg hj]
    exact (cell_boundary (partitionRestAttaching r p) _
      (boundaryFamilyInclusion_isClosedEmbedding {j // ¬p j} E).injective
      ⟨⟨j, hj⟩, a⟩).symm

def partitionRegroup : C(DiskAttachment r, PartitionAttachment r p) :=
  desc r (boundaryFamilyInclusion J E)
    ((⟨old (partitionRestAttaching r p) (boundaryFamilyInclusion {j // ¬p j} E),
      old_continuous _ _⟩ : C(DiskAttachment (partitionFirstAttaching r p), _)).comp
        ⟨old (partitionFirstAttaching r p) (boundaryFamilyInclusion {j // p j} E),
          old_continuous _ _⟩)
    (partitionCellMap r p) (partitionCellMap_boundary r p)

@[simp] theorem partitionRegroup_old (x : X) :
    partitionRegroup r p (old r (boundaryFamilyInclusion J E) x) =
      old (partitionRestAttaching r p) (boundaryFamilyInclusion {j // ¬p j} E)
        (old (partitionFirstAttaching r p) (boundaryFamilyInclusion {j // p j} E) x) := rfl

@[simp] theorem partitionRegroup_firstCell (d : DiskFamily {j // p j} E) :
    partitionRegroup r p (cell r (boundaryFamilyInclusion J E) ⟨d.1.val, d.2⟩) =
      old (partitionRestAttaching r p) (boundaryFamilyInclusion {j // ¬p j} E)
        (cell (partitionFirstAttaching r p) (boundaryFamilyInclusion {j // p j} E) d) := by
  change desc _ _ _ _ _ (cell _ _ _) = _
  rw [desc_cell]
  simp only [partitionCellMap, ContinuousMap.coe_mk, dif_pos d.1.property]

@[simp] theorem partitionRegroup_restCell (d : DiskFamily {j // ¬p j} E) :
    partitionRegroup r p (cell r (boundaryFamilyInclusion J E) ⟨d.1.val, d.2⟩) =
      cell (partitionRestAttaching r p) (boundaryFamilyInclusion {j // ¬p j} E) d := by
  change desc _ _ _ _ _ (cell _ _ _) = _
  rw [desc_cell]
  simp only [partitionCellMap, ContinuousMap.coe_mk, dif_neg d.1.property]

/-- Regrouping preserves each disk point and every old point, with the
original quotient topologies on both sides. -/
def diskAttachmentPartitionHomeomorph : DiskAttachment r ≃ₜ PartitionAttachment r p where
  toFun := partitionRegroup r p
  invFun := partitionFlatten r p
  left_inv z := by
    obtain ⟨w, rfl⟩ := quotientMap_surjective r (boundaryFamilyInclusion J E) z
    cases w with
    | inl x => rfl
    | inr d =>
        by_cases hd : p d.1
        · exact (congrArg (partitionFlatten r p)
            (partitionRegroup_firstCell r p ⟨⟨d.1, hd⟩, d.2⟩)).trans
            (partitionFlatten_firstCell r p ⟨⟨d.1, hd⟩, d.2⟩)
        · exact (congrArg (partitionFlatten r p)
            (partitionRegroup_restCell r p ⟨⟨d.1, hd⟩, d.2⟩)).trans
            (partitionFlatten_restCell r p ⟨⟨d.1, hd⟩, d.2⟩)
  right_inv z := by
    obtain ⟨w, rfl⟩ := quotientMap_surjective (partitionRestAttaching r p)
      (boundaryFamilyInclusion {j // ¬p j} E) z
    cases w with
    | inl y =>
        obtain ⟨w, rfl⟩ := quotientMap_surjective (partitionFirstAttaching r p)
          (boundaryFamilyInclusion {j // p j} E) y
        cases w with
        | inl x => rfl
        | inr d => exact (congrArg (partitionRegroup r p)
            (partitionFlatten_firstCell r p d)).trans (partitionRegroup_firstCell r p d)
    | inr d => exact (congrArg (partitionRegroup r p)
        (partitionFlatten_restCell r p d)).trans (partitionRegroup_restCell r p d)
  continuous_toFun := (partitionRegroup r p).continuous
  continuous_invFun := (partitionFlatten r p).continuous

theorem partitionRestAttaching_continuous (hr : Continuous r) :
    Continuous (partitionRestAttaching r p) := by
  apply (old_continuous _ _).comp
  apply hr.comp
  exact continuous_sigma (fun j =>
    continuous_sigmaMk (σ := fun _ : J => UnitBoundary E) (i := j.val))

end FiniteChains.RelativeAttachment
