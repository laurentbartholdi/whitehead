import RequestProject.ClassicalCellAttachmentMaps
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Tactic

/-! The original cells identify consecutive classical CW skeleta with an
actual disk attachment. Cell families may be infinite, and the statement
also includes dimension zero. The topology is proved from the CW weak
topology and compactness of each individual characteristic disk. -/

noncomputable section
open scoped Classical
open Set Topology Metric

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.ClassicalSkeletonAttachment
open RelativeAttachment

variable {X : Type} [TopologicalSpace X] [T2Space X]
  (C : Set X) [CWComplex C]

abbrev SkeletonCarrier (n : ℕ) :=
  {x : X // x ∈ CWComplex.skeletonLT C (n : ℕ∞)}

/-- The literal inclusion of consecutive original skeleta. -/
def skeletonInclusion (n : ℕ) : C(SkeletonCarrier C n, SkeletonCarrier C (n + 1)) where
  toFun x := ⟨x.val, CWComplex.skeletonLT_mono (C := C)
    (by exact_mod_cast Nat.le_succ n) x.property⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

/-- The original characteristic map restricted to its genuine closed disk. -/
def characteristicDisk (n : ℕ) (j : RelCWComplex.cell C n) :
    C(ClosedUnitBall (Fin n → ℝ), X) where
  toFun x := RelCWComplex.map n j x.val
  continuous_toFun := (RelCWComplex.continuousOn n j).comp_continuous
    continuous_subtype_val (fun x => by
      simpa only [Metric.mem_closedBall, dist_zero_right] using x.property)

def characteristicDiskFamily (n : ℕ) :
    C(DiskFamily (RelCWComplex.cell C n) (Fin n → ℝ), X) where
  toFun d := characteristicDisk C n d.1 d.2
  continuous_toFun := continuous_sigma (fun j => (characteristicDisk C n j).continuous)

/-- The attaching map is exactly the restriction of the original CW maps. -/
def skeletonAttachingMap (n : ℕ) :
    C(BoundaryFamily (RelCWComplex.cell C n) (Fin n → ℝ), SkeletonCarrier C n) where
  toFun a := ⟨RelCWComplex.map n a.1 a.2.val,
    CWComplex.cellFrontier_subset_skeletonLT n a.1
      ⟨a.2.val, by simpa only [Metric.mem_sphere, dist_zero_right] using a.2.property, rfl⟩⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (characteristicDiskFamily C n).continuous.comp
      (boundaryFamilyInclusion_isClosedEmbedding (RelCWComplex.cell C n) (Fin n → ℝ)).continuous

/-- Evaluation of the literal attachment into the original ambient CW space. -/
def skeletonAttachmentOrigin (n : ℕ) : C(DiskAttachment (skeletonAttachingMap C n), X) :=
  desc (skeletonAttachingMap C n)
    (boundaryFamilyInclusion (RelCWComplex.cell C n) (Fin n → ℝ))
    ⟨Subtype.val, continuous_subtype_val⟩ (characteristicDiskFamily C n) (fun _ => rfl)

@[simp] theorem skeletonAttachmentOrigin_old (n : ℕ) (x : SkeletonCarrier C n) :
    skeletonAttachmentOrigin C n
      (old (skeletonAttachingMap C n)
        (boundaryFamilyInclusion (RelCWComplex.cell C n) (Fin n → ℝ)) x) = x.val := rfl

@[simp] theorem skeletonAttachmentOrigin_cell (n : ℕ)
    (j : RelCWComplex.cell C n) (x : ClosedUnitBall (Fin n → ℝ)) :
    skeletonAttachmentOrigin C n
      (cell (skeletonAttachingMap C n)
        (boundaryFamilyInclusion (RelCWComplex.cell C n) (Fin n → ℝ)) ⟨j, x⟩) =
      RelCWComplex.map n j x.val := desc_cell ..

omit [T2Space X] in
private theorem disk_interior_norm (n : ℕ)
    (d : DiskFamily (RelCWComplex.cell C n) (Fin n → ℝ))
    (hd : d ∉ range (boundaryFamilyInclusion (RelCWComplex.cell C n) (Fin n → ℝ))) :
    ‖d.2.val‖ < 1 :=
  lt_of_le_of_ne d.2.property (fun h => hd
    ((boundaryFamilyInclusion_range (RelCWComplex.cell C n) (Fin n → ℝ) d).mpr h))

omit [T2Space X] in
private theorem characteristic_mem_open (n : ℕ) (j : RelCWComplex.cell C n)
    (x : Fin n → ℝ) (hx : ‖x‖ < 1) :
    RelCWComplex.map n j x ∈ CWComplex.openCell n j :=
  ⟨x, by simpa only [Metric.mem_ball, dist_zero_right] using hx, rfl⟩

/-- No new interior point is identified with an old point, or with a
different original open cell. -/
theorem skeletonAttachmentOrigin_injective (n : ℕ) :
    Function.Injective (skeletonAttachmentOrigin C n) := by
  rintro (x | ⟨⟨j, x⟩, hx⟩) (y | ⟨⟨k, y⟩, hy⟩) h
  · apply congrArg Sum.inl
    exact Subtype.ext h
  · change x.val = RelCWComplex.map n k y.val at h
    have hyopen := characteristic_mem_open C n k y.val
      (disk_interior_norm C n ⟨k, y⟩ hy)
    have hopen : x.val ∈ CWComplex.openCell n k := by rw [h]; exact hyopen
    exact False.elim (Set.disjoint_left.mp
      (CWComplex.disjoint_skeletonLT_openCell (C := C) (j := k)
        (show (n : ℕ∞) ≤ n from le_rfl)) x.property hopen)
  · change RelCWComplex.map n j x.val = y.val at h
    have hxopen := characteristic_mem_open C n j x.val
      (disk_interior_norm C n ⟨j, x⟩ hx)
    have hopen : y.val ∈ CWComplex.openCell n j := by rw [← h]; exact hxopen
    exact False.elim (Set.disjoint_left.mp
      (CWComplex.disjoint_skeletonLT_openCell (C := C) (j := j)
        (show (n : ℕ∞) ≤ n from le_rfl)) y.property hopen)
  · change RelCWComplex.map n j x.val = RelCWComplex.map n k y.val at h
    have hxlt := disk_interior_norm C n ⟨j, x⟩ hx
    have hylt := disk_interior_norm C n ⟨k, y⟩ hy
    have hxopen := characteristic_mem_open C n j x.val hxlt
    have hyopen : RelCWComplex.map n j x.val ∈ CWComplex.openCell n k := by
      rw [h]
      exact characteristic_mem_open C n k y.val hylt
    have hlabels : (⟨n, j⟩ : Σ m, RelCWComplex.cell C m) = ⟨n, k⟩ :=
      RelCWComplex.eq_of_not_disjoint_openCell (fun hd => Set.disjoint_left.mp hd hxopen hyopen)
    have hjk : j = k := eq_of_heq (Sigma.mk.inj_iff.mp hlabels).2
    subst k
    have hxy : x.val = y.val := (RelCWComplex.map n j).injOn
      (by rw [RelCWComplex.source_eq]; simpa only [Metric.mem_ball, dist_zero_right] using hxlt)
      (by rw [RelCWComplex.source_eq]; simpa only [Metric.mem_ball, dist_zero_right] using hylt) h
    apply congrArg Sum.inr
    apply Subtype.ext
    change (⟨j, x⟩ : DiskFamily (RelCWComplex.cell C n) (Fin n → ℝ)) = ⟨j, y⟩
    exact congrArg (Sigma.mk j) (Subtype.ext hxy)

theorem skeletonAttachmentOrigin_mem (n : ℕ)
    (z : DiskAttachment (skeletonAttachingMap C n)) :
    skeletonAttachmentOrigin C n z ∈ CWComplex.skeletonLT C (n + 1) := by
  obtain ⟨w, rfl⟩ := quotientMap_surjective (skeletonAttachingMap C n)
    (boundaryFamilyInclusion (RelCWComplex.cell C n) (Fin n → ℝ)) z
  cases w with
  | inl x =>
    exact CWComplex.skeletonLT_mono (C := C)
      (show (n : ℕ∞) ≤ n + 1 from le_self_add) x.property
  | inr d =>
    rw [show quotientMap (skeletonAttachingMap C n)
      (boundaryFamilyInclusion (RelCWComplex.cell C n) (Fin n → ℝ)) (Sum.inr d) =
      cell (skeletonAttachingMap C n)
        (boundaryFamilyInclusion (RelCWComplex.cell C n) (Fin n → ℝ)) d from rfl]
    rcases d with ⟨j, x⟩
    rw [skeletonAttachmentOrigin_cell]
    exact CWComplex.closedCell_subset_skeletonLT n j
      ⟨x.val, by simpa only [Metric.mem_closedBall, dist_zero_right] using x.property, rfl⟩

/-- The evaluation with codomain the next skeleton. -/
def skeletonAttachmentMap (n : ℕ) :
    C(DiskAttachment (skeletonAttachingMap C n), SkeletonCarrier C (n + 1)) := by
  have hm : ∀ z, skeletonAttachmentOrigin C n z ∈
      CWComplex.skeletonLT C ((n + 1 : ℕ) : ℕ∞) := by
    intro z
    simpa only [Nat.cast_add, Nat.cast_one] using skeletonAttachmentOrigin_mem C n z
  exact ⟨fun z => ⟨skeletonAttachmentOrigin C n z, hm z⟩,
    (skeletonAttachmentOrigin C n).continuous.subtype_mk hm⟩

theorem skeletonAttachmentMap_surjective (n : ℕ) :
    Function.Surjective (skeletonAttachmentMap C n) := by
  intro x
  have hx : x.val ∈ (CWComplex.skeletonLT C n : Set X) ∪
      ⋃ j : RelCWComplex.cell C n, CWComplex.closedCell n j := by
    rw [CWComplex.skeletonLT_union_iUnion_closedCell_eq_skeletonLT_succ]
    simpa only [Nat.cast_add, Nat.cast_one] using (show x.val ∈ (CWComplex.skeletonLT C (n + 1) : Set X) from x.property)
  rcases hx with hx | hx
  · refine ⟨old (skeletonAttachingMap C n)
      (boundaryFamilyInclusion (RelCWComplex.cell C n) (Fin n → ℝ)) ⟨x.val, hx⟩, ?_⟩
    exact Subtype.ext rfl
  · obtain ⟨j, hx⟩ := Set.mem_iUnion.mp hx
    obtain ⟨y, hy, hyx⟩ := hx
    let d : ClosedUnitBall (Fin n → ℝ) :=
      ⟨y, by simpa only [Metric.mem_closedBall, dist_zero_right] using hy⟩
    refine ⟨cell (skeletonAttachingMap C n)
      (boundaryFamilyInclusion (RelCWComplex.cell C n) (Fin n → ℝ)) ⟨j, d⟩, ?_⟩
    apply Subtype.ext
    exact (skeletonAttachmentOrigin_cell C n j d).trans hyx

private theorem origin_image_inter_lower_cell (n m : ℕ) (hmn : m < n)
    (j : RelCWComplex.cell C m) (A : Set (DiskAttachment (skeletonAttachingMap C n))) :
    skeletonAttachmentOrigin C n '' A ∩ CWComplex.closedCell m j =
      (Subtype.val '' ((old (skeletonAttachingMap C n)
        (boundaryFamilyInclusion (RelCWComplex.cell C n) (Fin n → ℝ))) ⁻¹' A)) ∩
        CWComplex.closedCell m j := by
  have hcell : CWComplex.closedCell m j ⊆ CWComplex.skeletonLT C (n : ℕ∞) :=
    (CWComplex.closedCell_subset_skeletonLT m j).trans
      (CWComplex.skeletonLT_mono (C := C) (by exact_mod_cast Nat.succ_le_of_lt hmn))
  ext x
  constructor
  · rintro ⟨⟨z, hz, hzx⟩, hx⟩
    let b : SkeletonCarrier C n := ⟨x, hcell hx⟩
    have hzb : z = old (skeletonAttachingMap C n)
        (boundaryFamilyInclusion (RelCWComplex.cell C n) (Fin n → ℝ)) b :=
      skeletonAttachmentOrigin_injective C n hzx
    refine ⟨⟨b, ?_, rfl⟩, hx⟩
    change old _ _ b ∈ A
    rw [← hzb]
    exact hz
  · rintro ⟨⟨b, hb, rfl⟩, hx⟩
    exact ⟨⟨old _ _ b, hb, rfl⟩, hx⟩

private theorem origin_image_inter_top_cell (n : ℕ) (j : RelCWComplex.cell C n)
    (A : Set (DiskAttachment (skeletonAttachingMap C n))) :
    skeletonAttachmentOrigin C n '' A ∩ CWComplex.closedCell n j =
      characteristicDisk C n j '' ((fun x : ClosedUnitBall (Fin n → ℝ) =>
        cell (skeletonAttachingMap C n)
          (boundaryFamilyInclusion (RelCWComplex.cell C n) (Fin n → ℝ)) ⟨j, x⟩) ⁻¹' A) := by
  ext x
  constructor
  · rintro ⟨⟨z, hz, hzx⟩, ⟨y, hy, hyx⟩⟩
    let d : ClosedUnitBall (Fin n → ℝ) :=
      ⟨y, by simpa only [Metric.mem_closedBall, dist_zero_right] using hy⟩
    have hdz : cell (skeletonAttachingMap C n)
        (boundaryFamilyInclusion (RelCWComplex.cell C n) (Fin n → ℝ)) ⟨j, d⟩ = z :=
      skeletonAttachmentOrigin_injective C n
        ((skeletonAttachmentOrigin_cell C n j d).trans (hyx.trans hzx.symm))
    refine ⟨d, ?_, hyx⟩
    change cell _ _ ⟨j, d⟩ ∈ A
    rw [hdz]
    exact hz
  · rintro ⟨d, hd, hdx⟩
    exact ⟨⟨cell _ _ ⟨j, d⟩, hd, (skeletonAttachmentOrigin_cell C n j d).trans hdx⟩,
      ⟨d.val, by simpa only [Metric.mem_closedBall, dist_zero_right] using d.property, hdx⟩⟩

/-- Weak topology is checked cell by cell; no compactness of the family
or finiteness of either skeleton is used. -/
theorem skeletonAttachmentOrigin_isClosedMap (n : ℕ) :
    IsClosedMap (skeletonAttachmentOrigin C n) := by
  intro A hA
  have hupper : skeletonAttachmentOrigin C n '' A ⊆ CWComplex.skeletonLT C (n + 1) := by
    rintro _ ⟨z, _, rfl⟩
    exact skeletonAttachmentOrigin_mem C n z
  apply CWComplex.isClosed_of_disjoint_openCell_or_isClosed_inter_closedCell
    (hupper.trans (CWComplex.skeletonLT C (n + 1)).subset_complex)
  intro m _hm j
  rcases lt_trichotomy m n with hmn | hmn | hnm
  · right
    rw [origin_image_inter_lower_cell C n m hmn j A]
    apply IsClosed.inter _ CWComplex.isClosed_closedCell
    exact (CWComplex.skeletonLT C (n : ℕ∞)).closed.isClosedMap_subtype_val _
      (hA.preimage (old_continuous _ _))
  · right
    subst m
    rw [origin_image_inter_top_cell C n j A]
    letI : CompactSpace (ClosedUnitBall (Fin n → ℝ)) :=
      isCompact_iff_compactSpace.mp (by
        convert isCompact_closedBall (0 : Fin n → ℝ) 1 using 1
        ext x
        simp only [Metric.mem_closedBall, dist_zero_right]
        rfl)
    have hc : IsClosed ((fun x : ClosedUnitBall (Fin n → ℝ) =>
        cell (skeletonAttachingMap C n)
          (boundaryFamilyInclusion (RelCWComplex.cell C n) (Fin n → ℝ)) ⟨j, x⟩) ⁻¹' A) :=
      hA.preimage ((cell_continuous _ _).comp continuous_sigmaMk)
    exact (hc.isCompact.image (characteristicDisk C n j).continuous).isClosed
  · left
    exact (CWComplex.disjoint_skeletonLT_openCell (C := C) (j := j)
      (show (n : ℕ∞) + 1 ≤ m by exact_mod_cast Nat.succ_le_of_lt hnm)).mono_left hupper

theorem skeletonAttachmentMap_isClosedMap (n : ℕ) :
    IsClosedMap (skeletonAttachmentMap C n) := by
  intro A hA
  have he : skeletonAttachmentMap C n '' A =
      Subtype.val ⁻¹' (skeletonAttachmentOrigin C n '' A) := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z, hz, rfl⟩
    · rintro ⟨z, hz, hzx⟩
      exact ⟨z, hz, Subtype.ext hzx⟩
  rw [he]
  exact (skeletonAttachmentOrigin_isClosedMap C n A hA).preimage continuous_subtype_val

/-- The actual attachment is homeomorphic to the next original skeleton. -/
def skeletonAttachmentHomeomorph (n : ℕ) :
    DiskAttachment (skeletonAttachingMap C n) ≃ₜ SkeletonCarrier C (n + 1) :=
  (Equiv.ofBijective (skeletonAttachmentMap C n)
    ⟨fun _ _ h => skeletonAttachmentOrigin_injective C n (congrArg Subtype.val h),
      skeletonAttachmentMap_surjective C n⟩).toHomeomorphOfContinuousClosed
    (skeletonAttachmentMap C n).continuous (skeletonAttachmentMap_isClosedMap C n)

/-- The same identification in the skeleton-to-attachment direction. -/
def skeletonAsDiskAttachment (n : ℕ) :
    SkeletonCarrier C (n + 1) ≃ₜ DiskAttachment (skeletonAttachingMap C n) :=
  (skeletonAttachmentHomeomorph C n).symm

@[simp] theorem skeletonAttachmentHomeomorph_old_eq (n : ℕ) (x : SkeletonCarrier C n) :
    skeletonAttachmentHomeomorph C n
      (old (skeletonAttachingMap C n)
        (boundaryFamilyInclusion (RelCWComplex.cell C n) (Fin n → ℝ)) x) =
      skeletonInclusion C n x := rfl

@[simp] theorem skeletonAsDiskAttachment_inclusion (n : ℕ) (x : SkeletonCarrier C n) :
    skeletonAsDiskAttachment C n (skeletonInclusion C n x) =
      old (skeletonAttachingMap C n)
        (boundaryFamilyInclusion (RelCWComplex.cell C n) (Fin n → ℝ)) x := by
  rw [← skeletonAttachmentHomeomorph_old_eq C n x]
  exact (skeletonAttachmentHomeomorph C n).symm_apply_apply _

@[simp] theorem skeletonAttachmentHomeomorph_old (n : ℕ) (x : SkeletonCarrier C n) :
    (skeletonAttachmentHomeomorph C n
      (old (skeletonAttachingMap C n)
        (boundaryFamilyInclusion (RelCWComplex.cell C n) (Fin n → ℝ)) x)).val = x.val := rfl

@[simp] theorem skeletonAttachmentHomeomorph_cell (n : ℕ)
    (j : RelCWComplex.cell C n) (x : ClosedUnitBall (Fin n → ℝ)) :
    (skeletonAttachmentHomeomorph C n
      (cell (skeletonAttachingMap C n)
        (boundaryFamilyInclusion (RelCWComplex.cell C n) (Fin n → ℝ)) ⟨j, x⟩)).val =
      RelCWComplex.map n j x.val := skeletonAttachmentOrigin_cell C n j x

end FiniteChains.ClassicalSkeletonAttachment
