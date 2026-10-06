import RequestProject.ClosedEmbeddingCWImage
import RequestProject.BallHomotopyExtension

/-! Characteristic maps for an arbitrary family of genuine disks attached
to a literal old space. The norm may be the sup norm used by classical CW
structures. No finiteness of the family is assumed. Pending Lean verification.
-/

noncomputable section
open scoped Classical
open Set Topology

namespace FiniteChains.RelativeAttachment

universe u
variable (J E : Type u) [NormedAddCommGroup E]

abbrev DiskFamily := Σ _ : J, ClosedUnitBall E
abbrev BoundaryFamily := Σ _ : J, UnitBoundary E

def boundaryFamilyInclusion : BoundaryFamily J E → DiskFamily J E :=
  fun a => ⟨a.1, unitBoundaryInclusion E a.2⟩

theorem boundaryFamilyInclusion_range (d : DiskFamily J E) :
    d ∈ Set.range (boundaryFamilyInclusion J E) ↔ ‖d.2.val‖ = 1 := by
  constructor
  · rintro ⟨⟨j, a⟩, rfl⟩
    exact a.property
  · intro hd
    exact ⟨⟨d.1, ⟨d.2.val, hd⟩⟩, by cases d; rfl⟩

theorem boundaryFamilyInclusion_isClosedEmbedding :
    IsClosedEmbedding (boundaryFamilyInclusion J E) := by
  constructor
  · change IsEmbedding (Sigma.map
      (β₁ := fun _ : J => UnitBoundary E) (β₂ := fun _ : J => ClosedUnitBall E) id
      (fun _ : J => (unitBoundaryInclusion E : UnitBoundary E → ClosedUnitBall E)))
    apply (isEmbedding_sigmaMap Function.injective_id).mpr
    intro j
    exact IsEmbedding.inclusion (fun _ h => h.le)
  · apply isClosed_sigma_iff.mpr
    intro j
    have he : (Sigma.mk j) ⁻¹' Set.range (boundaryFamilyInclusion J E) =
        {x : ClosedUnitBall E | ‖x.val‖ = 1} := by
      ext x
      exact boundaryFamilyInclusion_range J E ⟨j, x⟩
    rw [he]
    exact isClosed_eq (continuous_norm.comp continuous_subtype_val) continuous_const

variable {J E}
variable {X : Type u} [TopologicalSpace X]
  (r : BoundaryFamily J E → X) (x₀ : X)

abbrev DiskAttachment := Space r (boundaryFamilyInclusion J E)

/-- A total characteristic function; only its values on the closed ball
are used. Outside the disk it takes the chosen old value. -/
def diskCharacteristicFun (j : J) (x : E) : DiskAttachment r :=
  if hx : ‖x‖ ≤ 1 then cell r (boundaryFamilyInclusion J E) ⟨j, ⟨x, hx⟩⟩
  else old r (boundaryFamilyInclusion J E) x₀

omit [TopologicalSpace X] in
theorem diskCharacteristicFun_closed (j : J) (x : E) (hx : ‖x‖ ≤ 1) :
    diskCharacteristicFun r x₀ j x =
      cell r (boundaryFamilyInclusion J E) ⟨j, ⟨x, hx⟩⟩ := by
  simp only [diskCharacteristicFun, dif_pos hx]

def interiorDiskPoint (j : J) (x : {x : E // ‖x‖ < 1}) :
    {d : DiskFamily J E // d ∉ Set.range (boundaryFamilyInclusion J E)} :=
  ⟨⟨j, ⟨x.val, x.property.le⟩⟩, fun h =>
    (ne_of_lt x.property) ((boundaryFamilyInclusion_range J E _).mp h)⟩

theorem interiorDiskPoint_isEmbedding (j : J) : IsEmbedding (interiorDiskPoint (E := E) j) := by
  apply IsEmbedding.subtypeVal.of_comp_iff.mp
  change IsEmbedding (fun x : {x : E // ‖x‖ < 1} =>
    (⟨j, ⟨x.val, x.property.le⟩⟩ : DiskFamily J E))
  exact IsEmbedding.sigmaMk.comp (IsEmbedding.inclusion
    (fun (x : E) (h : ‖x‖ < 1) => le_of_lt h))

theorem interiorDiskPoint_isOpenEmbedding (j : J) :
    IsOpenEmbedding (interiorDiskPoint (E := E) j) := by
  apply IsOpenEmbedding.of_comp (interiorDiskPoint (E := E) j)
    (boundaryFamilyInclusion_isClosedEmbedding J E).isClosed_range.isOpen_compl.isOpenEmbedding_subtypeVal
  change IsOpenEmbedding (fun x : {x : E // ‖x‖ < 1} =>
    (⟨j, ⟨x.val, x.property.le⟩⟩ : DiskFamily J E))
  exact IsOpenEmbedding.sigmaMk.comp (IsOpenEmbedding.inclusion
    (fun (x : E) (h : ‖x‖ < 1) => le_of_lt h)
    (isOpen_lt (continuous_norm.comp continuous_subtype_val) continuous_const))

omit [TopologicalSpace X] in
theorem diskCharacteristicFun_interior (j : J) (x : {x : E // ‖x‖ < 1}) :
    diskCharacteristicFun r x₀ j x.val =
      fresh r (boundaryFamilyInclusion J E) (interiorDiskPoint j x) := by
  rw [diskCharacteristicFun_closed r x₀ j x.val x.property.le]
  exact cell_of_not_mem r _ _ (interiorDiskPoint j x).property

theorem diskCharacteristicFun_restrict_isEmbedding (j : J) :
    IsEmbedding (fun x : {x : E // ‖x‖ < 1} => diskCharacteristicFun r x₀ j x.val) := by
  have he : (fun x : {x : E // ‖x‖ < 1} => diskCharacteristicFun r x₀ j x.val) =
      fresh r (boundaryFamilyInclusion J E) ∘ interiorDiskPoint j := by
    funext x
    exact diskCharacteristicFun_interior r x₀ j x
  rw [he]
  exact (fresh_isOpenEmbedding r (boundaryFamilyInclusion J E)
    (boundaryFamilyInclusion_isClosedEmbedding J E).isClosed_range).isEmbedding.comp
      (interiorDiskPoint_isEmbedding j)

theorem diskCharacteristicFun_injOn (j : J) :
    Set.InjOn (diskCharacteristicFun r x₀ j) {x : E | ‖x‖ < 1} := by
  intro x hx y hy hxy
  exact congrArg Subtype.val
    ((diskCharacteristicFun_restrict_isEmbedding r x₀ j).injective
      (show diskCharacteristicFun r x₀ j (⟨x, hx⟩ : {x : E // ‖x‖ < 1}).val =
        diskCharacteristicFun r x₀ j (⟨y, hy⟩ : {x : E // ‖x‖ < 1}).val from hxy))

/-- The partial equivalence required by the classical CW definition. -/
def diskCharacteristic (j : J) : PartialEquiv E (DiskAttachment r) :=
  (diskCharacteristicFun_injOn r x₀ j).toPartialEquiv
    (diskCharacteristicFun r x₀ j) {x : E | ‖x‖ < 1}

theorem diskCharacteristic_source (j : J) :
    (diskCharacteristic r x₀ j).source = Metric.ball 0 1 := by
  ext x
  simp only [diskCharacteristic, Set.InjOn.toPartialEquiv,
    Set.BijOn.toPartialEquiv, Metric.mem_ball, dist_zero_right, Set.mem_setOf_eq]

theorem diskCharacteristic_continuousOn (j : J) :
    ContinuousOn (diskCharacteristic r x₀ j) (Metric.closedBall 0 1) := by
  apply continuousOn_iff_continuous_restrict.mpr
  change Continuous (fun x : Metric.closedBall (0 : E) 1 => diskCharacteristic r x₀ j x.val)
  have he : (fun x : Metric.closedBall (0 : E) 1 => diskCharacteristic r x₀ j x.val) =
      fun x : Metric.closedBall (0 : E) 1 =>
        cell r (boundaryFamilyInclusion J E)
          ⟨j, ⟨x.val, by simpa only [Metric.mem_closedBall, dist_zero_right] using x.property⟩⟩ := by
    funext x
    exact diskCharacteristicFun_closed r x₀ j x.val
      (by simpa only [Metric.mem_closedBall, dist_zero_right] using x.property)
  rw [he]
  exact (cell_continuous r (boundaryFamilyInclusion J E)).comp
    (continuous_sigmaMk.comp (continuous_subtype_val.subtype_mk _))

theorem diskCharacteristic_continuousOn_symm (j : J) :
    ContinuousOn (diskCharacteristic r x₀ j).symm (diskCharacteristic r x₀ j).target := by
  have ht : (diskCharacteristic r x₀ j).target =
      (fun x : {x : E // ‖x‖ < 1} => diskCharacteristicFun r x₀ j x.val) '' Set.univ := by
    ext y
    constructor
    · rintro ⟨x, hx, hxy⟩
      exact ⟨⟨x, hx⟩, trivial, hxy⟩
    · rintro ⟨x, _, hxy⟩
      exact ⟨x.val, x.property, hxy⟩
  rw [ht]
  apply (diskCharacteristicFun_restrict_isEmbedding r x₀ j).isInducing.continuousOn_image_iff.mpr
  have he : (diskCharacteristic r x₀ j).symm ∘
      (fun x : {x : E // ‖x‖ < 1} => diskCharacteristicFun r x₀ j x.val) =
      (Subtype.val : {x : E // ‖x‖ < 1} → E) := by
    funext x
    exact (diskCharacteristic r x₀ j).left_inv x.property
  rw [he]
  exact continuous_subtype_val.continuousOn

theorem diskCharacteristic_boundary (j : J) (x : E) (hx : ‖x‖ = 1) :
    diskCharacteristic r x₀ j x =
      old r (boundaryFamilyInclusion J E) (r ⟨j, ⟨x, hx⟩⟩) := by
  rw [show diskCharacteristic r x₀ j x =
      cell r (boundaryFamilyInclusion J E) ⟨j, ⟨x, hx.le⟩⟩ from
        diskCharacteristicFun_closed r x₀ j x hx.le]
  exact cell_boundary r (boundaryFamilyInclusion J E)
    (boundaryFamilyInclusion_isClosedEmbedding J E).injective ⟨j, ⟨x, hx⟩⟩

theorem diskCharacteristic_openCell (j : J) :
    diskCharacteristic r x₀ j '' Metric.ball 0 1 =
      Set.range (fresh r (boundaryFamilyInclusion J E) ∘ interiorDiskPoint j) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx' : ‖x‖ < 1 := by
      simpa only [Metric.mem_ball, dist_zero_right] using hx
    exact ⟨⟨x, hx'⟩, (diskCharacteristicFun_interior r x₀ j ⟨x, hx'⟩).symm⟩
  · rintro ⟨x, rfl⟩
    refine ⟨x.val, ?_, diskCharacteristicFun_interior r x₀ j x⟩
    simpa only [Metric.mem_ball, dist_zero_right] using x.property

theorem diskCharacteristic_closedCell (j : J) :
    diskCharacteristic r x₀ j '' Metric.closedBall 0 1 =
      Set.range (fun x : ClosedUnitBall E => cell r (boundaryFamilyInclusion J E) ⟨j, x⟩) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx' : ‖x‖ ≤ 1 := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hx
    exact ⟨⟨x, hx'⟩, (diskCharacteristicFun_closed r x₀ j x hx').symm⟩
  · rintro ⟨x, rfl⟩
    refine ⟨x.val, ?_, diskCharacteristicFun_closed r x₀ j x.val x.property⟩
    simpa only [Metric.mem_closedBall, dist_zero_right] using x.property

theorem diskCharacteristic_disjoint_old (j : J) :
    Disjoint (diskCharacteristic r x₀ j '' Metric.ball 0 1)
      (Set.range (old r (boundaryFamilyInclusion J E))) := by
  rw [diskCharacteristic_openCell]
  apply (old_fresh_disjoint r (boundaryFamilyInclusion J E)).symm.mono_left
  rintro _ ⟨x, rfl⟩
  exact ⟨interiorDiskPoint j x, rfl⟩

theorem diskCharacteristic_disjoint {j k : J} (hjk : j ≠ k) :
    Disjoint (diskCharacteristic r x₀ j '' Metric.ball 0 1)
      (diskCharacteristic r x₀ k '' Metric.ball 0 1) := by
  rw [diskCharacteristic_openCell, diskCharacteristic_openCell]
  apply Set.disjoint_left.mpr
  rintro _ ⟨x, rfl⟩ ⟨y, hy⟩
  have hd : interiorDiskPoint k y = interiorDiskPoint j x := Sum.inr_injective hy
  exact hjk (congrArg (fun d => d.val.1) hd).symm

theorem old_union_diskCharacteristic_closedCell :
    Set.range (old r (boundaryFamilyInclusion J E)) ∪
      ⋃ j, diskCharacteristic r x₀ j '' Metric.closedBall 0 1 = Set.univ := by
  apply Set.eq_univ_of_forall
  rintro (x | d)
  · exact Or.inl ⟨x, rfl⟩
  · apply Or.inr
    apply Set.mem_iUnion.mpr
    refine ⟨d.val.1, ?_⟩
    rw [diskCharacteristic_closedCell]
    exact ⟨d.val.2, cell_of_not_mem r _ d.val d.property⟩

/-- The weak topology is exactly the topology of the old part and the
individual attached closed disks, including infinitely many disks. -/
theorem diskAttachment_isClosed (S : Set (DiskAttachment r))
    (hOld : IsClosed ((old r (boundaryFamilyInclusion J E)) ⁻¹' S))
    (hDisk : ∀ j, IsClosed ((fun x : ClosedUnitBall E =>
      cell r (boundaryFamilyInclusion J E) ⟨j, x⟩) ⁻¹' S)) : IsClosed S := by
  apply isClosed_coinduced.mpr
  apply isClosed_sum_iff.mpr
  refine ⟨hOld, ?_⟩
  exact isClosed_sigma_iff.mpr hDisk

end FiniteChains.RelativeAttachment
