module

public import RequestProject.ClassicalCellAttachmentHausdorff

@[expose] public section

/-! The classical CW structure on an actual disk attachment. The original
cells are retained with their original dimensions and images; all added cells
have the specified dimension. Boundary support is the usual finite lower-cell
condition on the attaching maps, rather than a pre-existing CW structure on the
result. Pending Lean verification. -/

noncomputable section
open scoped Classical
open Set Topology Metric

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.RelativeAttachment

variable {X J : Type} [TopologicalSpace X] [Nonempty X]
  [CWComplex (Set.univ : Set X)]
variable (n : ℕ) (r : BoundaryFamily J (Fin n → ℝ) → X) (hr : Continuous r) (x₀ : X)

/-- The precise cellular condition on the attaching maps. -/
def FiniteLowerBoundary : Prop := ∀ j : J,
  ∃ I : ∀ m, Finset (RelCWComplex.cell (Set.univ : Set X) m),
    ∀ a : UnitBoundary (Fin n → ℝ),
      r ⟨j, a⟩ ∈ ⋃ (m < n) (k ∈ I m), RelCWComplex.closedCell m k

abbrev AttachmentCell (m : ℕ) :=
  RelCWComplex.cell (Set.univ : Set X) m ⊕ {_j : J // m = n}

def attachmentCharacteristic (m : ℕ) : AttachmentCell (X := X) (J := J) n m →
    PartialEquiv (Fin m → ℝ) (DiskAttachment r)
  | Sum.inl j => ClosedEmbeddingCW.imageCharacteristic
      (old r (boundaryFamilyInclusion J (Fin n → ℝ)))
      (old_isClosedEmbedding r _ hr (boundaryFamilyInclusion_isClosedEmbedding J (Fin n → ℝ))) m j
  | Sum.inr ⟨j, h⟩ => by
      subst m
      exact diskCharacteristic r x₀ j

@[simp] theorem attachmentCharacteristic_old (m : ℕ)
    (j : RelCWComplex.cell (Set.univ : Set X) m) :
    attachmentCharacteristic n r hr x₀ m (Sum.inl j) =
      ClosedEmbeddingCW.imageCharacteristic
        (old r (boundaryFamilyInclusion J (Fin n → ℝ)))
        (old_isClosedEmbedding r _ hr (boundaryFamilyInclusion_isClosedEmbedding J (Fin n → ℝ)))
        m j := rfl

@[simp] theorem attachmentCharacteristic_new (j : J) :
    attachmentCharacteristic n r hr x₀ n (Sum.inr ⟨j, rfl⟩) =
      diskCharacteristic r x₀ j := rfl

theorem attachmentCharacteristic_old_image (m : ℕ)
    (j : RelCWComplex.cell (Set.univ : Set X) m) (S : Set (Fin m → ℝ)) :
    attachmentCharacteristic n r hr x₀ m (Sum.inl j) '' S =
      old r (boundaryFamilyInclusion J (Fin n → ℝ)) '' (RelCWComplex.map m j '' S) :=
  ClosedEmbeddingCW.imageCharacteristic_image _ _ m j S

theorem attachmentCharacteristic_source (m : ℕ)
    (j : AttachmentCell (X := X) (J := J) n m) :
    (attachmentCharacteristic n r hr x₀ m j).source = ball 0 1 := by
  rcases j with j | ⟨j, h⟩
  · exact ClosedEmbeddingCW.imageCharacteristic_source _ _ m j
  · subst m
    exact diskCharacteristic_source r x₀ j

theorem attachmentCharacteristic_continuousOn (m : ℕ)
    (j : AttachmentCell (X := X) (J := J) n m) :
    ContinuousOn (attachmentCharacteristic n r hr x₀ m j) (closedBall 0 1) := by
  rcases j with j | ⟨j, h⟩
  · exact ClosedEmbeddingCW.imageCharacteristic_continuousOn _ _ m j
  · subst m
    exact diskCharacteristic_continuousOn r x₀ j

theorem attachmentCharacteristic_continuousOn_symm (m : ℕ)
    (j : AttachmentCell (X := X) (J := J) n m) :
    ContinuousOn (attachmentCharacteristic n r hr x₀ m j).symm
      (attachmentCharacteristic n r hr x₀ m j).target := by
  rcases j with j | ⟨j, h⟩
  · exact ClosedEmbeddingCW.imageCharacteristic_continuousOn_symm _ _ m j
  · subst m
    exact diskCharacteristic_continuousOn_symm r x₀ j

theorem attachmentCharacteristic_pairwiseDisjoint :
    (Set.univ : Set (Σ m, AttachmentCell (X := X) (J := J) n m)).PairwiseDisjoint
      (fun mj => attachmentCharacteristic n r hr x₀ mj.1 mj.2 '' ball 0 1) := by
  rintro ⟨m, i⟩ _ ⟨k, j⟩ _ hne
  change Disjoint (attachmentCharacteristic n r hr x₀ m i '' ball 0 1)
    (attachmentCharacteristic n r hr x₀ k j '' ball 0 1)
  rcases i with i | ⟨i, hi⟩ <;> rcases j with j | ⟨j, hj⟩
  · rw [attachmentCharacteristic_old_image, attachmentCharacteristic_old_image]
    apply Set.disjoint_left.mpr
    rintro _ ⟨a, ha, rfl⟩ ⟨b, hb, he⟩
    have he' := old_injective r (boundaryFamilyInclusion J (Fin n → ℝ)) he
    subst b
    apply Set.disjoint_left.mp (RelCWComplex.disjoint_openCell_of_ne (C := (Set.univ : Set X)) ?_) ha hb
    intro h
    apply hne
    exact congrArg (fun z : Σ m, RelCWComplex.cell (Set.univ : Set X) m =>
      (⟨z.1, Sum.inl z.2⟩ : Σ m, AttachmentCell (X := X) (J := J) n m)) h
  · subst k
    rw [attachmentCharacteristic_new, attachmentCharacteristic_old_image]
    apply (diskCharacteristic_disjoint_old r x₀ j).symm.mono_left
    exact Set.image_subset_range _ _
  · subst m
    rw [attachmentCharacteristic_new, attachmentCharacteristic_old_image]
    apply (diskCharacteristic_disjoint_old r x₀ i).mono_right
    exact Set.image_subset_range _ _
  · subst m
    subst k
    rw [attachmentCharacteristic_new, attachmentCharacteristic_new]
    apply diskCharacteristic_disjoint r x₀
    intro h
    subst j
    exact hne rfl

theorem attachmentCharacteristic_mapsTo (hb : FiniteLowerBoundary n r)
    (m : ℕ) (j : AttachmentCell (X := X) (J := J) n m) :
    ∃ I : ∀ k, Finset (AttachmentCell (X := X) (J := J) n k),
      MapsTo (attachmentCharacteristic n r hr x₀ m j) (sphere 0 1)
        (⋃ (k < m) (i ∈ I k), attachmentCharacteristic n r hr x₀ k i '' closedBall 0 1) := by
  rcases j with j | ⟨j, hm⟩
  · obtain ⟨I, hI⟩ := Topology.CWComplex.mapsTo' (C := (Set.univ : Set X)) m j
    refine ⟨fun k => (I k).image Sum.inl, ?_⟩
    intro x hx
    obtain ⟨k, hk, i, hi, hx'⟩ := by
      simpa only [Set.mem_iUnion] using hI hx
    simp only [Set.mem_iUnion]
    refine ⟨k, hk, Sum.inl i, Finset.mem_image.mpr ⟨i, hi, rfl⟩, ?_⟩
    rw [attachmentCharacteristic_old_image]
    exact ⟨RelCWComplex.map m j x, hx', rfl⟩
  · subst m
    obtain ⟨I, hI⟩ := hb j
    refine ⟨fun k => (I k).image Sum.inl, ?_⟩
    intro x hx
    have hx' : ‖x‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using hx
    rw [attachmentCharacteristic_new, diskCharacteristic_boundary r x₀ j x hx']
    obtain ⟨k, hk, i, hi, ha⟩ := by
      simpa only [Set.mem_iUnion] using hI ⟨x, hx'⟩
    simp only [Set.mem_iUnion]
    refine ⟨k, hk, Sum.inl i, Finset.mem_image.mpr ⟨i, hi, rfl⟩, ?_⟩
    rw [attachmentCharacteristic_old_image]
    exact ⟨r ⟨j, ⟨x, hx'⟩⟩, ha, rfl⟩

variable [T2Space X]

/-- The inherited old cells and the genuinely attached disks form a
classical CW complex on the entire attachment space. -/
def attachmentCW (hb : FiniteLowerBoundary n r) : CWComplex (Set.univ : Set (DiskAttachment r)) where
  cell := AttachmentCell (X := X) (J := J) n
  map := attachmentCharacteristic n r hr x₀
  source_eq := attachmentCharacteristic_source n r hr x₀
  continuousOn := attachmentCharacteristic_continuousOn n r hr x₀
  continuousOn_symm := attachmentCharacteristic_continuousOn_symm n r hr x₀
  pairwiseDisjoint' := attachmentCharacteristic_pairwiseDisjoint n r hr x₀
  mapsTo' := attachmentCharacteristic_mapsTo n r hr x₀ hb
  closed' := by
    intro S _ hS
    apply diskAttachment_isClosed r S
    · apply (CWComplex.closed (Set.univ : Set X) _ (Set.subset_univ _)).mpr
      intro m j
      have hs := (hS m (Sum.inl j)).preimage (old_continuous r (boundaryFamilyInclusion J (Fin n → ℝ)))
      rw [attachmentCharacteristic_old_image] at hs
      simpa only [Set.preimage_inter, Set.preimage_image_eq _ (old_injective r _), RelCWComplex.closedCell] using hs
    · intro j
      have hs := (hS n (Sum.inr ⟨j, rfl⟩)).preimage
        (f := fun x : ClosedUnitBall (Fin n → ℝ) =>
          cell r (boundaryFamilyInclusion J (Fin n → ℝ)) ⟨j, x⟩)
        ((cell_continuous r (boundaryFamilyInclusion J (Fin n → ℝ))).comp continuous_sigmaMk)
      rw [attachmentCharacteristic_new, diskCharacteristic_closedCell] at hs
      have he : (fun x : ClosedUnitBall (Fin n → ℝ) =>
          cell r (boundaryFamilyInclusion J (Fin n → ℝ)) ⟨j, x⟩) ⁻¹'
          (S ∩ Set.range (fun x : ClosedUnitBall (Fin n → ℝ) =>
            cell r (boundaryFamilyInclusion J (Fin n → ℝ)) ⟨j, x⟩)) =
          (fun x : ClosedUnitBall (Fin n → ℝ) =>
            cell r (boundaryFamilyInclusion J (Fin n → ℝ)) ⟨j, x⟩) ⁻¹' S := by
        ext x
        exact and_iff_left ⟨x, rfl⟩
      rwa [he] at hs
  union' := by
    apply Set.eq_univ_of_forall
    rintro (x | d)
    · have hx : x ∈ ⋃ m, ⋃ j : RelCWComplex.cell (Set.univ : Set X) m,
          RelCWComplex.closedCell m j := by rw [CWComplex.union]; trivial
      obtain ⟨m, j, hx⟩ := by simpa only [Set.mem_iUnion] using hx
      apply Set.mem_iUnion.mpr
      refine ⟨m, Set.mem_iUnion.mpr ⟨Sum.inl j, ?_⟩⟩
      rw [attachmentCharacteristic_old_image]
      exact ⟨x, hx, rfl⟩
    · apply Set.mem_iUnion.mpr
      refine ⟨n, Set.mem_iUnion.mpr ⟨Sum.inr ⟨d.val.1, rfl⟩, ?_⟩⟩
      rw [attachmentCharacteristic_new, diskCharacteristic_closedCell]
      exact ⟨d.val.2, cell_of_not_mem r _ d.val d.property⟩

variable (hb : FiniteLowerBoundary n r)

/-- The original space is a literal closed subcomplex, with precisely the
original cell summand in every dimension. -/
def attachmentOldSubcomplex :
    letI := attachmentCW n r hr x₀ hb
    CWComplex.Subcomplex (Set.univ : Set (DiskAttachment r)) := by
  letI := attachmentCW n r hr x₀ hb
  refine {
    carrier := Set.range (old r (boundaryFamilyInclusion J (Fin n → ℝ)))
    I := fun m => Set.range Sum.inl
    closed' := (old_isClosedEmbedding r _ hr
      (boundaryFamilyInclusion_isClosedEmbedding J (Fin n → ℝ))).isClosed_range
    union' := ?_ }
  rw [Set.empty_union]
  ext z
  constructor
  · intro hz
    obtain ⟨m, hz⟩ := Set.mem_iUnion.mp hz
    obtain ⟨j', hz⟩ := Set.mem_iUnion.mp hz
    obtain ⟨j, hj⟩ := j'.property
    have hj' : (j'.1 : AttachmentCell (X := X) (J := J) n m) = Sum.inl j := hj.symm
    rw [hj'] at hz
    change z ∈ attachmentCharacteristic n r hr x₀ m (Sum.inl j) '' ball 0 1 at hz
    rw [attachmentCharacteristic_old_image] at hz
    obtain ⟨y, _, rfl⟩ := hz
    exact ⟨y, rfl⟩
  · rintro ⟨x, rfl⟩
    have hx : x ∈ ⋃ m, ⋃ j : RelCWComplex.cell (Set.univ : Set X) m,
        RelCWComplex.openCell m j := by rw [CWComplex.iUnion_openCell_eq_complex]; trivial
    obtain ⟨m, hx⟩ := Set.mem_iUnion.mp hx
    obtain ⟨j, hx⟩ := Set.mem_iUnion.mp hx
    apply Set.mem_iUnion.mpr
    refine ⟨m, Set.mem_iUnion.mpr ⟨⟨Sum.inl j, ⟨j, rfl⟩⟩, ?_⟩⟩
    change old r _ x ∈ attachmentCharacteristic n r hr x₀ m (Sum.inl j) '' ball 0 1
    rw [attachmentCharacteristic_old_image]
    exact ⟨x, hx, rfl⟩

def attachmentOldCellEquiv (m : ℕ) :
    RelCWComplex.cell (Set.univ : Set X) m ≃
      {j : AttachmentCell (X := X) (J := J) n m // j ∈ Set.range Sum.inl} where
  toFun j := ⟨Sum.inl j, ⟨j, rfl⟩⟩
  invFun := by
    rintro ⟨j, hj⟩
    rcases j with j | j
    · exact j
    · exfalso
      obtain ⟨k, hk⟩ := hj
      cases hk
  left_inv _ := rfl
  right_inv j := by
    rcases j with ⟨j, hj⟩
    obtain ⟨j, rfl⟩ := hj
    rfl

theorem attachment_old_openCell (m : ℕ) (j : RelCWComplex.cell (Set.univ : Set X) m) :
    letI := attachmentCW n r hr x₀ hb
    old r (boundaryFamilyInclusion J (Fin n → ℝ)) '' CWComplex.openCell m j =
      CWComplex.openCell (C := (Set.univ : Set (DiskAttachment r))) m
        (attachmentOldCellEquiv (X := X) (J := J) n m j).val :=
  (attachmentCharacteristic_old_image n r hr x₀ m j (ball 0 1)).symm

end FiniteChains.RelativeAttachment
