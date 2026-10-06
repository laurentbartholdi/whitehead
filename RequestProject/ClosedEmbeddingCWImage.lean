module

public import Mathlib.Topology.CWComplex.Classical.Subcomplex
public import Mathlib.Topology.ContinuousOn
public import RequestProject.ExplicitRelativeAttachment

@[expose] public section

/-! Transport an existing classical CW structure onto its actual closed
embedded image. The cell indices and all characteristic maps are retained.
This applies in particular to the literal old-space inclusion in an
attachment. Pending Lean verification.
-/

noncomputable section
open scoped Classical
open Set Topology Metric

namespace FiniteChains.ClosedEmbeddingCW

universe u
variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] [Nonempty X]
  [CWComplex (Set.univ : Set X)] (f : X → Y) (hf : IsClosedEmbedding f)

def basePartial : PartialEquiv X Y :=
  hf.injective.injOn.toPartialEquiv f Set.univ

def imageCharacteristic (n : ℕ) (j : RelCWComplex.cell (Set.univ : Set X) n) :
    PartialEquiv (Fin n → ℝ) Y :=
  (RelCWComplex.map (C := (Set.univ : Set X)) n j).trans (basePartial f hf)

theorem imageCharacteristic_image (n : ℕ)
    (j : RelCWComplex.cell (Set.univ : Set X) n) (S : Set (Fin n → ℝ)) :
    imageCharacteristic f hf n j '' S =
      f '' (RelCWComplex.map (C := (Set.univ : Set X)) n j '' S) := by
  change (f ∘ RelCWComplex.map (C := (Set.univ : Set X)) n j) '' S = _
  exact Set.image_comp _ _ _

theorem imageCharacteristic_source (n : ℕ)
    (j : RelCWComplex.cell (Set.univ : Set X) n) :
    (imageCharacteristic f hf n j).source = ball 0 1 := by
  rw [imageCharacteristic, PartialEquiv.trans_source]
  change (RelCWComplex.map (C := (Set.univ : Set X)) n j).source ∩
    (RelCWComplex.map (C := (Set.univ : Set X)) n j) ⁻¹' Set.univ = _
  simp only [Set.preimage_univ, Set.inter_univ, RelCWComplex.source_eq]

theorem imageCharacteristic_continuousOn (n : ℕ)
    (j : RelCWComplex.cell (Set.univ : Set X) n) :
    ContinuousOn (imageCharacteristic f hf n j) (closedBall 0 1) :=
  hf.continuous.comp_continuousOn (RelCWComplex.continuousOn n j)

theorem imageCharacteristic_continuousOn_symm (n : ℕ)
    (j : RelCWComplex.cell (Set.univ : Set X) n) :
    ContinuousOn (imageCharacteristic f hf n j).symm
      (imageCharacteristic f hf n j).target := by
  rw [imageCharacteristic, PartialEquiv.trans_target'']
  change ContinuousOn
    ((RelCWComplex.map (C := (Set.univ : Set X)) n j).symm ∘ (basePartial f hf).symm)
    (f '' (Set.univ ∩ (RelCWComplex.map (C := (Set.univ : Set X)) n j).target))
  rw [Set.univ_inter]
  apply hf.isEmbedding.isInducing.continuousOn_image_iff.mpr
  have he : ((RelCWComplex.map (C := (Set.univ : Set X)) n j).symm ∘
      (basePartial f hf).symm) ∘ f =
      (RelCWComplex.map (C := (Set.univ : Set X)) n j).symm := by
    funext x
    exact congrArg (RelCWComplex.map (C := (Set.univ : Set X)) n j).symm
      ((basePartial f hf).left_inv (show x ∈ (basePartial f hf).source from trivial))
  rw [he]
  exact RelCWComplex.continuousOn_symm n j

variable [T2Space X]

/-- The CW structure on the old image has exactly the original cells. -/
def imageCW : CWComplex (Set.range f) where
  cell n := RelCWComplex.cell (Set.univ : Set X) n
  map := imageCharacteristic f hf
  source_eq := imageCharacteristic_source f hf
  continuousOn := imageCharacteristic_continuousOn f hf
  continuousOn_symm := imageCharacteristic_continuousOn_symm f hf
  pairwiseDisjoint' := by
    intro ni _ mj _ hne
    change Disjoint (imageCharacteristic f hf ni.1 ni.2 '' ball 0 1)
      (imageCharacteristic f hf mj.1 mj.2 '' ball 0 1)
    rw [imageCharacteristic_image, imageCharacteristic_image]
    apply Set.disjoint_left.mpr
    rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, he⟩
    have he' : y = x := hf.injective he
    subst y
    exact Set.disjoint_left.mp
      (RelCWComplex.disjoint_openCell_of_ne (C := (Set.univ : Set X)) hne) hx hy
  mapsTo' := by
    intro n j
    obtain ⟨I, hI⟩ := Topology.CWComplex.mapsTo' (C := (Set.univ : Set X)) n j
    refine ⟨I, ?_⟩
    intro x hx
    have hp := hI hx
    simp only [Set.mem_iUnion] at hp ⊢
    obtain ⟨m, hm, k, hk, hp⟩ := hp
    refine ⟨m, hm, k, hk, ?_⟩
    rw [imageCharacteristic_image]
    exact ⟨RelCWComplex.map (C := (Set.univ : Set X)) n j x, hp, rfl⟩
  closed' := by
    intro S hS hclosed
    have hp : IsClosed (f ⁻¹' S) := by
      apply (CWComplex.closed (Set.univ : Set X) (f ⁻¹' S) (Set.subset_univ _)).mpr
      intro n j
      have hc := (hclosed n j).preimage hf.continuous
      rw [imageCharacteristic_image] at hc
      simpa only [Set.preimage_inter, Set.preimage_image_eq _ hf.injective,
        RelCWComplex.closedCell] using hc
    have hc := hf.isClosedMap (f ⁻¹' S) hp
    rwa [Set.image_preimage_eq_of_subset hS] at hc
  union' := by
    ext y
    constructor
    · intro hy
      simp only [Set.mem_iUnion] at hy
      obtain ⟨n, j, hy⟩ := hy
      rw [imageCharacteristic_image] at hy
      obtain ⟨x, _, rfl⟩ := hy
      exact ⟨x, rfl⟩
    · rintro ⟨x, rfl⟩
      have hx : x ∈ ⋃ n, ⋃ j : RelCWComplex.cell (Set.univ : Set X) n,
          RelCWComplex.closedCell n j := by
        rw [CWComplex.union]
        trivial
      simp only [Set.mem_iUnion] at hx ⊢
      obtain ⟨n, j, hx⟩ := hx
      refine ⟨n, j, ?_⟩
      rw [imageCharacteristic_image]
      exact ⟨x, hx, rfl⟩

/-- Each actual original open cell is the corresponding image open cell. -/
theorem imageCW_openCell (n : ℕ) (j : RelCWComplex.cell (Set.univ : Set X) n) :
    letI := imageCW f hf
    f '' CWComplex.openCell (C := (Set.univ : Set X)) n j =
      CWComplex.openCell (C := Set.range f) n j :=
  (imageCharacteristic_image f hf n j (ball 0 1)).symm

end FiniteChains.ClosedEmbeddingCW

namespace FiniteChains.RelativeAttachment

universe u
variable {A X D : Type u} [TopologicalSpace A] [TopologicalSpace X] [TopologicalSpace D]
  [T2Space X] [Nonempty X] [CWComplex (Set.univ : Set X)]

/-- The original classical CW structure, literally retained inside the
explicit attachment space. Construction of the additional cells is separate. -/
def oldCW (r : A → X) (i : A → D) (hr : Continuous r) (hi : IsClosedEmbedding i) :
    CWComplex (Set.range (old r i)) :=
  ClosedEmbeddingCW.imageCW (old r i) (old_isClosedEmbedding r i hr hi)

end FiniteChains.RelativeAttachment
