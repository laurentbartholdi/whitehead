module

public import RequestProject.HomeomorphContinuousMap
public import RequestProject.ClassicalCWGraphCoordinates
public import RequestProject.ClassicalGraphBoundaryWords
public import RequestProject.ClassicalGraphRose

@[expose] public section

/-! A genuine homotopy equivalence from the given original two-dimensional
CW complex to a rose with word disks. The disks retain the original two-cell
index type. Every change of attaching map is a constructed homotopy in the
actual graph; no presentation-realization or homeomorphic-model premise is
assumed. Pending Lean verification. -/

noncomputable section
open scoped Classical unitInterval ContinuousMap
open Set Topology

namespace FiniteChains.ClassicalCW
open ClassicalSkeletonAttachment RelativeAttachment ClassicalGraphModel

variable (K : Whitehead.TwoComplex)

def originalGraphRoot : SkeletonCarrier (Set.univ : Set K) 1 :=
  zeroCellPoint (pointVertex (Classical.choice (inferInstance : Nonempty K)))

def originalGraphTree : Comb.SpanningTree (originalGraph K) :=
  Classical.choose (originalGraph_exists_spanningTree K (originalGraphRoot K))

abbrev OriginalRoseGen :=
  {j : RelCWComplex.cell (Set.univ : Set K) 1 // ¬(originalGraphTree K).isTree j}

abbrev OriginalRoseRel := RelCWComplex.cell (Set.univ : Set K) 2

def originalOneSkeletonRoseEquiv : OneSkeleton K ≃ₕ Rose (OriginalRoseGen K) := by
  letI := zeroSkeleton_discrete (X := K)
  exact (skeletonAsDiskAttachment (Set.univ : Set K) 1).toHomotopyEquiv.trans
    (graphRoseHomotopyEquiv (originalGraphAttaching K)
      (originalGraphAttaching K).continuous (originalGraphTree K))

def originalTopSkeletonHomeomorph : K ≃ₜ SkeletonCarrier (Set.univ : Set K) 3 where
  toFun x := ⟨x, twoComplex_mem_skeleton_three K x⟩
  invFun := Subtype.val
  left_inv _ := rfl
  right_inv _ := Subtype.ext rfl
  continuous_toFun := continuous_id.subtype_mk _
  continuous_invFun := continuous_subtype_val

/-- Literal original characteristic disks, prior to any graph collapse. -/
def originalAsDiskAttachment :
    K ≃ₜ DiskAttachment (skeletonAttachingMap (Set.univ : Set K) 2) :=
  (originalTopSkeletonHomeomorph K).trans
    (skeletonAsDiskAttachment (Set.univ : Set K) 2)

def originalRoseAttaching :
    C(BoundaryFamily (OriginalRoseRel K) (Fin 2 → ℝ), Rose (OriginalRoseGen K)) :=
  (originalOneSkeletonRoseEquiv K).toFun.comp (skeletonAttachingMap (Set.univ : Set K) 2)

def originalRoseDiskEquiv : K ≃ₕ DiskAttachment (originalRoseAttaching K) :=
  (originalAsDiskAttachment K).toHomotopyEquiv.trans
    (diskAttachmentBaseChangeHomotopyEquiv (skeletonAttachingMap (Set.univ : Set K) 2)
      (originalOneSkeletonRoseEquiv K))

theorem originalRoseWords_exists (j : OriginalRoseRel K) :
    ∃ W : BoundaryWords (roseAttaching (OriginalRoseGen K)),
      ((originalRoseAttaching K).comp
        (⟨fun a => ⟨j, a⟩, by
          exact continuous_sigmaMk («σ» := fun _ : OriginalRoseRel K => UnitBoundary (Fin 2 → ℝ)) (i := j)⟩ : C(UnitBoundary (Fin 2 → ℝ),
          BoundaryFamily (OriginalRoseRel K) (Fin 2 → ℝ)))).Homotopic W.boundaryMap :=
  boundaryMap_homotopic_boundaryWords (roseAttaching (OriginalRoseGen K))
    (roseAttaching (OriginalRoseGen K)).continuous _

def originalRoseWords (j : OriginalRoseRel K) :
    BoundaryWords (roseAttaching (OriginalRoseGen K)) :=
  Classical.choose (originalRoseWords_exists K j)

theorem originalRoseWords_spec (j : OriginalRoseRel K) :
    ((originalRoseAttaching K).comp
      (⟨fun a => ⟨j, a⟩, by
          exact continuous_sigmaMk («σ» := fun _ : OriginalRoseRel K => UnitBoundary (Fin 2 → ℝ)) (i := j)⟩ : C(UnitBoundary (Fin 2 → ℝ),
        BoundaryFamily (OriginalRoseRel K) (Fin 2 → ℝ)))).Homotopic
      (originalRoseWords K j).boundaryMap :=
  Classical.choose_spec (originalRoseWords_exists K j)

def originalRoseWordAttaching :
    C(BoundaryFamily (OriginalRoseRel K) (Fin 2 → ℝ), Rose (OriginalRoseGen K)) :=
  ⟨fun a => (originalRoseWords K a.1).boundaryMap a.2,
    continuous_sigma (fun j => (originalRoseWords K j).boundaryMap.continuous)⟩

/-- The cellwise homotopies are jointly continuous for arbitrary disk
families, using their disjoint union topology. -/
def originalRoseAttachingHomotopy :
    (originalRoseAttaching K).Homotopy (originalRoseWordAttaching K) := by
  let H (j : OriginalRoseRel K) := Classical.choice (originalRoseWords_spec K j)
  let F : C(BoundaryFamily (OriginalRoseRel K) (Fin 2 → ℝ), C(I, Rose (OriginalRoseGen K))) :=
    ⟨fun a => ((H a.1).toContinuousMap.comp ⟨Prod.swap, continuous_swap⟩).curry a.2,
      continuous_sigma (fun j =>
        ((H j).toContinuousMap.comp ⟨Prod.swap, continuous_swap⟩).curry.continuous)⟩
  exact {
    toContinuousMap := F.uncurry.comp ⟨Prod.swap, continuous_swap⟩
    map_zero_left := fun a => (H a.1).apply_zero a.2
    map_one_left := fun a => (H a.1).apply_one a.2 }

abbrev OriginalWordDiskModel := DiskAttachment (originalRoseWordAttaching K)

/-- This is an actual homotopy equivalence with the given original K.
The endpoint is a rose plus one genuine normed disk per original two-cell. -/
def originalWordDiskHomotopyEquiv : K ≃ₕ OriginalWordDiskModel K :=
  (originalRoseDiskEquiv K).trans
    (diskAttachingHomotopyEquiv (originalRoseAttaching K) (originalRoseWordAttaching K)
      (originalRoseAttachingHomotopy K))

def originalRelatorWords (j : OriginalRoseRel K) : List (OriginalRoseGen K × Bool) :=
  (originalRoseWords K j).loopWord

def originalRelators (j : OriginalRoseRel K) : FreeGroup (OriginalRoseGen K) :=
  FreeGroup.mk (originalRelatorWords K j)

theorem originalRoseGen_finite (hK : Whitehead.FiniteCells K) : Finite (OriginalRoseGen K) := by
  letI : Finite (Σ n, RelCWComplex.cell (Set.univ : Set K) n) := hK
  letI : Finite (RelCWComplex.cell (Set.univ : Set K) 1) :=
    Finite.of_injective (Sigma.mk 1) (fun _ _ h => eq_of_heq (Sigma.mk.inj_iff.mp h).2)
  infer_instance

theorem originalRoseRel_finite (hK : Whitehead.FiniteCells K) : Finite (OriginalRoseRel K) := by
  letI : Finite (Σ n, RelCWComplex.cell (Set.univ : Set K) n) := hK
  exact Finite.of_injective (Sigma.mk 2) (fun _ _ h => eq_of_heq (Sigma.mk.inj_iff.mp h).2)

end FiniteChains.ClassicalCW
