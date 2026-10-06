import RequestProject.PosetCoverPullback
import RequestProject.NerveUpperSectionReflection
import RequestProject.TruncatedCubePoset

/-! Pulling a genuine old-cell covering back to the actual truncated block. -/
namespace FiniteChains.Davis
open RACG Mirror Comb Nerve
variable {V P : Type} [DecidableEq V] [PartialOrder P] {A : CommRel V}
  (f : P → QOld A)

abbrev TruncatedCover := PosetCoverPullback f (truncatedCellRetraction (A := A))

abbrev truncatedCoverProjection : TruncatedCover f → TruncatedCell A :=
  posetPullbackProjection f truncatedCellRetraction

abbrev truncatedCoverRetraction : TruncatedCover f → P :=
  posetPullbackOriginal f truncatedCellRetraction

theorem truncatedCoverProjection_isPosetCover (hf : IsPosetCover f) :
    IsPosetCover (truncatedCoverProjection f) :=
  hf.pullback truncatedCellRetraction truncatedCellRetraction_monotone

def truncatedCoverSection (p : P) : TruncatedCover f :=
  ⟨(p, oldCellIncl (f p)), rfl⟩

theorem truncatedCoverSection_monotone (hf : Monotone f) :
    Monotone (truncatedCoverSection f) := fun _ _ h => ⟨h, oldCellIncl_monotone (hf h)⟩

omit [DecidableEq V] [PartialOrder P] in
@[simp] theorem truncatedCoverRetraction_section (p : P) :
    truncatedCoverRetraction f (truncatedCoverSection f p) = p := rfl

theorem truncatedCover_le_section_retraction (p : TruncatedCover f) :
    p ≤ truncatedCoverSection f (truncatedCoverRetraction f p) := by
  refine ⟨le_refl _, ?_⟩
  change p.1.2 ≤ oldCellIncl (f p.1.1)
  rw [p.2]
  exact truncatedCell_le_retraction p.1.2

/-- Actual filling reflection in every old-cell covering, without a homology hypothesis. -/
theorem truncatedCoverRetraction_reflects_boundaries (hf : Monotone f)
    (c : Ch (TruncatedCover f)) (hc : c ∈ Inc (TruncatedCover f))
    (hcyc : Nerve.bdry c = 0)
    (hbound : ∃ y ∈ Inc P, Nerve.bdry y = cmap (truncatedCoverRetraction f) c) :
    ∃ y ∈ Inc (TruncatedCover f), Nerve.bdry y = c :=
  boundary_reflection_of_upper_section (truncatedCoverRetraction f) (truncatedCoverSection f)
    (posetPullbackOriginal_monotone f _) (truncatedCoverSection_monotone f hf)
    (truncatedCover_le_section_retraction f) c hc hcyc hbound

end FiniteChains.Davis
