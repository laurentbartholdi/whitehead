module

public import RequestProject.ClassicalCWCellularDiskTransfer

@[expose] public section

/-! Transfer a whole relative presentation extension: first its new
one-cells, then its new two-cells. The zero-on-pi2 condition is required
only for the whole model extension, not for either intermediate map. -/

noncomputable section
namespace Whitehead
open scoped Topology Classical
open FiniteChains.RelativeAttachment

variable (K : TwoComplex) {P J₁ J₂ : Type} [TopologicalSpace P]
  (e : ContinuousMap.HomotopyEquiv P K)
  (r₁ : C(BoundaryFamily J₁ (Fin 1 → ℝ), P))
  (r₂ : C(BoundaryFamily J₂ (Fin 2 → ℝ), DiskAttachment r₁))

def oneTwoAttachmentMap : C(P, DiskAttachment r₂) :=
  (⟨old r₂ (boundaryFamilyInclusion J₂ (Fin 2 → ℝ)), old_continuous _ _⟩ :
    C(DiskAttachment r₁, DiskAttachment r₂)).comp
      ⟨old r₁ (boundaryFamilyInclusion J₁ (Fin 1 → ℝ)), old_continuous _ _⟩

structure OneTwoDiskTransfer where
  target : TwoComplex
  oldEmbedding : CWCellEmbedding K target
  comparison : ContinuousMap.HomotopyEquiv (DiskAttachment r₂) target
  square : comparison.toFun.comp (oneTwoAttachmentMap r₁ r₂) =
    oldEmbedding.map.comp e.toFun
  finite : FiniteCells K → Finite J₁ → Finite J₂ → FiniteCells target
  proper : Nonempty J₁ ∨ Nonempty J₂ → ∃ z : target, z ∉ Set.range oldEmbedding.map

def oneTwoDiskTransfer : OneTwoDiskTransfer K e r₁ r₂ := by
  let T₁ := cellularDiskTransfer K e 1 r₁ (Or.inl rfl)
  let T₂ := cellularDiskTransfer T₁.target T₁.comparison 2 r₂ (Or.inr rfl)
  refine {
    target := T₂.target
    oldEmbedding := T₂.oldEmbedding.comp T₁.oldEmbedding
    comparison := T₂.comparison
    square := ?_
    finite := fun hK hJ₁ hJ₂ => T₂.finite (T₁.finite hK hJ₁) hJ₂
    proper := ?_ }
  · apply ContinuousMap.ext
    intro p
    have h₂ := congrArg (fun f : C(DiskAttachment r₁, T₂.target) =>
      f (old r₁ (boundaryFamilyInclusion J₁ (Fin 1 → ℝ)) p)) T₂.square
    have h₁ := congrArg (fun f : C(P, T₁.target) => f p) T₁.square
    exact h₂.trans (congrArg T₂.oldEmbedding.map h₁)
  · intro hJ
    rcases hJ with hJ | hJ
    · obtain ⟨z, hz⟩ := T₁.proper hJ
      refine ⟨T₂.oldEmbedding.map z, ?_⟩
      rintro ⟨x, hx⟩
      exact hz ⟨x, T₂.oldEmbedding.closedEmbedding.injective hx⟩
    · obtain ⟨z, hz⟩ := T₂.proper hJ
      refine ⟨z, ?_⟩
      rintro ⟨x, hx⟩
      exact hz ⟨T₁.oldEmbedding.map x, hx⟩

namespace OneTwoDiskTransfer

theorem killsPi2_iff (T : OneTwoDiskTransfer K e r₁ r₂) :
    KillsPi2 T.oldEmbedding.map ↔ KillsPi2 (oneTwoAttachmentMap r₁ r₂) := by
  apply killsPi2_homotopyEquiv_square_iff e T.comparison
  rw [T.square]

theorem initialIdentification (T : OneTwoDiskTransfer K e r₁ r₂) :
    InitialIdentification T.oldEmbedding.imageSubcomplex T.oldEmbedding.imageHomeomorph :=
  T.oldEmbedding.initialIdentification

end OneTwoDiskTransfer
end Whitehead
