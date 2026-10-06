module

public import RequestProject.OrderRoseRealizationHomeomorph
public import RequestProject.PresWordEmbedding
public import RequestProject.OrderNervePosetCoverVertexStars

@[expose] public section

/-! Literal generator maps of disk roses, and exact naturality of the
order-rose homeomorphism for generator embeddings. -/

noncomputable section
namespace FiniteChains.ClassicalGraphModel
open RelativeAttachment
open scoped Classical unitInterval

variable {A B : Type} (f : A → B)

def diskRoseMap : C(Rose A, Rose B) :=
  desc (roseAttaching A) (boundaryFamilyInclusion A (Fin 1 → ℝ))
    (ContinuousMap.const _ (roseVertex B))
    ⟨fun d => cell (roseAttaching B) (boundaryFamilyInclusion B _) ⟨f d.1, d.2⟩,
      continuous_sigma (fun a => (cell_continuous _ _).comp
        (continuous_sigmaMk («σ» := fun _ : B => ClosedUnitBall (Fin 1 → ℝ)) (i := f a)))⟩
    (fun a => (cell_boundary (roseAttaching B) _
      (boundaryFamilyInclusion_isClosedEmbedding B _).injective ⟨f a.1, a.2⟩).symm)

@[simp] theorem diskRoseMap_vertex : diskRoseMap f (roseVertex A) = roseVertex B := rfl

@[simp] theorem diskRoseMap_cell (d : DiskFamily A (Fin 1 → ℝ)) :
    diskRoseMap f (cell (roseAttaching A) (boundaryFamilyInclusion A _) d) =
      cell (roseAttaching B) (boundaryFamilyInclusion B _) ⟨f d.1, d.2⟩ := desc_cell ..

end FiniteChains.ClassicalGraphModel

namespace FiniteChains.PresModel
open Comb ClassicalGraphModel RelativeAttachment
open scoped Classical unitInterval

variable {A B J K : Type} {w : J → List (A × Bool)} {v : K → List (B × Bool)}
    (h : PresWordEmbedding w v)

theorem roseMapRealization_copy (a : A) (x : orderNerveRealization (Rose PUnit)) :
    orderNerveRealizationMap h.roseMap h.roseMap.monotone (roseCopyRealization a x) =
      roseCopyRealization (h.gen a) x := by
  change orderNerveRealizationMap h.roseMap h.roseMap.monotone
    (orderNerveRealizationMap (roseCopy a) (roseCopy a).monotone x) = _
  rw [orderNerveRealizationMap_comp]
  have he : h.roseMap ∘ roseCopy a = (roseCopy (h.gen a) : Rose PUnit → Rose B) := by
    funext p
    cases p <;> rfl
  have mapEq (f g : Rose PUnit → Rose B) (hf : Monotone f) (hg : Monotone g)
      (he : f = g) : orderNerveRealizationMap f hf x = orderNerveRealizationMap g hg x := by
    subst g
    rfl
  exact mapEq _ _ _ _ he

theorem orderRoseRealizationHomeomorph_natural (x : orderNerveRealization (Rose A)) :
    orderRoseRealizationHomeomorph B (orderNerveRealizationMap h.roseMap h.roseMap.monotone x) =
      diskRoseMap h.gen (orderRoseRealizationHomeomorph A x) := by
  rcases orderRoseRealization_cases x with rfl | ⟨a, u, rfl⟩
  · change orderRoseRealizationHomeomorph B
        (orderNerveRealizationMap h.roseMap h.roseMap.monotone
          (orderNerveRealizationVertex Rose.base)) = _
    rw [realizedMap_vertex]
    change orderRoseRealizationHomeomorph B (orderRoseBase B) = _
    rw [orderRoseRealizationHomeomorph_base, orderRoseRealizationHomeomorph_base,
      diskRoseMap_vertex]
  · obtain ⟨t, rfl⟩ := orderRoseTraversal_surjective u
    rw [roseMapRealization_copy, orderRoseRealizationHomeomorph_interval,
      orderRoseRealizationHomeomorph_interval, diskRoseMap_cell]

end FiniteChains.PresModel
