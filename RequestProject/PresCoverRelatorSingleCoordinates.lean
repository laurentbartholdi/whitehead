module

public import RequestProject.PresCoverFirstTriangleFibreEquiv

@[expose] public section

namespace FiniteChains.PresModel
open Comb
universe u
variable {α J P : Type u} [PartialOrder P] (w : J → List (α × Bool))
  (f : P → PresPos w) (hf : IsPosetCover f) (hpos : ∀ j, 0 < (w j).length)

/-- An actual single coordinate triangle has exactly its single lifted-apex coefficient. -/
theorem presCoverRelatorChain_single_triangle (p : PresCoverRelator w f) (n : ℤ) :
    presCoverRelatorChain w f hf hpos
      (Finsupp.single (presCoverRelatorTriangle w f hf hpos p) n) = Finsupp.single p n := by
  exact Finsupp.comapDomain_single (presCoverRelatorTriangle w f hf hpos) p n
    (presCoverRelatorTriangle_injective w f hf hpos).injOn

/-- Actual triangles outside all coordinate-triangle fibres contribute no relator coefficients. -/
theorem presCoverRelatorChain_single_off_coordinates (t : StrictOrdTri P) (n : ℤ)
    (ht : ∀ j, (strictOrderCxMap f hf.strictMono).onF t ≠ presRelatorFirstTriangle w hpos j) :
    presCoverRelatorChain w f hf hpos (Finsupp.single t n) = 0 := by
  classical
  ext p
  rw [presCoverRelatorChain_apply]
  have hn : t ≠ presCoverRelatorTriangle w f hf hpos p := by
    intro he
    apply ht p.val.2
    rw [he]
    exact presCoverRelatorTriangle_projection w f hf hpos p
  simp [hn]

/-- A genuine triangle projecting to a coordinate triangle has the actual single apex coordinate. -/
theorem presCoverRelatorChain_single_over_coordinate (j : J) (t : StrictOrdTri P)
    (ht : (strictOrderCxMap f hf.strictMono).onF t = presRelatorFirstTriangle w hpos j)
    (n : ℤ) :
    presCoverRelatorChain w f hf hpos (Finsupp.single t n) =
      Finsupp.single
        (⟨(t.val.2.2, j), congrArg (fun r : StrictOrdTri (PresPos w) => r.val.2.2) ht⟩ :
          PresCoverRelator w f) n := by
  conv_lhs => rw [presCoverRelatorTriangle_unique w f hf hpos
    ⟨(t.val.2.2, j), congrArg (fun r : StrictOrdTri (PresPos w) => r.val.2.2) ht⟩ t ht rfl]
  exact presCoverRelatorChain_single_triangle w f hf hpos _ n

end FiniteChains.PresModel
