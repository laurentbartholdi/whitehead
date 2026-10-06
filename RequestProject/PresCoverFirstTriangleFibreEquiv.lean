import RequestProject.PresCoverRelatorNaturality

namespace FiniteChains.PresModel
open Comb
universe u
variable {α J P : Type u} [PartialOrder P] (w : J → List (α × Bool))
  (f : P → PresPos w) (hf : IsPosetCover f) (hpos : ∀ j, 0 < (w j).length)

/-- The fibre of an actual coordinate triangle is exactly the actual relator-apex fibre. -/
noncomputable def presCoverFirstTriangleFibreEquiv (j : J) :
    {t : StrictOrdTri P // (strictOrderCxMap f hf.strictMono).onF t =
      presRelatorFirstTriangle w hpos j} ≃ {p : P // f p = apexOf w j} where
  toFun t := ⟨t.val.val.2.2,
    congrArg (fun r : StrictOrdTri (PresPos w) => r.val.2.2) t.property⟩
  invFun p := ⟨presCoverRelatorTriangle w f hf hpos ⟨(p.val, j), p.property⟩,
    presCoverRelatorTriangle_projection w f hf hpos ⟨(p.val, j), p.property⟩⟩
  left_inv t := by
    apply Subtype.ext
    exact (presCoverRelatorTriangle_unique w f hf hpos
      ⟨(t.val.val.2.2, j), congrArg (fun r : StrictOrdTri (PresPos w) => r.val.2.2) t.property⟩
      t.val t.property rfl).symm
  right_inv p := by
    apply Subtype.ext
    rfl

end FiniteChains.PresModel
