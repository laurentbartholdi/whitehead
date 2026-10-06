import RequestProject.PresWordEmbedding
import RequestProject.PresCoverRelatorProjectionCoordinates

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.PresModel.PresWordEmbedding
open Comb
universe u
variable {α β J K P Q : Type u} [PartialOrder P] [PartialOrder Q]
variable {w : J → List (α × Bool)} {v : K → List (β × Bool)}
  (h : PresWordEmbedding w v) (hw : ∀ j, 0 < (w j).length) (hv : ∀ j, 0 < (v j).length)

/-- Renaming a presentation preserves its distinguished relator triangle. -/
theorem firstTriangle_map (j : J) :
    (strictOrderCxMap h.posMap h.posMap.strictMono).onF (presRelatorFirstTriangle w hw j) =
      presRelatorFirstTriangle v hv (h.cell j) := by
  apply Subtype.ext
  rfl

/-- A triangle mapped to a distinguished relator triangle was already one,
with the corresponding original relator label. -/
theorem firstTriangle_preimage (t : StrictOrdTri (PresPos w)) (j : K)
    (ht : (strictOrderCxMap h.posMap h.posMap.strictMono).onF t = presRelatorFirstTriangle v hv j) :
    ∃ i : J, h.cell i = j ∧ t = presRelatorFirstTriangle w hw i := by
  have he : h.posFun t.val.2.2 = apexOf v j := congrArg (fun s => s.val.2.2) ht
  have hj : ∃ i : J, h.cell i = j := by
    cases hp : t.val.2.2 with
    | inr i => exact ⟨i, Sum.inr.inj (by simpa only [hp, posFun, apexOf, ConeAdj.apex] using he)⟩
    | inl p => cases p <;> simp only [hp, posFun] at he <;> cases he
  obtain ⟨i, rfl⟩ := hj
  refine ⟨i, rfl, ?_⟩
  apply strictOrderCxMap_onF_injective h.posMap h.posMap.strictMono h.posMap.injective
  exact ht.trans (h.firstTriangle_map hw hv i).symm

variable (f : P → PresPos w) (hf : IsPosetCover f)
  (g : Q → PresPos v) (hg : IsPosetCover g)
  (k : P → Q) (hk : StrictMono k) (hc : ∀ p, g (k p) = h.posMap (f p))

/-- The actual map of lifted relator apices, with labels renamed by the inclusion. -/
def coverRelatorMap (p : PresCoverRelator w f) : PresCoverRelator v g :=
  ⟨(k p.val.1, h.cell p.val.2), (hc p.val.1).trans (congrArg h.posMap p.property)⟩

include hc in
theorem coverTriangle_projection (t : StrictOrdTri P) :
    (strictOrderCxMap g hg.strictMono).onF ((strictOrderCxMap k hk).onF t) =
      (strictOrderCxMap h.posMap h.posMap.strictMono).onF
        ((strictOrderCxMap f hf.strictMono).onF t) := by
  apply Subtype.ext
  exact Prod.ext (hc _) (Prod.ext (hc _) (hc _))

/-- The lift respects the distinguished triangles even when the induced group
map, and hence the map of universal-cover vertices, is not injective. -/
theorem coverRelatorTriangle_map (p : PresCoverRelator w f) :
    (strictOrderCxMap k hk).onF (presCoverRelatorTriangle w f hf hw p) =
      presCoverRelatorTriangle v g hg hv (h.coverRelatorMap f g k hc p) := by
  apply presCoverRelatorTriangle_unique v g hg hv
  · rw (config := { transparency := .default }) [h.coverTriangle_projection f hf g hg k hk hc,
      presCoverRelatorTriangle_projection, h.firstTriangle_map]
    rfl
  · rfl

/-- Every finite relator-coordinate chain transforms by the actual lifted map.
No injectivity or surjectivity of the map between covers is assumed. -/
theorem coverRelatorChain_map (c : StrictOrdTri P →₀ ℤ) :
    presCoverRelatorChain v g hg hv (chain2 (strictOrderCxMap k hk) c) =
      Finsupp.mapDomain (h.coverRelatorMap f g k hc) (presCoverRelatorChain w f hf hw c) := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc' hd' =>
    simp only [map_add, Finsupp.mapDomain_add, hc', hd']
  | single t n =>
    change presCoverRelatorChain v g hg hv
      (Finsupp.mapDomain (strictOrderCxMap k hk).onF (Finsupp.single t n)) = _
    rw (config := { transparency := .default }) [Finsupp.mapDomain_single]
    by_cases ht : ∃ j, (strictOrderCxMap f hf.strictMono).onF t = presRelatorFirstTriangle w hw j
    · obtain ⟨j, hj⟩ := ht
      let p : PresCoverRelator w f :=
        ⟨(t.val.2.2, j), congrArg (fun s : StrictOrdTri (PresPos w) => s.val.2.2) hj⟩
      have he : t = presCoverRelatorTriangle w f hf hw p :=
        presCoverRelatorTriangle_unique w f hf hw p t hj rfl
      rw (config := { transparency := .default }) [he, h.coverRelatorTriangle_map hw hv f hf g hg k hk hc,
        presCoverRelatorChain_single_triangle, presCoverRelatorChain_single_triangle,
        Finsupp.mapDomain_single]
    · rw (config := { transparency := .default }) [presCoverRelatorChain_single_off_coordinates w f hf hw t n
        (fun j hj => ht ⟨j, hj⟩), Finsupp.mapDomain_zero]
      apply presCoverRelatorChain_single_off_coordinates
      intro j hj
      rw (config := { transparency := .default }) [h.coverTriangle_projection f hf g hg k hk hc] at hj
      obtain ⟨i, _, hi⟩ := h.firstTriangle_preimage hw hv _ j hj
      exact ht ⟨i, hi⟩

end FiniteChains.PresModel.PresWordEmbedding
