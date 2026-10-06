import RequestProject.StrictOrderChains
import RequestProject.OrderNerveDictionary

/-! Normalization preserves the coefficients of all genuine order simplices. -/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb
variable {P : Type} [PartialOrder P]

noncomputable def ordTriangleCoefficient (t : OrdTri P) : Nerve.Ch P →+ ℤ := by
  classical
  exact FreeAbelianGroup.lift (fun l =>
    if l = [t.1.1, t.1.2.1, t.1.2.2] then 1 else 0)

/-- Reading a flag coefficient in the full nerve agrees with reading its cellular coordinate. -/
theorem ordTriangleCoefficient_encode (t : OrdTri P) (c : OrdTri P →₀ ℤ) :
    ordTriangleCoefficient t (ordNerveChain2 c) = c t := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, Finsupp.add_apply, hc, hd]
  | single w n =>
    have he : [w.1.1, w.1.2.1, w.1.2.2] = [t.1.1, t.1.2.1, t.1.2.2] ↔ w = t := by
      constructor
      · intro h
        apply Subtype.ext
        simp only [List.cons.injEq, and_true] at h
        exact Prod.ext h.1 (Prod.ext h.2.1 h.2.2)
      · rintro rfl
        rfl
    simp [ordNerveChain2, ordTriangleCoefficient, FreeAbelianGroup.lift_apply_of,
      Finsupp.single_apply, he]

theorem normalizeOrdChain2_apply (c : OrdTri P →₀ ℤ) (t : StrictOrdTri P) :
    normalizeOrdChain2 c t = c ((strictOrderIncl P).onF t) := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, Finsupp.add_apply, hc, hd]
  | single w n =>
    rw [normalizeOrdChain2_single]
    by_cases hw : w.1.1 < w.1.2.1 ∧ w.1.2.1 < w.1.2.2
    · have he : (⟨w.1, hw⟩ : StrictOrdTri P) = t ↔ w = (strictOrderIncl P).onF t := by
        constructor <;> intro h <;> apply Subtype.ext
        · exact congrArg (fun u : StrictOrdTri P => u.val) h
        · exact congrArg (fun u : OrdTri P => u.val) h
      simp [normalizeOrdTriangle, hw, Finsupp.single_apply, he]
    · have he : w ≠ (strictOrderIncl P).onF t := by
        intro h
        apply hw
        simpa [h, strictOrderIncl] using t.2
      simp [normalizeOrdTriangle, hw, he]

end FiniteChains.Comb
