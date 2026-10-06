import RequestProject.TopologicalCoverPi2

namespace Whitehead
open scoped unitInterval Topology
variable {E X : Type} [TopologicalSpace E] [TopologicalSpace X]
variable (f : C(E, X)) (r : C(X, E)) (hr : r.comp f = ContinuousMap.id E)

/-- Pull a based square through a retraction, retaining the original base point. -/
def retractSquare {e : E} (q : GenLoop (Fin 2) X (f e)) : GenLoop (Fin 2) E e :=
  ⟨r.comp q.val, fun z hz =>
    (congrArg r (GenLoop.boundary q z hz)).trans (congrArg (fun k => k e) hr)⟩

theorem retractSquare_mapSquare {e : E} (q : GenLoop (Fin 2) E e) :
    retractSquare f r hr (mapSquare f q) = q := by
  apply GenLoop.ext
  intro z
  exact congrArg (fun k => k (q z)) hr

theorem retractSquare_homotopic {e : E} {p q : GenLoop (Fin 2) X (f e)}
    (h : GenLoop.Homotopic p q) :
    GenLoop.Homotopic (retractSquare f r hr p) (retractSquare f r hr q) :=
  h.comp_continuousMap r

/-- A strong deformation retraction gives the based homotopy needed for pi2,
because its deformation fixes the included base point throughout. -/
theorem mapSquare_retractSquare_homotopic
    (H : ContinuousMap.Homotopy (ContinuousMap.id X) (f.comp r))
    (hfix : ∀ t e, H (t, f e) = f e) {e : E} (q : GenLoop (Fin 2) X (f e)) :
    GenLoop.Homotopic q (mapSquare f (retractSquare f r hr q)) := by
  refine ⟨{
    toFun := fun tz => H (tz.1, q tz.2)
    continuous_toFun := H.continuous.comp
      (continuous_fst.prodMk (q.val.continuous.comp continuous_snd))
    map_zero_left := fun z => H.apply_zero (q z)
    map_one_left := fun z => H.apply_one (q z)
    prop' := ?_ }⟩
  intro t z hz
  change H (t, q z) = q z
  rw [GenLoop.boundary q z hz]
  exact hfix t e

include hr in
/-- The map on Mathlib's actual based second homotopy quotient is bijective. -/
theorem pi2Map_bijective_of_deformation_retract
    (H : ContinuousMap.Homotopy (ContinuousMap.id X) (f.comp r))
    (hfix : ∀ t e, H (t, f e) = f e) (e : E) : Function.Bijective (pi2Map f e) := by
  constructor
  · intro a b
    induction a using Quotient.inductionOn with
    | h a =>
      induction b using Quotient.inductionOn with
      | h b =>
        intro he
        have h := retractSquare_homotopic f r hr (Quotient.exact he)
        rw [retractSquare_mapSquare, retractSquare_mapSquare] at h
        exact Quotient.sound h
  · intro q
    induction q using Quotient.inductionOn with
    | h q =>
      refine ⟨Quotient.mk _ (retractSquare f r hr q), ?_⟩
      exact Quotient.sound ((mapSquare_retractSquare_homotopic f r hr H hfix q).symm)

/-- A genuine group isomorphism induced by the inclusion of a deformation retract. -/
noncomputable def pi2DeformationRetractEquiv
    (H : ContinuousMap.Homotopy (ContinuousMap.id X) (f.comp r))
    (hfix : ∀ t e, H (t, f e) = f e) (e : E) :
    HomotopyGroup (Fin 2) E e ≃* HomotopyGroup (Fin 2) X (f e) :=
  MulEquiv.ofBijective (pi2MapHom f e)
    (pi2Map_bijective_of_deformation_retract f r hr H hfix e)

end Whitehead
