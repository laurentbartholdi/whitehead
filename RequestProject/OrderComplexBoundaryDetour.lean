import RequestProject.OrderComplexLoopRepresentatives
import RequestProject.CmpNerve
import RequestProject.OrderCxMonodromy

/-! Replace a passage through a top cell by an actual path in its remaining boundary. -/
namespace FiniteChains.Comb
variable {P : Type} [PartialOrder P]

theorem boundary_detour {C : P → Prop} {t u v : P}
    (hconn : ConnectedIn (fun x => C x ∧ x < t))
    (hu : C u ∧ u < t) (hv : C v ∧ v < t) :
    ∃ l, IsPath (orderCx P).src (orderCx P).tgt l u v ∧
      PathIn (fun x => C x ∧ x ≠ t) l ∧
      Htpy (orderCx P) u v [ordPos hu.2.le, ordNeg hv.2.le] l := by
  obtain ⟨l, hl, hB⟩ := hconn u v hu hv
  have htop : PathIn (fun x : P => x ≤ t) l :=
    pathIn_mono (fun _ hx => hx.2.le) hB
  have hp : IsPath (orderCx P).src (orderCx P).tgt
      [ordPos hu.2.le, ordNeg hv.2.le] u v := ⟨rfl, rfl, rfl⟩
  have hpT : PathIn (fun x : P => x ≤ t) [ordPos hu.2.le, ordNeg hv.2.le] :=
    pathIn_cons ⟨hu.2.le, le_refl t⟩
      (pathIn_cons ⟨hv.2.le, le_refl t⟩ (pathIn_nil _))
  refine ⟨l, hl, pathIn_mono (fun _ hx => ⟨hx.1, hx.2.ne⟩) hB, ?_⟩
  apply Davis.htpy_of_loop_nil hp hl
  exact htpy_nil_of_pathIn_le_top (A := fun x : P => x ≤ t) (le_refl t)
    (fun _ h => h) hu.2.le (hp.append (isPath_revPath hl))
    (pathIn_append hpT (pathIn_revPath htop))

end FiniteChains.Comb
