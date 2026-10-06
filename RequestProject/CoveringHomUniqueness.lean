import RequestProject.CombCoveringLift
import RequestProject.CombData

namespace FiniteChains.Comb
universe u
variable {X Y Z : Complex2.{u}}

/-- Connected-source lifts into a covering agree once their initial vertex agrees. -/
theorem coveringHom_onV_unique (p : Hom Y Z) (hp : IsCovering p)
    (f g : Hom X Y) (hc : IsConnected X) (a : X.V)
    (ha : f.onV a = g.onV a)
    (he : ∀ e, p.onE (f.onE e) = p.onE (g.onE e)) :
    ∀ v, f.onV v = g.onV v := by
  intro v
  obtain ⟨l, hl⟩ := hc a v
  have hf := isPath_mapPath f hl
  have hg := isPath_mapPath g hl
  rw [← ha] at hg
  have hm : mapPath p (mapPath f l) = mapPath p (mapPath g l) := by
    simp only [mapPath, List.map_map]
    apply List.map_congr_left
    intro e _
    exact Prod.ext (he e.1) rfl
  have hpaths := liftPath_unique hp _ _ _ _ _ hf hg hm
  exact isPath_endpoint_eq (hpaths ▸ hf) hg

end FiniteChains.Comb
