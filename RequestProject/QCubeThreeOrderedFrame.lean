module

public import RequestProject.QCubeThreeComponentRecovery

@[expose] public section

/-! Existence of decreasing actual coordinate frames for three-dimensional cubes. -/
namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V : Type} [DecidableEq V] [LinearOrder V] {A : CommRel V}

theorem qCube_three_ordered_frame (c : QCube A) (hc : c.spx.card = 3) :
    ∃ u v w : V, v < u ∧ w < v ∧ c.spx = {u, v, w} := by
  obtain ⟨x, y, z, hxy, hxz, hyz, hs⟩ := Finset.card_eq_three.mp hc
  have perm (a b d : V) (hp : ∀ t : V, t = x ∨ t = y ∨ t = z ↔
      t = a ∨ t = b ∨ t = d) : c.spx = {a, b, d} := by
    ext t
    simp only [hs, Finset.mem_insert, Finset.mem_singleton]
    exact hp t
  rcases lt_or_gt_of_ne hxy with hxy | hxy <;>
    rcases lt_or_gt_of_ne hxz with hxz | hxz <;>
    rcases lt_or_gt_of_ne hyz with hyz | hyz
  · exact ⟨z, y, x, hyz, hxy, perm z y x (by intro t; tauto)⟩
  · exact ⟨y, z, x, hyz, hxz, perm y z x (by intro t; tauto)⟩
  · exact False.elim ((lt_irrefl z) (hxz.trans (hxy.trans hyz)))
  · exact ⟨y, x, z, hxy, hxz, perm y x z (by intro t; tauto)⟩
  · exact ⟨z, x, y, hxz, hxy, perm z x y (by intro t; tauto)⟩
  · exact False.elim ((lt_irrefl y) (hxy.trans (hxz.trans hyz)))
  · exact ⟨x, z, y, hxz, hyz, perm x z y (by intro t; tauto)⟩
  · exact ⟨x, y, z, hxy, hyz, hs⟩

end FiniteChains.Davis
