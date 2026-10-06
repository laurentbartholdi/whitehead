import RequestProject.PresCylinderPi1Surjective
import RequestProject.OrderIsoPi1Surjective
import RequestProject.CylinderPi1Surjective

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.PresModel
open Comb
universe u
variable {α J : Type u} (w : J → List (α × Bool)) (hpos : ∀ j, 0 < (w j).length)

include hpos in
/-- The concrete cylinder inclusion surjects onto the presentation fundamental group. -/
theorem presCylinderInclusion_pi1_surjective (a : CylP (aHom w)) :
    Function.Surjective (pi1Map
      (orderCxMap (ConeAdj.inc (S := circSet w)) (fun _ _ h => h)) a) := by
  let e : coneAdjBaseSet (S := circSet w) ≃o CylP (aHom w) := coneAdjBaseOrderIso
  let b : coneAdjBaseSet (S := circSet w) := e.symm a
  intro z
  obtain ⟨q, hq⟩ := presCylinder_pi1_surjective w hpos b z
  obtain ⟨p, hp⟩ := orderIso_pi1_surjective e.symm a q
  refine ⟨p, ?_⟩
  rw (config := { transparency := .default }) [← hp] at hq
  have hmap : pi1Map (orderCxMap (ConeAdj.inc (S := circSet w)) (fun _ _ h => h)) a p =
      pi1Map (subposetHom (coneAdjBaseSet (S := circSet w))) b
        (pi1Map (orderCxMap e.symm e.symm.monotone) a p) := by
    induction p using Quotient.inductionOn with
    | h r =>
      apply Quotient.sound
      have heq : mapPath (orderCxMap (ConeAdj.inc (S := circSet w)) (fun _ _ h => h)) r.val =
          mapPath (subposetHom (coneAdjBaseSet (S := circSet w)))
            (mapPath (orderCxMap e.symm e.symm.monotone) r.val) := by
        simp only [mapPath, List.map_map, Function.comp_def, orderCxMap, iRose]
        rfl
      change Htpy (orderCx (PresPos w)) (ConeAdj.inc (S := circSet w) a) (ConeAdj.inc (S := circSet w) a)
        (mapPath (orderCxMap (ConeAdj.inc (S := circSet w)) (fun _ _ h => h)) r.val)
        (mapPath (subposetHom (coneAdjBaseSet (S := circSet w)))
          (mapPath (orderCxMap e.symm e.symm.monotone) r.val))
      rw (config := { transparency := .default }) [heq]
      exact Htpy.refl _
  exact hmap.trans hq

include hpos in
/-- Every actual presentation loop class comes from the actual rose. -/
theorem presRoseInclusion_pi1_surjective (x : Rose α) :
    Function.Surjective (pi1Map (orderCxMap (iRose w)
      (iRose_monotone w)) x) := by
  intro z
  obtain ⟨q, hq⟩ := presCylinderInclusion_pi1_surjective w hpos (cylIn (aHom w) x) z
  obtain ⟨p, hp⟩ := cylinder_pi1_surjective (aHom w) x q
  refine ⟨p, ?_⟩
  rw (config := { transparency := .default }) [← hp] at hq
  have he : pi1Map (orderCxMap (iRose w)
      (iRose_monotone w)) x p =
      pi1Map (orderCxMap (ConeAdj.inc (S := circSet w)) (fun _ _ h => h))
        (cylIn (aHom w) x)
        (pi1Map (orderCxMap (cylIn (aHom w)) (cylIn_monotone (aHom w))) x p) := by
    induction p using Quotient.inductionOn with
    | h r =>
      apply Quotient.sound
      change Htpy (orderCx (PresPos w)) (iRose w x) (iRose w x)
        (mapPath (orderCxMap (iRose w) _) r.val)
        (mapPath (orderCxMap (ConeAdj.inc (S := circSet w)) _)
          (mapPath (orderCxMap (cylIn (aHom w)) _) r.val))
      simpa only [mapPath, List.map_map, Function.comp_def, orderCxMap, iRose] using
        (Htpy.refl (X := orderCx (PresPos w)) (a := iRose w x) (b := iRose w x)
          (mapPath (orderCxMap (iRose w)
            (iRose_monotone w)) r.val))
  exact he.trans hq

end FiniteChains.PresModel
