import RequestProject.PresStrictPathCylinderReduction

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.PresModel
open Comb
universe u
variable {α J : Type u} (w : J → List (α × Bool)) (hpos : ∀ j, 0 < (w j).length)

include hpos in
/-- The actual cylinder inclusion is surjective on the actual presentation fundamental group. -/
theorem presCylinder_pi1_surjective
    (a : {p : PresPos w // p ∈ coneAdjBaseSet (S := circSet w)}) :
    Function.Surjective (pi1Map (subposetHom (coneAdjBaseSet (S := circSet w))) a) := by
  intro z
  induction z using Quotient.inductionOn with
  | h p =>
    obtain ⟨q, hq, hqc, hh⟩ := exists_presPath_cylinder_reduction w hpos p.val a.val a.val
      a.property a.property p.property
    let r := liftPathIn q hqc
    have hr : IsPath (orderCx (coneAdjBaseSet (S := circSet w))).src
        (orderCx (coneAdjBaseSet (S := circSet w))).tgt r a a :=
      isPath_liftPathIn q hqc a.property a.property hq
    refine ⟨Pi1.mk ⟨r, hr⟩, Quotient.sound ?_⟩
    change Htpy (orderCx (PresPos w)) a.val a.val
      (mapPath (subposetHom (coneAdjBaseSet (S := circSet w))) (liftPathIn q hqc)) p.val
    rw (config := { transparency := .default }) [mapPath_liftPathIn]
    exact hh.symm

end FiniteChains.PresModel
