module

public import RequestProject.OrderConstructionPartialOrder
public import RequestProject.OrderReflexiveConjugation

@[expose] public section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb
universe u
variable {X S : Type u} [PartialOrder X] [PartialOrder S] (a : S →o X)

/-- Every actual based cylinder loop is homotopic to its retraction onto the base. -/
theorem cylinder_loop_retraction (x : X)
    (p : List ((orderCx (CylP a)).E × Bool))
    (hp : IsPath (orderCx (CylP a)).src (orderCx (CylP a)).tgt p (cylIn a x) (cylIn a x)) :
    Htpy (orderCx (CylP a)) (cylIn a x) (cylIn a x) p
      (mapPath (orderCxMap (cylIn a) (cylIn_monotone a))
        (mapPath (orderCxMap (cylRetr a) (cylRetr_monotone a)) p)) := by
  have h := htpy_loop_mapPath_le_fixed monotone_id (cylCollapse_monotone a)
    (le_cylIn_cylRetr a) (a := cylIn a x) rfl p hp
  have hid : mapPath (orderCxMap id monotone_id) p = p := by
    clear hp h
    induction p with
    | nil => rfl
    | cons e p ih =>
      simp only [mapPath, List.map_cons] at ih ⊢
      exact congrArg (List.cons e) ih
  rw [hid] at h
  simpa only [mapPath, List.map_map, Function.comp_def, orderCxMap, cylCollapse, cylIn, cylRetr, id] using h

/-- The actual base inclusion surjects onto the cylinder fundamental group. -/
theorem cylinder_pi1_surjective (x : X) :
    Function.Surjective (pi1Map (orderCxMap (cylIn a) (cylIn_monotone a)) x) := by
  intro z
  induction z using Quotient.inductionOn with
  | h p =>
    refine ⟨Pi1.mk ⟨mapPath (orderCxMap (cylRetr a) (cylRetr_monotone a)) p.val,
      isPath_mapPath (orderCxMap (cylRetr a) (cylRetr_monotone a)) p.property⟩,
      Quotient.sound ?_⟩
    exact (cylinder_loop_retraction a x p.val p.property).symm

end FiniteChains.Comb
