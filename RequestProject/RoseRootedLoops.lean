import RequestProject.RoseStrictEdges
import RequestProject.RootedPathClasses
import RequestProject.OrderReflexiveConjugation
import RequestProject.CombLoopWord

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.PresModel
open Comb
universe u
variable {α : Type u}

/-- Concrete paths from the rose base along the chosen spanning tree. -/
def roseRootPath : Rose α → List ((orderCx (Rose α)).E × Bool)
  | .base => []
  | .mid i => [ordPos (Rose.base_le_edg i false), ordNeg (Rose.mid_le_edg i false)]
  | .edg i b => [ordPos (Rose.base_le_edg i b)]

theorem roseRootPath_isPath (v : Rose α) :
    IsPath (orderCx (Rose α)).src (orderCx (Rose α)).tgt (roseRootPath v) Rose.base v := by
  cases v with
  | base => rfl
  | mid i => exact ⟨rfl, rfl, rfl⟩
  | edg i b => exact ⟨rfl, rfl⟩

/-- The actual four-edge generator loop in the rose. -/
def roseGeneratorLoop (i : α) : Loop (orderCx (Rose α)) Rose.base :=
  ⟨[ordPos (Rose.base_le_edg i false), ordNeg (Rose.mid_le_edg i false),
    ordPos (Rose.mid_le_edg i true), ordNeg (Rose.base_le_edg i true)],
    ⟨rfl, rfl, rfl, rfl, rfl⟩⟩

/-- Every rooted base incidence is a tree loop and has trivial actual class. -/
theorem roseRooted_base (i : α) (b : Bool) :
    Pi1.mk (rootedGermLoop roseRootPath roseRootPath_isPath
      (ordPos (Rose.base_le_edg i b))) = 1 := by
  apply Quotient.sound
  exact htpy_append_revPath (isPath_ordPos (Rose.base_le_edg i b))

/-- The remaining tree incidence at the midpoint has trivial actual class. -/
theorem roseRooted_mid_false (i : α) :
    Pi1.mk (rootedGermLoop roseRootPath roseRootPath_isPath
      (ordPos (Rose.mid_le_edg i false))) = 1 := by
  apply Quotient.sound
  have h := (htpy_revPath_append (isPath_ordPos (Rose.mid_le_edg i false))).congr_append
    (isPath_ordPos (Rose.base_le_edg i false))
    (isPath_revPath (isPath_ordPos (Rose.base_le_edg i false)))
  have h' : Htpy (orderCx (Rose α)) Rose.base Rose.base
      [ordPos (Rose.base_le_edg i false), ordNeg (Rose.mid_le_edg i false),
        ordPos (Rose.mid_le_edg i false), ordNeg (Rose.base_le_edg i false)]
      [ordPos (Rose.base_le_edg i false), ordNeg (Rose.base_le_edg i false)] := by
    simpa only [revPath, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.map_cons, List.map_nil, revGerm, Bool.not, ordPos, ordNeg,
      List.cons_append, List.nil_append] using h
  exact h'.trans (htpy_append_revPath (isPath_ordPos (Rose.base_le_edg i false)))

/-- The non-tree midpoint incidence closes to the concrete generator loop. -/
theorem roseRooted_mid_true (i : α) :
    Pi1.mk (rootedGermLoop roseRootPath roseRootPath_isPath
      (ordPos (Rose.mid_le_edg i true))) = Pi1.mk (roseGeneratorLoop i) := rfl

/-- Reflexive actual rose edges contribute no rooted loop class. -/
theorem roseRooted_self (v : Rose α) :
    Pi1.mk (rootedGermLoop roseRootPath roseRootPath_isPath
      (ordPos (le_refl v))) = 1 := by
  apply Quotient.sound
  have h := (htpy_ordSelf_nil v).congr_append (roseRootPath_isPath v)
    (isPath_revPath (roseRootPath_isPath v))
  have h' : Htpy (orderCx (Rose α)) Rose.base Rose.base
      (roseRootPath v ++ [ordPos (le_refl v)] ++ revPath (roseRootPath v))
      (roseRootPath v ++ revPath (roseRootPath v)) := by
    simpa only [List.append_nil] using h
  exact h'.trans (htpy_append_revPath (roseRootPath_isPath v))

/-- Every positive actual rose germ class is in the image of the concrete generator map. -/
theorem roseRooted_positive_mem_range (e : OrdEdge (Rose α)) :
    Pi1.mk (rootedGermLoop roseRootPath roseRootPath_isPath (e, true)) ∈
      (loopHom (roseGeneratorLoop (α := α))).range := by
  classical
  rcases e with ⟨⟨a, b⟩, h⟩
  by_cases hab : a = b
  · subst b
    change Pi1.mk (rootedGermLoop roseRootPath roseRootPath_isPath
      (ordPos (le_refl a))) ∈ _
    rw [roseRooted_self]
    exact Subgroup.one_mem _
  · let d : StrictOrdEdge (Rose α) := ⟨(a, b), lt_of_le_of_ne h hab⟩
    obtain ⟨i, c, hd | hd⟩ := rose_strict_edge_cases d
    · have he : (⟨(a, b), h⟩ : OrdEdge (Rose α)) =
          (ordPos (Rose.base_le_edg i c)).1 :=
        Subtype.ext (congrArg (fun z : StrictOrdEdge (Rose α) => z.val) hd)
      change Pi1.mk (rootedGermLoop (X := orderCx (Rose α)) roseRootPath roseRootPath_isPath
        ((⟨(a, b), h⟩ : OrdEdge (Rose α)), true)) ∈ _
      rw [he]
      change Pi1.mk (rootedGermLoop roseRootPath roseRootPath_isPath
        (ordPos (Rose.base_le_edg i c))) ∈ _
      rw [roseRooted_base]
      exact Subgroup.one_mem _
    · have he : (⟨(a, b), h⟩ : OrdEdge (Rose α)) =
          (ordPos (Rose.mid_le_edg i c)).1 :=
        Subtype.ext (congrArg (fun z : StrictOrdEdge (Rose α) => z.val) hd)
      change Pi1.mk (rootedGermLoop (X := orderCx (Rose α)) roseRootPath roseRootPath_isPath
        ((⟨(a, b), h⟩ : OrdEdge (Rose α)), true)) ∈ _
      rw [he]
      change Pi1.mk (rootedGermLoop roseRootPath roseRootPath_isPath
        (ordPos (Rose.mid_le_edg i c))) ∈ _
      cases c
      · rw [roseRooted_mid_false]
        exact Subgroup.one_mem _
      · rw [roseRooted_mid_true]
        exact ⟨FreeGroup.of i, loopHom_of _ _⟩

/-- Every oriented actual rose germ class lies in the image of its generator map. -/
theorem roseRooted_mem_range (e : (orderCx (Rose α)).E × Bool) :
    Pi1.mk (rootedGermLoop roseRootPath roseRootPath_isPath e) ∈
      (loopHom (roseGeneratorLoop (α := α))).range := by
  rcases e with ⟨e, b⟩
  cases b
  · have h := rootedGermLoop_rev roseRootPath roseRootPath_isPath (e, true)
    change Pi1.mk (rootedGermLoop roseRootPath roseRootPath_isPath (e, false)) = _ at h
    rw [h]
    exact Subgroup.inv_mem _ (roseRooted_positive_mem_range e)
  · exact roseRooted_positive_mem_range e

/-- The actual rose fundamental group is generated by its concrete generator loops. -/
theorem roseLoopHom_surjective :
    Function.Surjective (loopHom (roseGeneratorLoop (α := α))) := by
  intro z
  induction z using Quotient.inductionOn with
  | h p =>
    have h := rootedPathLoop_eq_prod roseRootPath roseRootPath_isPath p.val
      Rose.base Rose.base p.property
    simp only [rootedPathLoop, roseRootPath, revPath_nil (X := orderCx (Rose α)), List.nil_append,
      List.append_nil] at h
    have hm : (p.val.map (fun e =>
        Pi1.mk (rootedGermLoop roseRootPath roseRootPath_isPath e))).prod ∈
        (loopHom (roseGeneratorLoop (α := α))).range := by
      induction p.val with
      | nil => exact Subgroup.one_mem _
      | cons e l ih =>
        exact Subgroup.mul_mem _ (roseRooted_mem_range e) ih
    rw [← h] at hm
    exact hm

end FiniteChains.PresModel
