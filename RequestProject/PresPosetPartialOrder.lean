module

public import RequestProject.PresPosetModel
public import RequestProject.OrderConstructionPartialOrder

@[expose] public section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.PresModel
open Comb
universe u
variable {α J : Type u}

instance rose_partialOrder : PartialOrder (Rose α) :=
  { (inferInstance : Preorder (Rose α)) with
    le_antisymm := by
      intro x y hxy hyx
      change Rose.le x y at hxy
      change Rose.le y x at hyx
      cases x <;> cases y <;> simp_all [Rose.le] }

instance tCirc_partialOrder (w : J → List (α × Bool)) : PartialOrder (TCirc w) :=
  { (inferInstance : Preorder (TCirc w)) with
    le_antisymm := by
      intro x y hxy hyx
      rcases hxy with h | h
      · exact h
      rcases hyx with h' | h'
      · exact h'.symm
      have hl := TCirc.lt_left_tag w h
      have hr := TCirc.lt_right_tag w h'
      rcases hl with hl | hl <;> rcases hr with hr | hr <;> simp_all }

instance presPos_partialOrder (w : J → List (α × Bool)) : PartialOrder (PresPos w) :=
  inferInstanceAs (PartialOrder (ConeAdj (circSet w)))

end FiniteChains.PresModel
