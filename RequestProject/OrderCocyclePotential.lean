module

public import RequestProject.OrderCxMonodromy

@[expose] public section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb.OrdCocycle
universe u v
variable {P : Type u} [Preorder P] {G : Type v} [Group G]
  (c : OrdCocycle P G)

@[simp] theorem readPath_revPath (p : List ((orderCx P).E × Bool)) :
    c.readPath (revPath p) = (c.readPath p)⁻¹ := by
  induction p with
  | nil => simp [revPath, readPath]
  | cons e p ih =>
    rw [revPath_cons, readPath_append, readPath_cons, readPath_nil,
      readGerm_revGerm, ih, mul_one, readPath_cons, mul_inv_rev]

/-- On a combinatorially simply connected order complex, a cocycle reads one
on every closed edge path. -/
theorem readPath_eq_one_of_simplyConnected (h : SimplyConnected (orderCx P))
    {a : P} {p : List ((orderCx P).E × Bool)}
    (hp : IsPath (orderCx P).src (orderCx P).tgt p a a) : c.readPath p = 1 :=
  c.readPath_htpy (h a p hp)

/-- Cocycle reading is independent of the edge path with prescribed endpoints. -/
theorem readPath_eq_of_simplyConnected (h : SimplyConnected (orderCx P))
    {a b : P} {p q : List ((orderCx P).E × Bool)}
    (hp : IsPath (orderCx P).src (orderCx P).tgt p a b)
    (hq : IsPath (orderCx P).src (orderCx P).tgt q a b) :
    c.readPath p = c.readPath q := by
  have hr := c.readPath_eq_one_of_simplyConnected h
    (isPath_append_iff.mpr ⟨b, hp, isPath_revPath hq⟩)
  rw [readPath_append, readPath_revPath] at hr
  exact mul_inv_eq_one.mp hr

/-- Every group-valued order cocycle on a connected simply connected order
complex has a normalized potential, with no commutativity assumption on the group. -/
theorem exists_potential_of_simplyConnected (hconn : IsConnected (orderCx P))
    (hsc : SimplyConnected (orderCx P)) (a : P) :
    ∃ k : P → G, k a = 1 ∧ ∀ {p q : P}, p ≤ q → k p * c.val p q = k q := by
  classical
  choose paths hpaths using hconn a
  let k : P → G := fun p => c.readPath (paths p)
  refine ⟨k, c.readPath_eq_one_of_simplyConnected hsc (hpaths a), ?_⟩
  intro p q hpq
  have h := c.readPath_eq_of_simplyConnected hsc
    (isPath_append_iff.mpr ⟨p, hpaths p, isPath_single (ordPos hpq)⟩) (hpaths q)
  simpa only [c.readPath_append, c.readPath_cons, c.readPath_nil, c.readGerm_ordPos, mul_one] using h

end FiniteChains.Comb.OrdCocycle
