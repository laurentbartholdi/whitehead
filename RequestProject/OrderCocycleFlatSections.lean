import RequestProject.OrderCocyclePotential

/-! Flat sections for arbitrary group actions, retaining nonabelian monodromy. -/
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb.OrdCocycle
universe u v w
variable {P : Type u} [Preorder P] {G : Type v} [Group G]
  {Ω : Type w} [MulAction G Ω] (c : OrdCocycle P G)

def IsFlatSection (s : P → Ω) : Prop :=
  ∀ {a b}, a ≤ b → c.val a b • s b = s a

theorem IsFlatSection.readGerm {s : P → Ω} (hs : c.IsFlatSection s)
    (e : (orderCx P).E × Bool) :
    c.readGerm e • s (germTgt (orderCx P).src (orderCx P).tgt e) =
      s (germSrc (orderCx P).src (orderCx P).tgt e) := by
  obtain ⟨e, b⟩ := e
  cases b with
  | true => exact hs e.2
  | false =>
    change (c.val e.1.1 e.1.2)⁻¹ • s e.1.1 = s e.1.2
    rw [← hs e.2, inv_smul_smul]

theorem IsFlatSection.readPath {s : P → Ω} (hs : c.IsFlatSection s)
    {a b : P} {p : List ((orderCx P).E × Bool)}
    (hp : IsPath (orderCx P).src (orderCx P).tgt p a b) :
    c.readPath p • s b = s a := by
  induction p generalizing a with
  | nil => cases hp; simp
  | cons e p ih =>
    obtain ⟨ha, hp⟩ := hp
    rw [readPath_cons, mul_smul, ih hp, IsFlatSection.readGerm c hs e]
    exact congrArg s ha.symm

/-- Flat sections at the base point are fixed by every actual loop, without any
commutativity or faithfulness assumption on the action. -/
theorem IsFlatSection.loop_fixed {s : P → Ω} (hs : c.IsFlatSection s)
    {a : P} (p : Loop (orderCx P) a) : c.monodromy a (Pi1.mk p) • s a = s a :=
  IsFlatSection.readPath c hs p.2

theorem flat_transport {a b d : P} (hab : a ≤ b) (hbd : b ≤ d) (x : Ω) :
    c.val b d • ((c.val a d)⁻¹ • x) = (c.val a b)⁻¹ • x := by
  rw [← c.comp hab hbd, mul_inv_rev, mul_smul, smul_inv_smul]

end FiniteChains.Comb.OrdCocycle
