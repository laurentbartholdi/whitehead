module

public import RequestProject.OrderCocycleFlatSections

@[expose] public section

/-! Comparing arbitrary nonabelian cocycles by their action on a torsor. -/
namespace FiniteChains.Comb.OrdCocycle
universe u v
variable {P : Type u} [Preorder P] {G : Type v} [Group G]

structure ComparisonPoint (G : Type v) where
  val : G

instance : MulAction (G × G) (ComparisonPoint G) where
  smul g x := ⟨g.1 * x.val * g.2⁻¹⟩
  one_smul x := by
    change (⟨(1 : G) * x.val * (1 : G)⁻¹⟩ : ComparisonPoint G) = x
    cases x
    simp only [one_mul, inv_one, mul_one]
  mul_smul g h x := by
    change (⟨(g.1 * h.1) * x.val * (g.2 * h.2)⁻¹⟩ : ComparisonPoint G) =
      ⟨g.1 * (h.1 * x.val * h.2⁻¹) * g.2⁻¹⟩
    congr 1
    group

def comparisonOne : ComparisonPoint G := ⟨1⟩

theorem comparisonOne_fixed_iff (g h : G) :
    (g, h) • (comparisonOne : ComparisonPoint G) = comparisonOne ↔ g = h := by
  change (⟨g * 1 * h⁻¹⟩ : ComparisonPoint G) = ⟨1⟩ ↔ g = h
  rw [ComparisonPoint.mk.injEq, mul_one, mul_inv_eq_one]

def product (c d : OrdCocycle P G) : OrdCocycle P (G × G) where
  val a b := (c.val a b, d.val a b)
  comp hab hbd := Prod.ext (c.comp hab hbd) (d.comp hab hbd)

theorem product_readGerm (c d : OrdCocycle P G) (e : (orderCx P).E × Bool) :
    (product c d).readGerm e = (c.readGerm e, d.readGerm e) := by
  obtain ⟨e, b⟩ := e
  cases b <;> rfl

theorem product_readPath (c d : OrdCocycle P G) (p : List ((orderCx P).E × Bool)) :
    (product c d).readPath p = (c.readPath p, d.readPath p) := by
  induction p with
  | nil => rfl
  | cons e p ih =>
    rw [readPath_cons, product_readGerm, ih, readPath_cons, readPath_cons]
    rfl

end FiniteChains.Comb.OrdCocycle
