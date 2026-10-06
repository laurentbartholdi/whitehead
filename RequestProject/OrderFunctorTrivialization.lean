import RequestProject.OrderCocyclePotential
import Mathlib.CategoryTheory.Endomorphism

namespace FiniteChains.Comb
open CategoryTheory
open scoped Classical
universe u v w

variable {P : Type u} [Preorder P] {C : Type v} [Groupoid.{w} C]

/-- A choice of arrows from a base object turns a groupoid-valued order functor
into a cocycle. The opposite group makes multiplication follow path order. -/
noncomputable def orderFunctorCocycle (F : P ⥤ C) (a : P)
    (d : ∀ p : P, F.obj a ⟶ F.obj p) : OrdCocycle P (End (F.obj a))ᵐᵒᵖ where
  val p q := if h : p ≤ q then
    MulOpposite.op (d p ≫ F.map (homOfLE h) ≫ Groupoid.inv (d q)) else 1
  comp {p q r} hpq hqr := by
    simp only [dif_pos hpq, dif_pos hqr, dif_pos (hpq.trans hqr)]
    apply MulOpposite.unop_injective
    change (d p ≫ F.map (homOfLE hpq) ≫ Groupoid.inv (d q)) ≫
      (d q ≫ F.map (homOfLE hqr) ≫ Groupoid.inv (d r)) =
      d p ≫ F.map (homOfLE (hpq.trans hqr)) ≫ Groupoid.inv (d r)
    have hc : homOfLE (hpq.trans hqr) = homOfLE hpq ≫ homOfLE hqr := rfl
    rw [hc, F.map_comp]
    simp only [Category.assoc, Groupoid.inv_eq_inv, IsIso.inv_hom_id_assoc]

/-- Combinatorial simple connectivity makes the arrows to all vertices coherent
with every order morphism, in an arbitrary target groupoid. -/
theorem orderFunctor_exists_coherent_arrows (F : P ⥤ C) (a : P)
    (d : ∀ p : P, F.obj a ⟶ F.obj p)
    (hconn : IsConnected (orderCx P)) (hsc : SimplyConnected (orderCx P)) :
    ∃ k : ∀ p : P, F.obj a ⟶ F.obj p,
      ∀ {p q : P} (h : p ⟶ q), k p ≫ F.map h = k q := by
  obtain ⟨k, _, hk⟩ := (orderFunctorCocycle F a d).exists_potential_of_simplyConnected
    hconn hsc a
  refine ⟨fun p => (k p).unop ≫ d p, ?_⟩
  intro p q h
  have he : homOfLE (leOfHom h) = h := Subsingleton.elim _ _
  have h₁ := congrArg MulOpposite.unop (hk (leOfHom h))
  simp only [orderFunctorCocycle, dif_pos (leOfHom h), MulOpposite.unop_mul,
    MulOpposite.unop_op, End.mul_def, he] at h₁
  have h₂ := congrArg (fun e : End (F.obj a) => e ≫ d q) h₁
  simpa only [Category.assoc, Groupoid.inv_eq_inv, IsIso.inv_hom_id, Category.comp_id] using h₂

/-- The resulting natural isomorphism with a constant functor. -/
theorem orderFunctor_isomorphic_constant (F : P ⥤ C) (a : P)
    (d : ∀ p : P, F.obj a ⟶ F.obj p)
    (hconn : IsConnected (orderCx P)) (hsc : SimplyConnected (orderCx P)) :
    Nonempty ((Functor.const P).obj (F.obj a) ≅ F) := by
  obtain ⟨k, hk⟩ := orderFunctor_exists_coherent_arrows F a d hconn hsc
  refine ⟨NatIso.ofComponents (fun p => asIso (k p)) ?_⟩
  intro p q h
  change 𝟙 (F.obj a) ≫ k q = k p ≫ F.map h
  rw [Category.id_comp, hk h]

end FiniteChains.Comb
