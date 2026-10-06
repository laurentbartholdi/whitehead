module

public import RequestProject.ComponentComplex
public import RequestProject.OrderComplexGluing

@[expose] public section

/-! Actual path components of an order complex, as labels of its vertices. -/
namespace FiniteChains.Comb
universe u
variable (P : Type u) [Preorder P]

def orderComponentSetoid : Setoid P where
  r := Reach (orderCx P)
  iseqv := ⟨reach_self (orderCx P), fun ⟨p, hp⟩ => ⟨revPath p, isPath_revPath hp⟩,
    fun hab ⟨_, hp⟩ => hab.trans_path hp⟩

def OrderComponent := Quotient (orderComponentSetoid P)

def orderComponentLabel (p : P) : OrderComponent P := Quotient.mk _ p

variable {P}

theorem orderComponentLabel_eq_iff (a b : P) :
    orderComponentLabel P a = orderComponentLabel P b ↔ Reach (orderCx P) a b :=
  Quotient.eq_iff_equiv

theorem orderComponentLabel_eq_of_le {a b : P} (h : a ≤ b) :
    orderComponentLabel P a = orderComponentLabel P b :=
  Quotient.sound ⟨[ordPos h], isPath_ordPos h⟩

end FiniteChains.Comb
