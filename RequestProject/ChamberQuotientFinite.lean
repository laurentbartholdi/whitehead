import RequestProject.BlockSpinePres

/-! Finiteness of the quotient's cube poset and its order-complex cells. -/

namespace FiniteChains.Davis

open RACG Comb

universe u

variable {V : Type u} [DecidableEq V] [Finite V] (A : CommRel V)

instance : Finite (QCube A) :=
  Finite.of_injective (fun c : QCube A => (c.spx, c.sgn)) (by
    intro c d h
    exact QCube.ext' (congrArg Prod.fst h) (fun v _ =>
      congrFun (congrArg Prod.snd h) v))

instance : Finite (QOld A) := inferInstanceAs (Finite {c : QCube A // ¬ (c.spx = ∅ ∧ c.sgn = 0)})

instance : Finite (orderCx (QOld A)).E :=
  inferInstanceAs (Finite {p : QOld A × QOld A // p.1 ≤ p.2})

instance : Finite (orderCx (QOld A)).F :=
  inferInstanceAs (Finite {p : QOld A × QOld A × QOld A //
    p.1 ≤ p.2.1 ∧ p.2.1 ≤ p.2.2})

end FiniteChains.Davis
