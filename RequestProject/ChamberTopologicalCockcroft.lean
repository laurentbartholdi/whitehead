import RequestProject.OrderRealizationCockcroft
import RequestProject.ChamberQuotientPushdownFillings
import RequestProject.ChamberZConnected

namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V : Type} [DecidableEq V] [Fintype V] {A : CommRel V}
variable {X : Type} [PartialOrder X] [Nonempty X] {att : NeSpx A →o X}

/-- The quotient chamber construction is connected over every connected base. -/
theorem qpos_isConnected (hX : IsConnected (orderCx X)) :
    IsConnected (orderCx (Qpos A X att)) :=
  qpos_isConnected_of_zpos (zpos_isConnected hX)

/-- The quotient chamber construction preserves the genuine topological
Cockcroft property. This transfers the proved cycle-generation and filling
argument through the actual universal cover and the Hurewicz isomorphism. -/
theorem qpos_realization_isCockcroft (hX : IsConnected (orderCx X))
    (hc : Whitehead.IsCockcroft (orderNerveRealization X)) :
    Whitehead.IsCockcroft (orderNerveRealization (Qpos A X att)) := by
  let x : X := Classical.arbitrary X
  apply (orderRealization_isCockcroft_iff (qNew (A := A) (att := att) x)
    (qpos_isConnected hX)).mpr
  exact qCover_homology_pushdown_map_zero x hX ((orderRealization_isCockcroft_iff x hX).mp hc)

theorem qpos_realization_isCockcroft_of_acyclic (hX : IsConnected (orderCx X))
    (ha : Whitehead.Acyclic (orderNerveRealization X)) :
    Whitehead.IsCockcroft (orderNerveRealization (Qpos A X att)) :=
  qpos_realization_isCockcroft hX (Whitehead.isCockcroft_of_acyclic ha)

end FiniteChains.Davis
