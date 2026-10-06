import RequestProject.LocalSystemPosetCover
import RequestProject.OrderNerveRealizationFundamental
import Mathlib.Topology.Homotopy.Lifting

/-! Recover an actual poset cover from a genuine topological cover of an
order realization. Its vertices are actual points above the original
vertices, and incidence is the endpoint of genuine path lifting.
Unverified source. -/

noncomputable section
namespace FiniteChains.Comb.TopologicalOrderCover
open CategoryTheory Topology
variable {P : Type} [PartialOrder P] {E : Type} [TopologicalSpace E]
  (p : C(E, orderNerveRealization P)) (hp : IsCoveringMap p)

def fibreFunctor : P ⥤ Type :=
  orderNerveRealizationFundamentalFunctor P ⋙ hp.monodromyFunctor

abbrev Cover := LocalSystem.Cover (fibreFunctor p hp)
def projection : Cover p hp → P := LocalSystem.projection (fibreFunctor p hp)

theorem projection_monotone : Monotone (projection p hp) :=
  LocalSystem.projection_monotone (fibreFunctor p hp)

def point (v : Cover p hp) : E := v.2.val

theorem point_projection (v : Cover p hp) : p (point p hp v) = orderNerveRealizationVertex v.1 :=
  v.2.property

theorem fibreFunctor_map_bijective {a b : P} (h : a ≤ b) :
    Function.Bijective ((fibreFunctor p hp).map (homOfLE h)) :=
  hp.monodromy_bijective (Path.Homotopic.Quotient.mk (orderNerveRealizationEdgePath h))

theorem projection_isPosetCover (hs : Function.Surjective p) : IsPosetCover (projection p hp) := by
  apply LocalSystem.projection_isPosetCover (fibreFunctor p hp)
  · exact fun h => fibreFunctor_map_bijective p hp h
  · intro a
    obtain ⟨x, hx⟩ := hs (orderNerveRealizationVertex a)
    exact ⟨⟨x, hx⟩⟩

def combinatorialProjection : Hom (orderCx (Cover p hp)) (orderCx P) :=
  orderCxMap (projection p hp) (projection_monotone p hp)

theorem combinatorialProjection_isCovering (hs : Function.Surjective p) :
    IsCovering (combinatorialProjection p hp) :=
  isCovering_orderCxMap (projection_isPosetCover p hp hs)

/-- The defining incidence square retains the actual covering lift. -/
theorem comparable_transport {v w : Cover p hp} (h : v ≤ w) :
    hp.monodromy (Path.Homotopic.Quotient.mk
      (orderNerveRealizationEdgePath h.choose)) v.2 = w.2 := h.choose_spec

end FiniteChains.Comb.TopologicalOrderCover
