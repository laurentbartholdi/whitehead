import RequestProject.ChamberZPoset

/-!
# Why the attaching map is defined on the simplices and not on all finite sets of vertices

The boundary of a chamber of the Davis complex is the order complex of the poset of **nonempty
simplices** of `L` (the barycentric subdivision of `L`), and this is the poset
`FiniteChains.Davis.NeSpx A` on which the attaching map `att` of the modified chambers is
defined.

It is tempting to let the attaching map be defined on *all* nonempty finite sets of vertices —
the condition `IsSimplex` is never needed to state the order of the model, because only
simplices occur as types of cells.  This file shows that this convenience would make the whole
construction vacuous:

* `FiniteChains.Davis.simplyConnected_orderCx_neFinsets` — the poset of all nonempty finite sets
  of vertices of a finite nonempty vertex set has a largest element, so its order complex is
  simply connected;
* `FiniteChains.Davis.htpy_nil_mapPath_of_attAll` — consequently a monotone map defined on
  **all** nonempty finite sets kills every loop of the boundary of a chamber: the attached loop
  is null-homotopic in the base.

So an attaching map of that kind can only realise attaching words that are already trivial in
the base, and the marking equalities `b [s_h] = j [u_h]` of a block could only be satisfied for
`u_h = 1`.  The domain of `att` must therefore be the poset of nonempty simplices, as it is.
-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains
namespace Davis

open RACG Mirror Comb

universe u

variable {V : Type u} [DecidableEq V] [Fintype V] [Nonempty V] {A : CommRel V}
  {X : Type u} [Preorder X]

/-- All nonempty finite sets of vertices, ordered by inclusion. -/
abbrev NeFinsets (V : Type u) : Type u := {σ : Finset V // σ.Nonempty}

omit [DecidableEq V] in
/-- **The poset of all nonempty finite sets of vertices is a cone**: its order complex is simply
connected, because the set of all vertices is a largest element. -/
theorem simplyConnected_orderCx_neFinsets :
    SimplyConnected (orderCx (NeFinsets V)) :=
  Comb.simplyConnected_orderCx
    (⟨Finset.univ, Finset.univ_nonempty⟩ : NeFinsets V) id (fun _ => le_refl _)
    (fun x => show x.1 ⊆ Finset.univ from Finset.subset_univ _) (fun h => h)

/-- The inclusion of the nonempty simplices in all nonempty finite sets of vertices. -/
def neSpxIncl (A : CommRel V) : NeSpx A →o NeFinsets V :=
  ⟨fun σ => ⟨σ.1, σ.2.1⟩, fun _ _ h => h⟩

omit [DecidableEq V] in
/-- **A monotone map defined on all nonempty finite sets of vertices attaches every loop of the
boundary of a chamber trivially.**  This is the reason the domain of the attaching map is the
poset of nonempty simplices: on the larger poset every attaching word would be null-homotopic
in the base. -/
theorem htpy_nil_mapPath_of_attAll (attAll : NeFinsets V →o X) {v : NeSpx A}
    {l : List ((orderCx (NeSpx A)).E × Bool)}
    (hp : IsPath (orderCx (NeSpx A)).src (orderCx (NeSpx A)).tgt l v v) :
    Htpy (orderCx X) (attAll (neSpxIncl A v)) (attAll (neSpxIncl A v))
      (mapPath (orderCxMap (fun σ : NeSpx A => attAll (neSpxIncl A σ))
        (attAll.monotone.comp (neSpxIncl A).monotone)) l) [] := by
  classical
  -- the loop already dies in the poset of all nonempty finite sets of vertices
  have hincl : Htpy (orderCx (NeFinsets V)) (neSpxIncl A v) (neSpxIncl A v)
      (mapPath (orderCxMap (neSpxIncl A) (neSpxIncl A).monotone) l) [] :=
    simplyConnected_orderCx_neFinsets _ _
      (isPath_mapPath (orderCxMap (neSpxIncl A) (neSpxIncl A).monotone) hp)
  have himg := mapPath_htpy (orderCxMap attAll attAll.monotone) hincl
  simp only [mapPath, List.map_map, List.map_nil] at himg
  convert himg using 1 <;> rfl

end Davis
end FiniteChains
