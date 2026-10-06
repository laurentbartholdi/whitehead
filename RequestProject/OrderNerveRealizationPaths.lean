import RequestProject.OrderNerveRealizationCW

namespace FiniteChains.Comb
open CategoryTheory Simplicial

/-- The canonical actual realization point of a poset vertex. -/
noncomputable def orderNerveRealizationVertex {P : Type} [PartialOrder P] (p : P) :
    orderNerveRealization P :=
  orderNerveRealizationSimplex P (n := ⦋0⦌) (ComposableArrows.mk₀ p) default

/-- Every vertex of a simplex belongs to its actual canonical image. -/
theorem orderNerveRealizationVertex_mem_simplex {P : Type} [PartialOrder P]
    {n : SimplexCategory} (s : (nerve P).obj (Opposite.op n)) (i : Fin (n.len + 1)) :
    ∃ z : SimplexCategory.toTop.obj n,
      orderNerveRealizationSimplex P s z = orderNerveRealizationVertex (s.obj i) := by
  let a : ⦋0⦌ ⟶ n := SimplexCategory.mkHom (OrderHom.const _ i)
  refine ⟨SimplexCategory.toTop.map a default, ?_⟩
  have h := congrArg (fun k => k default) (orderNerveRealizationSimplex_operator P a s)
  change orderNerveRealizationSimplex P s (SimplexCategory.toTop.map a default) =
    orderNerveRealizationSimplex P ((nerve P).map a.op s) default at h
  have hs : (nerve P).map a.op s = ComposableArrows.mk₀ (s.obj i) := by
    exact CategoryTheory.Functor.ext (fun _ => rfl)
  rw [hs] at h
  exact h

/-- Every actual simplex point is joined by a continuous path to each of its vertices. -/
theorem orderNerveRealizationSimplex_joined_vertex {P : Type} [PartialOrder P]
    {n : SimplexCategory} (s : (nerve P).obj (Opposite.op n))
    (z : SimplexCategory.toTop.obj n) (i : Fin (n.len + 1)) :
    Joined (orderNerveRealizationSimplex P s z) (orderNerveRealizationVertex (s.obj i)) := by
  obtain ⟨w, hw⟩ := orderNerveRealizationVertex_mem_simplex s i
  have h : Joined (orderNerveRealizationSimplex P s z) (orderNerveRealizationSimplex P s w) :=
    ⟨(PathConnectedSpace.joined z w).somePath.map
      (orderNerveRealizationSimplex P s).hom.continuous⟩
  rw [hw] at h
  exact h

/-- Comparable poset vertices are joined in the actual realization. -/
theorem orderNerveRealizationVertex_joined_of_le {P : Type} [PartialOrder P]
    {p q : P} (h : p ≤ q) : Joined (orderNerveRealizationVertex p) (orderNerveRealizationVertex q) := by
  let s := ComposableArrows.mk₁ (homOfLE h)
  let z : SimplexCategory.toTop.obj ⦋1⦌ := Classical.choice inferInstance
  have hp := orderNerveRealizationSimplex_joined_vertex s z (0 : Fin 2)
  have hq := orderNerveRealizationSimplex_joined_vertex s z (1 : Fin 2)
  exact hp.symm.trans hq

/-- Actual realization vertices joined by a combinatorial edge path are topologically joined. -/
theorem orderNerveRealizationVertex_joined_of_isPath {P : Type} [PartialOrder P]
    {a b : P} {p : List (OrdEdge P × Bool)}
    (hp : IsPath (orderCx P).src (orderCx P).tgt p a b) :
    Joined (orderNerveRealizationVertex a) (orderNerveRealizationVertex b) := by
  induction p generalizing a with
  | nil =>
    change a = b at hp
    subst b
    exact Joined.refl _
  | cons e p ih =>
    rcases hp with ⟨rfl, hp⟩
    have he : Joined
        (orderNerveRealizationVertex (P := P) (germSrc (orderCx P).src (orderCx P).tgt e))
        (orderNerveRealizationVertex (P := P) (germTgt (orderCx P).src (orderCx P).tgt e)) := by
      rcases e with ⟨e, o⟩
      cases o
      · exact (orderNerveRealizationVertex_joined_of_le e.property).symm
      · exact orderNerveRealizationVertex_joined_of_le e.property
    exact he.trans (ih hp)

/-- A nonempty combinatorially connected poset has path-connected actual realization. -/
theorem orderNerveRealization_pathConnectedSpace (P : Type) [PartialOrder P] [Nonempty P]
    (hP : IsConnected (orderCx P)) : PathConnectedSpace (orderNerveRealization P) where
  nonempty := ⟨orderNerveRealizationVertex (Classical.choice (inferInstance : Nonempty P))⟩
  joined x y := by
    obtain ⟨n, s, z, hx⟩ := orderNerveRealizationSimplex_jointly_surjective P x
    obtain ⟨m, t, w, hy⟩ := orderNerveRealizationSimplex_jointly_surjective P y
    have hs := orderNerveRealizationSimplex_joined_vertex s z (0 : Fin (n.len + 1))
    have ht := orderNerveRealizationSimplex_joined_vertex t w (0 : Fin (m.len + 1))
    rw [hx] at hs
    rw [hy] at ht
    obtain ⟨p, hp⟩ := hP (s.obj 0) (t.obj 0)
    exact hs.trans ((orderNerveRealizationVertex_joined_of_isPath hp).trans ht.symm)

end FiniteChains.Comb
