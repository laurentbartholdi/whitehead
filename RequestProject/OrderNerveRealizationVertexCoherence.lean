module

public import RequestProject.OrderNerveRealizationFundamental
public import RequestProject.OrderFunctorTrivialization

@[expose] public section

namespace FiniteChains.Comb
open CategoryTheory Simplicial

/-- A combinatorially connected simply connected poset admits topological path
classes to its vertices which commute with every realized comparable edge. -/
theorem orderNerveRealization_exists_vertex_coherence (P : Type) [PartialOrder P]
    (a : P) (hconn : IsConnected (orderCx P)) (hsc : SimplyConnected (orderCx P)) :
    ∃ k : ∀ p : P, FundamentalGroupoid.mk (orderNerveRealizationVertex a) ⟶
        FundamentalGroupoid.mk (orderNerveRealizationVertex p),
      ∀ {p q : P} (h : p ≤ q),
        k p ≫ Path.Homotopic.Quotient.mk (orderNerveRealizationEdgePath h) = k q := by
  letI : Nonempty P := ⟨a⟩
  letI := orderNerveRealization_pathConnectedSpace P hconn
  let F := orderNerveRealizationFundamentalFunctor P
  let d : ∀ p : P, F.obj a ⟶ F.obj p := fun p =>
    Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath
      (orderNerveRealizationVertex a) (orderNerveRealizationVertex p))
  obtain ⟨k, hk⟩ := orderFunctor_exists_coherent_arrows F a d hconn hsc
  exact ⟨k, fun {p q} h => hk (homOfLE h)⟩

/-- Each point has a radial path from a supporting vertex. The radial path
stays inside every closed star whose corresponding open star contains the point. -/
theorem orderNerveRealization_exists_radial {P : Type} [PartialOrder P]
    (x : orderNerveRealization P) :
    ∃ (p : P) (r : Path (orderNerveRealizationVertex p) x),
      ∀ v : P, x ∈ orderNerveRealizationOpenStar P v →
        (p ≤ v ∨ v ≤ p) ∧
        Set.range r ⊆ (orderNerveRealizationSubcomplex P (orderNerveVertexStar P v) :
          Set (orderNerveRealization P)) := by
  obtain ⟨n, s, z, hz, hx⟩ := orderNerveRealization_interior_cover P x
  obtain ⟨w, hw⟩ := orderNerveRealizationVertex_mem_simplex s.val 0
  let r₀ := (PathConnectedSpace.joined w z).somePath.map
    (orderNerveRealizationSimplex P s.val).hom.continuous
  let r : Path (orderNerveRealizationVertex (s.val.obj 0)) x := r₀.cast hw.symm hx.symm
  refine ⟨s.val.obj 0, r, ?_⟩
  intro v hv
  rw [← hx] at hv
  obtain ⟨j, hj⟩ := (orderNerveRealizationSimplex_mem_openStar_iff s.val z hz v).mp hv
  have hall : ∀ i, s.val.obj i ≤ v ∨ v ≤ s.val.obj i := by
    intro i
    rcases le_total i j with h | h
    · exact Or.inl (hj ▸ leOfHom (s.val.map (homOfLE h)))
    · exact Or.inr (hj ▸ leOfHom (s.val.map (homOfLE h)))
  refine ⟨hall 0, ?_⟩
  have hr : Set.range r ⊆ Set.range (orderNerveRealizationSimplex P s.val) := by
    rintro y ⟨t, rfl⟩
    exact ⟨(PathConnectedSpace.joined w z).somePath t, rfl⟩
  exact hr.trans (orderNerveRealizationSimplex_supported (orderNerveVertexStar P v) s.val hall)

end FiniteChains.Comb
