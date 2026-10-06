module

public import RequestProject.OrderNerveRealizationVertexCoherence
public import RequestProject.TopologyPaths.OpenCoverPaths

@[expose] public section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb
open CategoryTheory

/-- Combinatorial connectivity and simple connectivity imply genuine topological
simple connectivity of the poset-nerve realization. No finiteness is required. -/
theorem orderNerveRealization_simplyConnected (P : Type) [PartialOrder P] [Nonempty P]
    (hconn : IsConnected (orderCx P)) (hsc : SimplyConnected (orderCx P)) :
    SimplyConnectedSpace (orderNerveRealization P) := by
  classical
  let a : P := Classical.choice inferInstance
  letI := orderNerveRealization_pathConnectedSpace P hconn
  obtain ⟨k, hk⟩ := orderNerveRealization_exists_vertex_coherence P a hconn hsc
  choose v r hr using (fun x : orderNerveRealization P => orderNerveRealization_exists_radial x)
  let R : ∀ x : orderNerveRealization P,
      FundamentalGroupoid.mk (orderNerveRealizationVertex a) ⟶ FundamentalGroupoid.mk x :=
    fun x => k (v x) ≫ Path.Homotopic.Quotient.mk (r x)
  have hstar (x : orderNerveRealization P) (b : P)
      (hx : x ∈ orderNerveRealizationOpenStar P b) :
      ∃ p : Path (orderNerveRealizationVertex b) x,
        Set.range p ⊆ (orderNerveRealizationSubcomplex P (orderNerveVertexStar P b) :
          Set (orderNerveRealization P)) ∧
        k b ≫ Path.Homotopic.Quotient.mk p = R x := by
    obtain ⟨hcomp, hrad⟩ := hr x b hx
    have he : ∃ e : Path (orderNerveRealizationVertex b) (orderNerveRealizationVertex (v x)),
        Set.range e ⊆ (orderNerveRealizationSubcomplex P (orderNerveVertexStar P b) :
          Set (orderNerveRealization P)) ∧
        k b ≫ Path.Homotopic.Quotient.mk e = k (v x) := by
      rcases hcomp with h | h
      · refine ⟨(orderNerveRealizationEdgePath h).symm, ?_, ?_⟩
        · rw (config := { transparency := .default }) [Path.symm_range]
          exact orderNerveRealizationEdgePath_supported h b (Or.inl h) (Or.inl le_rfl)
        · change k b ≫ Groupoid.inv (Path.Homotopic.Quotient.mk
            (orderNerveRealizationEdgePath h)) = k (v x)
          rw (config := { transparency := .default }) [← hk h, Category.assoc, Groupoid.comp_inv, Category.comp_id]
      · exact ⟨orderNerveRealizationEdgePath h,
          orderNerveRealizationEdgePath_supported h b (Or.inl le_rfl) (Or.inr h), hk h⟩
    obtain ⟨e, he, hke⟩ := he
    refine ⟨e.trans (r x), ?_, ?_⟩
    · rw (config := { transparency := .default }) [Path.trans_range]
      exact Set.union_subset he hrad
    · change k b ≫ (Path.Homotopic.Quotient.mk e ≫ Path.Homotopic.Quotient.mk (r x)) = _
      rw (config := { transparency := .default }) [← Category.assoc, hke]
  have hlocal {x y : orderNerveRealization P} (p : Path x y)
      (hp : ∃ b, Set.range p ⊆ orderNerveRealizationOpenStar P b) :
      R x ≫ Path.Homotopic.Quotient.mk p = R y := by
    obtain ⟨b, hp⟩ := hp
    obtain ⟨e, he, hke⟩ := hstar x b (hp p.source_mem_range)
    obtain ⟨f, hf, hkf⟩ := hstar y b (hp p.target_mem_range)
    letI := orderNerveRealization_closedStar_contractible b
    have hC : IsSimplyConnected (orderNerveRealizationSubcomplex P
        (orderNerveVertexStar P b) : Set (orderNerveRealization P)) := by
      change SimplyConnectedSpace _
      infer_instance
    have hh : (e.trans p).Homotopic f := paths_homotopic_of_range_subset hC _ _ (by
      rw (config := { transparency := .default }) [Path.trans_range]
      exact Set.union_subset he (hp.trans (orderNerveRealizationOpenStar_subset_subcomplex b))) hf
    rw (config := { transparency := .default }) [← hke, ← hkf, Category.assoc]
    apply congrArg (fun q => k b ≫ q)
    exact Quotient.sound hh
  have hall {x y : orderNerveRealization P} (p : Path x y) :
      R x ≫ Path.Homotopic.Quotient.mk p = R y := by
    refine FiniteChains.OpenCoverPaths.path_induction
      (orderNerveRealizationOpenStar P) (orderNerveRealizationOpenStar_isOpen P)
      (orderNerveRealizationOpenStar_cover P)
      (fun {x y} q => R x ≫ Path.Homotopic.Quotient.mk q = R y) ?_ ?_ ?_ ?_ p
    · intro x
      exact Category.comp_id (R x)
    · intro x y z p q hp hq
      change R x ≫ (Path.Homotopic.Quotient.mk p ≫ Path.Homotopic.Quotient.mk q) = R z
      rw (config := { transparency := .default }) [← Category.assoc, hp, hq]
    · intro x y p q hpq hp
      have he : Path.Homotopic.Quotient.mk p = Path.Homotopic.Quotient.mk q := Quotient.sound hpq
      rwa [← he]
    · exact hlocal
  apply simply_connected_iff_loops_nullhomotopic.mpr
  refine ⟨inferInstance, fun x p => ?_⟩
  have he : (Path.Homotopic.Quotient.mk p : End (FundamentalGroupoid.mk x)) =
      𝟙 (FundamentalGroupoid.mk x) := by
    apply (cancel_epi (R x)).mp
    simpa only [Category.comp_id] using hall p
  exact Quotient.exact he

end FiniteChains.Comb
