module

public import RequestProject.TopologicalOrderCoverComparison
public import RequestProject.CoveringFibreComparison
public import RequestProject.OrderNerveRealizationRegular

@[expose] public section

/-! The reconstructed poset covering has exactly the original covering
space as its actual geometric realization. No connectedness assumption
is needed for this identification. Unverified source. -/

noncomputable section
namespace FiniteChains.Comb.TopologicalOrderCover
open CategoryTheory Simplicial Topology
open scoped Classical
variable {P : Type} [PartialOrder P] {E : Type} [TopologicalSpace E]
  (p : C(E, orderNerveRealization P)) (hp : IsCoveringMap p) (hs : Function.Surjective p)

include hs in
theorem realizedProjection_isCoveringMap : IsCoveringMap (realizedProjection p hp) :=
  (projection_isPosetCover p hp hs).realizationMap_isCoveringMap

include hs in
theorem realizedProjection_vertex_fibre (q : P)
    (x : orderNerveRealization (Cover p hp))
    (hx : realizedProjection p hp x = orderNerveRealizationVertex q) :
    ∃ v : Cover p hp, v.1 = q ∧ x = orderNerveRealizationVertex v := by
  let hf := projection_isPosetCover p hp hs
  obtain ⟨v, hxv⟩ := orderNerveRealizationOpenStar_cover (Cover p hp) x
  have himg : realizedProjection p hp x ∈ orderNerveRealizationOpenStar P v.1 :=
    (orderNerveRealizationMap_mem_openStar_iff (projection p hp)
      (projection_monotone p hp) x v.1).mpr ⟨v, rfl, hxv⟩
  have hvq : v.1 = q := by
    rw [hx] at himg
    by_contra h
    have h' : q ≠ v.1 := Ne.symm h
    simp only [orderNerveRealizationOpenStar, Set.mem_setOf_eq,
      orderNerveRealizationCoordinates_vertex, if_neg h'] at himg
    exact lt_irrefl _ himg
  refine ⟨v, hvq, hf.realizationMap_injOn_openStar v hxv ?_ ?_⟩
  · simp [orderNerveRealizationOpenStar, orderNerveRealizationCoordinates_vertex]
  · change realizedProjection p hp x = orderNerveRealizationMap _ _ _
    rw [orderNerveRealizationMap_vertex, hx]
    exact (congrArg (orderNerveRealizationVertex (P := P)) hvq).symm

include hs in
theorem comparison_vertex_fibre_bijective (q : P) :
    Function.Bijective
      (CoveringComparison.fibreMap (realizedProjection p hp) p
        (realizationComparison p hp) (realizationComparison_projection p hp)
        (orderNerveRealizationVertex q)) := by
  constructor
  · intro x y hxy
    obtain ⟨v, hv, hx⟩ := realizedProjection_vertex_fibre p hp hs q x.val x.property
    obtain ⟨w, hw, hy⟩ := realizedProjection_vertex_fibre p hp hs q y.val y.property
    have hpoint : point p hp v = point p hp w := by
      have h := congrArg Subtype.val hxy
      change realizationComparison p hp x.val = realizationComparison p hp y.val at h
      simpa only [hx, hy, realizationComparison_vertex] using h
    have hvw : v = w := by
      cases v with
      | mk a e =>
        cases w with
        | mk b e' =>
          dsimp at hv hw
          have hab : a = b := hv.trans hw.symm
          clear hv hw
          subst b
          refine Sigma.ext rfl ?_
          exact heq_of_eq (Subtype.ext hpoint)
    apply Subtype.ext
    rw [hx, hy, hvw]
  · intro e
    let v : Cover p hp := ⟨q, e⟩
    refine ⟨⟨orderNerveRealizationVertex v, ?_⟩, ?_⟩
    · exact orderNerveRealizationMap_vertex _ _ v
    · apply Subtype.ext
      exact realizationComparison_vertex p hp v

include hs in
theorem comparison_fibre_bijective (x : orderNerveRealization P) :
    Function.Bijective
      (CoveringComparison.fibreMap (realizedProjection p hp) p
        (realizationComparison p hp) (realizationComparison_projection p hp) x) := by
  obtain ⟨n, s, z, hz⟩ := orderNerveRealizationSimplex_jointly_surjective P x
  have hj := orderNerveRealizationSimplex_joined_vertex s z (0 : Fin (n.len + 1))
  rw [hz] at hj
  exact CoveringComparison.fibreMap_bijective_of_joined (realizedProjection p hp) p
    (realizedProjection_isCoveringMap p hp hs) hp (realizationComparison p hp)
    (realizationComparison_projection p hp) hj
    (comparison_vertex_fibre_bijective p hp hs (s.obj 0))

def realizationHomeomorph : orderNerveRealization (Cover p hp) ≃ₜ E :=
  CoveringComparison.homeomorphOfFibrewise (realizedProjection p hp) p
    (realizedProjection_isCoveringMap p hp hs) hp (realizationComparison p hp)
    (realizationComparison_projection p hp) (comparison_fibre_bijective p hp hs)

theorem realizationHomeomorph_apply (x : orderNerveRealization (Cover p hp)) :
    realizationHomeomorph p hp hs x = realizationComparison p hp x := rfl

theorem realizationHomeomorph_projection (x : orderNerveRealization (Cover p hp)) :
    p (realizationHomeomorph p hp hs x) = realizedProjection p hp x :=
  realizationComparison_projection p hp x

theorem realizationHomeomorph_vertex (v : Cover p hp) :
    realizationHomeomorph p hp hs (orderNerveRealizationVertex v) = point p hp v :=
  realizationComparison_vertex p hp v

end FiniteChains.Comb.TopologicalOrderCover
