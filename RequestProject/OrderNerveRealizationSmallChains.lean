module

public import RequestProject.TopologicalSingular.SmallMathlibComparison
public import RequestProject.OrderNerveRealizationStarAcyclic

@[expose] public section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb
open CategoryTheory AlgebraicTopology TopologicalSingular SingularSubdivision

/-- Integral singular chains subordinate to the actual open vertex stars. -/
noncomputable def orderNerveRealizationSmallComplex (P : Type) [PartialOrder P] :=
  smallComplex (orderNerveRealizationOpenStar P)

/-- The open-star small complex computes actual singular homology in every
degree. Neither finiteness nor local finiteness is required. -/
noncomputable def orderNerveRealizationSmallHomologyIso (P : Type)
    [PartialOrder P] (n : ℕ) :
    (orderNerveRealizationSmallComplex P).homology n ≅
      ((singularHomologyFunctor (ModuleCat.{0} ℤ) n).obj (ModuleCat.of ℤ ℤ)).obj
        (orderNerveRealization P) :=
  smallMathlibHomologyIso (orderNerveRealizationOpenStar P)
    (orderNerveRealizationOpenStar_isOpen P) (orderNerveRealizationOpenStar_cover P) n

/-- Every positive-dimensional singular cycle is homologous to one whose
individual simplices each lie in an open vertex star. -/
theorem orderNerveRealization_exists_small_cycle (P : Type) [PartialOrder P]
    (n : ℕ) (c : Chain (orderNerveRealization P) (n + 1)) (hc : boundary n c = 0) :
    ∃ d : Chain (orderNerveRealization P) (n + 1),
      d ∈ smallChains (orderNerveRealizationOpenStar P) (n + 1) ∧
      boundary n d = 0 ∧ d - c ∈ LinearMap.range (boundary (n + 1)) :=
  exists_small_cycle_representative (orderNerveRealizationOpenStar P)
    (orderNerveRealizationOpenStar_isOpen P) (orderNerveRealizationOpenStar_cover P) n c hc

/-- A star-small boundary admits a star-small filling whenever it admits a
singular filling. This supplies injectivity as well as surjectivity. -/
theorem orderNerveRealization_exists_small_filling (P : Type) [PartialOrder P]
    (n : ℕ) (c : Chain (orderNerveRealization P) (n + 1))
    (hc : c ∈ smallChains (orderNerveRealizationOpenStar P) (n + 1))
    (b : Chain (orderNerveRealization P) (n + 2)) (hb : boundary (n + 1) b = c) :
    ∃ a : Chain (orderNerveRealization P) (n + 2),
      a ∈ smallChains (orderNerveRealizationOpenStar P) (n + 2) ∧ boundary (n + 1) a = c :=
  exists_small_filling (orderNerveRealizationOpenStar P)
    (orderNerveRealizationOpenStar_isOpen P) (orderNerveRealizationOpenStar_cover P) n c hc b hb

end FiniteChains.Comb
