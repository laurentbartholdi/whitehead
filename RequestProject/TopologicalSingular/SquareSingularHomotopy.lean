module

public import RequestProject.TopologicalSingular.SquareSingularChains
public import RequestProject.TopologicalSingular.RelativeSingularPrism
public import RequestProject.TopologicalCoverPi2

@[expose] public section

namespace FiniteChains.SingularPrism
open TopologicalSingular
open scoped unitInterval
universe u v
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
variable {f g : C(X, Y)} (H : ContinuousMap.Homotopy f g)

theorem prism_one_single_eq_zero_of_constant (tau : Simplex X 1) (r : ℤ) (y : Y)
    (h : ∀ t : I, ∀ z, H (t, tau z) = y) : prism H 1 (Finsupp.single tau r) = 0 := by
  have hs (i : Fin 2) : simplex H tau i = ContinuousMap.const (Domain 2) y := by
    apply ContinuousMap.ext
    intro z
    exact h _ _
  rw [prism_single, altSum, Fin.sum_univ_two]
  simp only [hs, Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul, neg_smul]
  exact add_neg_cancel _

theorem prism_one_eq_zero_of_constant_on (A : Set X) (y : Y)
    (hH : ∀ t : I, ∀ a ∈ A, H (t, a) = y) {c : Chain X 1} (hc : c ∈ subChains A 1) :
    prism H 1 c = 0 := by
  obtain ⟨b, rfl⟩ := hc
  induction b using Finsupp.induction_linear with
  | zero => simp
  | add b c hb hc => simp only [map_add, hb, hc, add_zero]
  | single tau r =>
    rw [TopologicalSingular.map_single]
    exact prism_one_single_eq_zero_of_constant H _ r y (fun t z => hH t _ (tau z).property)

end FiniteChains.SingularPrism

namespace FiniteChains.TopologicalSingular
open scoped unitInterval Topology
universe u
variable {X : Type u} [TopologicalSpace X] {x : X}

/-- An actual homotopy relative to the square boundary gives an explicit
singular three-chain between the associated two-cycles. -/
theorem squareCycle_homotopic_difference_bounds {p q : GenLoop (Fin 2) X x}
    (h : GenLoop.Homotopic p q) :
    squareCycle q - squareCycle p ∈ LinearMap.range (boundary 2) := by
  obtain ⟨H⟩ := h
  refine ⟨SingularPrism.prism H.toHomotopy 2 squareFundamentalChain, ?_⟩
  have he := SingularPrism.prism_identity_succ H.toHomotopy 1 squareFundamentalChain
  have hz := SingularPrism.prism_one_eq_zero_of_constant_on H.toHomotopy
    (Cube.boundary (Fin 2)) x
    (fun t a ha => (H.eq_fst t ha).trans (GenLoop.boundary p a ha))
    squareFundamentalChain_boundary_supported
  rw [hz, add_zero] at he
  exact he

theorem squareCycle_map {Y : Type} [TopologicalSpace Y] {X : Type} [TopologicalSpace X]
    (f : C(X, Y)) {x : X} (p : GenLoop (Fin 2) X x) :
    squareCycle (Whitehead.mapSquare f p) = map f 2 (squareCycle p) := by
  change map (f.comp p.val) 2 squareFundamentalChain = _
  rw [map_comp, LinearMap.comp_apply]
  rfl

end FiniteChains.TopologicalSingular
