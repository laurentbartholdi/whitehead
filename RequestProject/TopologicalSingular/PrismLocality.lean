import RequestProject.TopologicalSingular.SingularPrism

namespace FiniteChains.SingularPrism
open TopologicalSingular
open scoped unitInterval
universe u v w
variable {A : Type u} {B : Type v} {X : Type w}
  [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace X]
  {f g : C(A, X)} {f' g' : C(B, X)}

/-- A prism depends only on the homotopy restricted to its input simplex. -/
theorem prism_single_congr (H : f.Homotopy g) (K : f'.Homotopy g')
    {n : ℕ} (tau : Simplex A n) (eta : Simplex B n)
    (h : ∀ (t : I) (z : Domain n), H (t, tau z) = K (t, eta z)) (r : ℤ) :
    prism H n (Finsupp.single tau r) = prism K n (Finsupp.single eta r) := by
  have he (i : Fin (n + 1)) : simplex H tau i = simplex K eta i := by
    apply ContinuousMap.ext
    intro z
    exact h (prismMap i z).1 (prismMap i z).2
  rw [prism_single, prism_single]
  simp only [he]

end FiniteChains.SingularPrism
