module

public import RequestProject.TopologicalSingular.SingularChains

@[expose] public section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.TopologicalSingular
open scoped unitInterval Topology
universe u
variable {Y : Type u} [TopologicalSpace Y] {n : ℕ}

/-- Coordinatewise straight-line interpolation stays in the standard simplex. -/
noncomputable def simplexLinearHomotopy (f g : C(Y, Domain n)) : f.Homotopy g where
  toFun w := ⟨fun i => (1 - (w.1 : ℝ)) * (f w.2).val i + (w.1 : ℝ) * (g w.2).val i, by
    constructor
    · intro i
      exact add_nonneg (mul_nonneg (sub_nonneg.mpr w.1.property.2) ((f w.2).property.1 i))
        (mul_nonneg w.1.property.1 ((g w.2).property.1 i))
    · rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
        (f w.2).property.2, (g w.2).property.2]
      ring⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    exact ((continuous_const.sub continuous_fst.subtype_val).mul
      ((continuous_apply i).comp (f.continuous.comp continuous_snd).subtype_val)).add
      (continuous_fst.subtype_val.mul
        ((continuous_apply i).comp (g.continuous.comp continuous_snd).subtype_val))
  map_zero_left z := by
    apply Subtype.ext
    funext i
    simp
  map_one_left z := by
    apply Subtype.ext
    funext i
    simp

theorem simplexLinearHomotopy_fixed (f g : C(Y, Domain n)) (z : Y)
    (h : f z = g z) (t : I) : simplexLinearHomotopy f g (t, z) = f z := by
  apply Subtype.ext
  funext i
  change (1 - (t : ℝ)) * (f z).val i + (t : ℝ) * (g z).val i = (f z).val i
  rw [h]
  ring

noncomputable def simplexLinearHomotopyRel (f g : C(Y, Domain n)) (S : Set Y)
    (h : ∀ z ∈ S, f z = g z) : ContinuousMap.HomotopyRel f g S where
  toHomotopy := simplexLinearHomotopy f g
  prop' t z hz := simplexLinearHomotopy_fixed f g z (h z hz) t

end FiniteChains.TopologicalSingular
