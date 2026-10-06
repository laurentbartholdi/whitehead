import Mathlib.Topology.Path
import Mathlib.Topology.Homotopy.Basic
import Mathlib.Tactic

/-! A square filling obtained by sliding along a single concatenated path.
It extends an arbitrary contraction path at the initial end of an edge. -/

noncomputable section
namespace Path
open scoped unitInterval Topology

variable {X : Type*} [TopologicalSpace X] {a b z : X}

/-- Time runs vertically. At time zero the square is `p`; at time one it
is constant at `z`. Its left side is `q`, and its right side is `p.symm.trans q`. -/
def tailContraction (p : Path a b) (q : Path a z) : C(I × I, X) where
  toFun ts := (p.symm.trans q).extend
    ((1 - (ts.2 : ℝ) + (1 + (ts.2 : ℝ)) * (ts.1 : ℝ)) / 2)
  continuous_toFun := (p.symm.trans q).continuous_extend.comp (by fun_prop)

@[simp] theorem tailContraction_zero (p : Path a b) (q : Path a z) (s : I) :
    tailContraction p q (0, s) = p s := by
  change (p.symm.trans q).extend ((1 - (s : ℝ) + (1 + (s : ℝ)) * 0) / 2) = p s
  rw [Path.extend_trans_of_le_half _ _ (by linarith [s.property.1]),
    Path.extend_symm_apply]
  have hs : 1 - 2 * ((1 - (s : ℝ) + (1 + (s : ℝ)) * 0) / 2) = s := by ring
  rw [hs, Path.extend_apply _ s.property]

@[simp] theorem tailContraction_one (p : Path a b) (q : Path a z) (s : I) :
    tailContraction p q (1, s) = z := by
  change (p.symm.trans q).extend ((1 - (s : ℝ) + (1 + (s : ℝ)) * 1) / 2) = z
  have hs : (1 - (s : ℝ) + (1 + (s : ℝ)) * 1) / 2 = 1 := by ring
  rw [hs, Path.extend_one]

@[simp] theorem tailContraction_left (p : Path a b) (q : Path a z) (t : I) :
    tailContraction p q (t, 0) = q t := by
  change (p.symm.trans q).extend ((1 - 0 + (1 + 0) * (t : ℝ)) / 2) = q t
  rw [Path.extend_trans_of_half_le _ _ (by linarith [t.property.1])]
  have ht : 2 * ((1 - 0 + (1 + 0) * (t : ℝ)) / 2) - 1 = t := by ring
  rw [ht, Path.extend_apply _ t.property]

@[simp] theorem tailContraction_right (p : Path a b) (q : Path a z) (t : I) :
    tailContraction p q (t, 1) = (p.symm.trans q) t := by
  change (p.symm.trans q).extend ((1 - 1 + (1 + 1) * (t : ℝ)) / 2) = _
  have ht : (1 - 1 + (1 + 1) * (t : ℝ)) / 2 = t := by ring
  rw [ht, Path.extend_apply _ t.property]

end Path
