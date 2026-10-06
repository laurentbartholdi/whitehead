import RequestProject.CubeMedianGraph
import RequestProject.CubeRollerModel
import RequestProject.CubeCartanHadamardExample

/-!
# A model of the median-graph axioms

The hypotheses of `FiniteChains.MedianGraph` are not vacuous: the cubulated positive octant
of three-space is a median graph of dimension three.  Its vertices are the triples of natural
numbers, the distance is the `ℓ¹`-distance (the graph distance of the cubulation) and the
median is taken coordinatewise.  The complex is infinite and has three-dimensional cells, so
`FiniteChains.MedianGraph.ker_d₂_eq_range_d₃` applies to it and has content.
-/

namespace FiniteChains

namespace MedianGraphExample

open OctantModel

/-- The distance of two natural numbers. -/
def d1 (x y : ℕ) : ℕ := (x - y) + (y - x)

/-- The median of three natural numbers. -/
def med3 (a b c : ℕ) : ℕ := max (min a b) (min (max a b) c)

theorem d1_self (x : ℕ) : d1 x x = 0 := by simp [d1]

theorem d1_comm (x y : ℕ) : d1 x y = d1 y x := by simp only [d1]; omega

theorem d1_eq_zero {x y : ℕ} (h : d1 x y = 0) : x = y := by simp only [d1] at h; omega

theorem d1_triangle (x y z : ℕ) : d1 x z ≤ d1 x y + d1 y z := by simp only [d1]; omega

theorem d1_med_ab (a b c : ℕ) : d1 a (med3 a b c) + d1 (med3 a b c) b = d1 a b := by
  simp only [d1, med3]; omega

theorem d1_med_bc (a b c : ℕ) : d1 b (med3 a b c) + d1 (med3 a b c) c = d1 b c := by
  simp only [d1, med3]; omega

theorem d1_med_ac (a b c : ℕ) : d1 a (med3 a b c) + d1 (med3 a b c) c = d1 a c := by
  simp only [d1, med3]; omega

theorem d1_med_unique {a b c z : ℕ} (h1 : d1 a z + d1 z b = d1 a b)
    (h2 : d1 b z + d1 z c = d1 b c) (h3 : d1 a z + d1 z c = d1 a c) : z = med3 a b c := by
  simp only [d1, med3] at *; omega

theorem d1_zero (x : ℕ) : d1 0 x = x := by simp [d1]

/-- A vertex of the octant one step below `w` differs from it in exactly one coordinate. -/
theorem octant_step {a1 a2 a3 w1 w2 w3 : ℕ}
    (h1 : d1 a1 w1 + d1 a2 w2 + d1 a3 w3 = 1)
    (h2 : a1 + a2 + a3 + 1 = w1 + w2 + w3) :
    (a1 + 1 = w1 ∧ a2 = w2 ∧ a3 = w3) ∨ (a1 = w1 ∧ a2 + 1 = w2 ∧ a3 = w3) ∨
      (a1 = w1 ∧ a2 = w2 ∧ a3 + 1 = w3) := by
  simp only [d1] at h1
  omega

/-- The `ℓ¹`-distance on triples of natural numbers: the graph distance of the cubulated
octant. -/
def dst (x y : V3) : ℕ :=
  d1 (co x).1 (co y).1 + d1 (co x).2.1 (co y).2.1 + d1 (co x).2.2 (co y).2.2

/-- The coordinatewise median of three vertices. -/
def mdd (x y z : V3) : V3 :=
  mk3 (med3 (co x).1 (co y).1 (co z).1) (med3 (co x).2.1 (co y).2.1 (co z).2.1)
    (med3 (co x).2.2 (co y).2.2 (co z).2.2)

@[simp] theorem co_mdd (x y z : V3) :
    co (mdd x y z) = (med3 (co x).1 (co y).1 (co z).1, med3 (co x).2.1 (co y).2.1 (co z).2.1,
      med3 (co x).2.2 (co y).2.2 (co z).2.2) := rfl

/-- The cubulated positive octant of three-space as a median graph. -/
def octantMedian : MedianGraph V3 where
  dist := dst
  base := mk3 0 0 0
  dist_self := by
    intro x
    simp [dst, d1_self]
  eq_of_dist_eq_zero := by
    intro x y h
    simp only [dst] at h
    exact eq_of_co (Prod.ext (d1_eq_zero (by omega))
      (Prod.ext (d1_eq_zero (by omega)) (d1_eq_zero (by omega))))
  dist_comm := by
    intro x y
    simp only [dst]
    have c1 := d1_comm (co x).1 (co y).1
    have c2 := d1_comm (co x).2.1 (co y).2.1
    have c3 := d1_comm (co x).2.2 (co y).2.2
    omega
  dist_triangle := by
    intro x y z
    simp only [dst]
    have t1 := d1_triangle (co x).1 (co y).1 (co z).1
    have t2 := d1_triangle (co x).2.1 (co y).2.1 (co z).2.1
    have t3 := d1_triangle (co x).2.2 (co y).2.2 (co z).2.2
    omega
  med := mdd
  med_ab := by
    intro a b c
    simp only [dst, co_mdd]
    have m1 := d1_med_ab (co a).1 (co b).1 (co c).1
    have m2 := d1_med_ab (co a).2.1 (co b).2.1 (co c).2.1
    have m3 := d1_med_ab (co a).2.2 (co b).2.2 (co c).2.2
    omega
  med_bc := by
    intro a b c
    simp only [dst, co_mdd]
    have m1 := d1_med_bc (co a).1 (co b).1 (co c).1
    have m2 := d1_med_bc (co a).2.1 (co b).2.1 (co c).2.1
    have m3 := d1_med_bc (co a).2.2 (co b).2.2 (co c).2.2
    omega
  med_ac := by
    intro a b c
    simp only [dst, co_mdd]
    have m1 := d1_med_ac (co a).1 (co b).1 (co c).1
    have m2 := d1_med_ac (co a).2.1 (co b).2.1 (co c).2.1
    have m3 := d1_med_ac (co a).2.2 (co b).2.2 (co c).2.2
    omega
  med_unique := by
    intro a b c z h1 h2 h3
    simp only [dst] at h1 h2 h3
    have p1 := d1_triangle (co a).1 (co z).1 (co b).1
    have p2 := d1_triangle (co a).2.1 (co z).2.1 (co b).2.1
    have p3 := d1_triangle (co a).2.2 (co z).2.2 (co b).2.2
    have q1 := d1_triangle (co b).1 (co z).1 (co c).1
    have q2 := d1_triangle (co b).2.1 (co z).2.1 (co c).2.1
    have q3 := d1_triangle (co b).2.2 (co z).2.2 (co c).2.2
    have r1 := d1_triangle (co a).1 (co z).1 (co c).1
    have r2 := d1_triangle (co a).2.1 (co z).2.1 (co c).2.1
    have r3 := d1_triangle (co a).2.2 (co z).2.2 (co c).2.2
    exact eq_of_co
      (Prod.ext (d1_med_unique (by omega) (by omega) (by omega))
        (Prod.ext (d1_med_unique (by omega) (by omega) (by omega))
          (d1_med_unique (by omega) (by omega) (by omega))))
  dim_le := by
    intro w s hs
    classical
    have hsub : s ⊆ ({mk3 ((co w).1 - 1) (co w).2.1 (co w).2.2,
        mk3 (co w).1 ((co w).2.1 - 1) (co w).2.2,
        mk3 (co w).1 (co w).2.1 ((co w).2.2 - 1)} : Finset V3) := by
      intro a ha
      obtain ⟨h1, h2⟩ := hs a ha
      have h1' : d1 (co a).1 (co w).1 + d1 (co a).2.1 (co w).2.1
          + d1 (co a).2.2 (co w).2.2 = 1 := h1
      have h2' : (co a).1 + (co a).2.1 + (co a).2.2 + 1
          = (co w).1 + (co w).2.1 + (co w).2.2 := by
        have h2'' : dst (mk3 0 0 0) a + 1 = dst (mk3 0 0 0) w := h2
        simpa [dst, d1_zero, co_mk3] using h2''
      clear h1 h2
      simp only [Finset.mem_insert, Finset.mem_singleton]
      rcases octant_step h1' h2' with hcase | hcase | hcase
      · left
        refine eq_of_co (Prod.ext ?_ (Prod.ext ?_ ?_)) <;> simp only [co_mk3] <;> omega
      · right; left
        refine eq_of_co (Prod.ext ?_ (Prod.ext ?_ ?_)) <;> simp only [co_mk3] <;> omega
      · right; right
        refine eq_of_co (Prod.ext ?_ (Prod.ext ?_ ?_)) <;> simp only [co_mk3] <;> omega
    refine le_trans (Finset.card_le_card hsub) ?_
    refine le_trans (Finset.card_insert_le _ _) ?_
    have h2 : ({mk3 (co w).1 ((co w).2.1 - 1) (co w).2.2,
        mk3 (co w).1 (co w).2.1 ((co w).2.2 - 1)} : Finset V3).card ≤ 2 := by
      refine le_trans (Finset.card_insert_le _ _) ?_
      simp
    omega

/-- The descending neighbours in the octant: lower one coordinate by one. -/
theorem mem_dnM_of_octant {a b c a' b' c' : ℕ} (h1 : a' + b' + c' + 1 = a + b + c)
    (h2 : a' ≤ a) (h3 : b' ≤ b) (h4 : c' ≤ c) :
    mk3 a' b' c' ∈ octantMedian.dnM (mk3 a b c) := by
  constructor
  · show dst (mk3 a' b' c') (mk3 a b c) = 1
    simp only [dst, d1, co_mk3]
    omega
  · show dst (mk3 0 0 0) (mk3 a' b' c') + 1 = dst (mk3 0 0 0) (mk3 a b c)
    simp only [dst, d1, co_mk3]
    omega

theorem mk3_ne {a b c a' b' c' : ℕ} (h : (a, b, c) ≠ (a', b', c')) :
    mk3 a b c ≠ mk3 a' b' c' := by
  intro hc
  exact h (by simpa using congrArg co hc)

/-- The median graph model of the octant really has three-dimensional cells. -/
theorem octantMedian_nonempty_CbC : Nonempty (octantMedian.toDescCubeStr).CbC :=
  DescCubeStr.nonempty_CbC (S := octantMedian.toDescCubeStr)
    (mem_dnM_of_octant (a := 1) (b := 1) (c := 1) (a' := 0) (b' := 1) (c' := 1) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num))
    (mem_dnM_of_octant (a := 1) (b := 1) (c := 1) (a' := 1) (b' := 0) (c' := 1) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num))
    (mem_dnM_of_octant (a := 1) (b := 1) (c := 1) (a' := 1) (b' := 1) (c' := 0) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num))
    (mk3_ne (by decide)) (mk3_ne (by decide)) (mk3_ne (by decide))

/-- Consequently the vanishing of the second homology applies to a nontrivial infinite
complex, with the CAT(0) input in its median-graph form. -/
theorem octantMedian_ker_eq_range :
    LinearMap.ker (octantMedian.toDescCubeStr).d₂
      = LinearMap.range (octantMedian.toDescCubeStr).d₃ :=
  octantMedian.ker_d₂_eq_range_d₃

end MedianGraphExample

end FiniteChains
