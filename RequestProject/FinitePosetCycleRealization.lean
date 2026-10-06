module

public import RequestProject.OrderNerveAffineEdgePath
public import RequestProject.FiniteSimpleArcConcatenation

@[expose] public section

/-! Realizing an explicitly enumerated finite rank-one poset cycle gives
an actual topological circle. All topological assertions follow from exact
affine edge coordinates. Pending Lean verification. -/

noncomputable section
open scoped Classical unitInterval
open Set Topology

namespace FiniteChains.Comb
open RelativeAttachment

structure FinitePosetCycle (P : Type) [PartialOrder P] (n : ℕ) where
  positive : 0 < n
  vertex : Fin (n + 2) ≃ P
  consecutive : ∀ i : Fin (n + 1),
    vertex i.castSucc ≤ vertex i.succ ∨ vertex i.succ ≤ vertex i.castSucc
  closing : vertex (Fin.last (n + 1)) ≤ vertex 0 ∨ vertex 0 ≤ vertex (Fin.last (n + 1))
  edges : ∀ a b : P, a ≠ b → (a ≤ b ∨ b ≤ a) →
    (∃ i : Fin (n + 1), (a = vertex i.castSucc ∧ b = vertex i.succ) ∨
      (b = vertex i.castSucc ∧ a = vertex i.succ)) ∨
    (a = vertex (Fin.last (n + 1)) ∧ b = vertex 0) ∨
      (b = vertex (Fin.last (n + 1)) ∧ a = vertex 0)
  height : P → ℕ
  height_strict : StrictMono height
  height_le : ∀ p, height p ≤ 1

namespace FinitePosetCycle

variable {P : Type} [PartialOrder P] {n : ℕ} (C : FinitePosetCycle P n)

def edge (i : Fin (n + 1)) := orderNerveComparablePath (C.consecutive i)
def lastEdge := orderNerveComparablePath C.closing

theorem edge_coordinates (i : Fin (n + 1)) (t : I) (p : P) :
    orderNerveRealizationCoordinates P (C.edge i t) p =
      (1 - (t : ℝ)) * (if C.vertex i.castSucc = p then 1 else 0) +
        (t : ℝ) * (if C.vertex i.succ = p then 1 else 0) :=
  orderNerveComparablePath_coordinates _ _ _

theorem lastEdge_coordinates (t : I) (p : P) :
    orderNerveRealizationCoordinates P (C.lastEdge t) p =
      (1 - (t : ℝ)) * (if C.vertex (Fin.last (n + 1)) = p then 1 else 0) +
        (t : ℝ) * (if C.vertex 0 = p then 1 else 0) :=
  orderNerveComparablePath_coordinates _ _ _

theorem vne {i j : Fin (n + 2)} (h : i.val ≠ j.val) : C.vertex i ≠ C.vertex j :=
  fun he => h (congrArg Fin.val (C.vertex.injective he))

theorem edge_injective (i : Fin (n + 1)) : Function.Injective (C.edge i) :=
  orderNerveComparablePath_injective _ (C.vne (by simp))

theorem lastEdge_injective : Function.Injective C.lastEdge :=
  orderNerveComparablePath_injective _ (C.vne (by simp))

theorem edge_meet (i j : Fin (n + 1)) (hij : i < j) (s t : I)
    (h : C.edge i s = C.edge j t) : s = 1 ∧ t = 0 := by
  have hij' : i.val < j.val := hij
  have hi0 := congrArg (fun z => orderNerveRealizationCoordinates P z (C.vertex i.castSucc)) h
  have hj1 := congrArg (fun z => orderNerveRealizationCoordinates P z (C.vertex j.succ)) h
  have hi : C.vertex i.succ ≠ C.vertex i.castSucc := C.vne (by simp)
  have hji : C.vertex j.castSucc ≠ C.vertex i.castSucc := C.vne (by simpa using ne_of_gt hij')
  have hji' : C.vertex j.succ ≠ C.vertex i.castSucc := C.vne (by dsimp; omega)
  have hij₁ : C.vertex i.castSucc ≠ C.vertex j.succ := C.vne (by dsimp; omega)
  have hij₂ : C.vertex i.succ ≠ C.vertex j.succ := C.vne (by dsimp; omega)
  have hj : C.vertex j.castSucc ≠ C.vertex j.succ := C.vne (by simp)
  simp only [edge_coordinates, ite_true, if_neg hi, if_neg hji, if_neg hji',
    mul_one, mul_zero, add_zero] at hi0
  simp only [edge_coordinates, ite_true, if_neg hij₁, if_neg hij₂, if_neg hj,
    mul_one, mul_zero, zero_add, add_zero] at hj1
  exact ⟨Subtype.ext (show (s : ℝ) = 1 by linarith),
    Subtype.ext (show (t : ℝ) = 0 by linarith)⟩

def «prefix» : Path (orderNerveRealizationVertex (C.vertex 0))
    (orderNerveRealizationVertex (C.vertex (Fin.last (n + 1)))) :=
  arcConcat n (orderNerveRealizationVertex ∘ C.vertex) C.edge

theorem prefix_injective : Function.Injective C.prefix :=
  arcConcat_injective n _ _ C.edge_injective C.edge_meet

theorem prefix_meet_last (s t : I) (h : C.prefix s = C.lastEdge t) :
    C.prefix s = orderNerveRealizationVertex (C.vertex 0) ∨
      C.prefix s = orderNerveRealizationVertex (C.vertex (Fin.last (n + 1))) := by
  obtain ⟨i, u, hu⟩ := (arcConcat_range n (orderNerveRealizationVertex ∘ C.vertex)
    C.edge _).mp ⟨s, rfl⟩
  have he := hu.trans h
  by_cases hi : i.val = 0
  · have hc := (C.edge_coordinates i u (C.vertex (Fin.last (n + 1)))).symm.trans
      ((congrArg (fun z => orderNerveRealizationCoordinates P z
        (C.vertex (Fin.last (n + 1)))) he).trans
          (C.lastEdge_coordinates t (C.vertex (Fin.last (n + 1)))))
    have h₀ : C.vertex i.castSucc ≠ C.vertex (Fin.last (n + 1)) := C.vne (by dsimp; omega)
    have h₁ : C.vertex i.succ ≠ C.vertex (Fin.last (n + 1)) := C.vne (by
      have hn := C.positive
      dsimp
      omega)
    have hz : C.vertex 0 ≠ C.vertex (Fin.last (n + 1)) := C.vne (by simp)
    simp only [if_neg h₀, if_neg h₁, if_neg hz,
      ite_true, mul_zero, mul_one, add_zero] at hc
    have ht : t = 1 := Subtype.ext (show (t : ℝ) = 1 by linarith)
    exact Or.inl (h.trans (by rw [ht]; exact C.lastEdge.target))
  · have hc := (C.edge_coordinates i u (C.vertex 0)).symm.trans
      ((congrArg (fun z => orderNerveRealizationCoordinates P z (C.vertex 0)) he).trans
        (C.lastEdge_coordinates t (C.vertex 0)))
    have h₀ : C.vertex i.castSucc ≠ C.vertex 0 := C.vne (by simpa using hi)
    have h₁ : C.vertex i.succ ≠ C.vertex 0 := C.vne (by simp)
    have hz : C.vertex (Fin.last (n + 1)) ≠ C.vertex 0 := C.vne (by simp)
    simp only [if_neg h₀, if_neg h₁, if_neg hz,
      ite_true, mul_zero, mul_one, zero_add, add_zero] at hc
    have ht : t = 0 := Subtype.ext (show (t : ℝ) = 0 by linarith)
    exact Or.inr (h.trans (by rw [ht]; exact C.lastEdge.source))

def traversal : Path (orderNerveRealizationVertex (C.vertex 0))
    (orderNerveRealizationVertex (C.vertex 0)) := C.prefix.trans C.lastEdge

theorem traversal_fiber (s t : I) (h : C.traversal s = C.traversal t) :
    s = t ∨ (s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 0) :=
  path_trans_loop_fiber C.prefix C.lastEdge C.prefix_injective C.lastEdge_injective
    C.prefix_meet_last h

include C in
theorem height_ne {a b : P} (hne : a ≠ b) (h : a ≤ b ∨ b ≤ a) :
    C.height a ≠ C.height b := by
  rcases h with h | h
  · exact ne_of_lt (C.height_strict (lt_of_le_of_ne h hne))
  · exact (ne_of_lt (C.height_strict (lt_of_le_of_ne h hne.symm))).symm

include C in
theorem support_pair [Fintype P] (x : orderNerveRealization P) :
    ∃ a b : P, a ≠ b ∧ (a ≤ b ∨ b ≤ a) ∧
      ∀ p, p ≠ a → p ≠ b → orderNerveRealizationCoordinates P x p = 0 := by
  let c := orderNerveRealizationCoordinates P x
  have hpositive : ∃ a, 0 < c a := by
    by_contra hn
    push_neg at hn
    have hs : ∑ a, c a ≤ 0 := Finset.sum_nonpos (fun a _ => hn a)
    have he : ∑ a, c a = 1 := orderNerveRealizationCoordinates_sum x
    linarith
  obtain ⟨a, ha⟩ := hpositive
  have hc := orderNerveRealizationCoordinates_support_chain x
  by_cases hb : ∃ b, b ≠ a ∧ 0 < c b
  · obtain ⟨b, hba, hb⟩ := hb
    have hab : a ≤ b ∨ b ≤ a := hc ha hb hba.symm
    refine ⟨a, b, hba.symm, hab, ?_⟩
    intro p hpa hpb
    apply le_antisymm _ (orderNerveRealizationCoordinates_nonneg x p)
    by_contra hp
    have hp' : 0 < c p := lt_of_not_ge hp
    have h₁ := C.height_ne hba.symm hab
    have h₂ := C.height_ne hpa (hc hp' ha hpa)
    have h₃ := C.height_ne hpb (hc hp' hb hpb)
    have ha₁ := C.height_le a
    have hb₁ := C.height_le b
    have hp₁ := C.height_le p
    omega
  · have hz : ∀ p, p ≠ a → c p = 0 := by
      intro p hpa
      apply le_antisymm _ (orderNerveRealizationCoordinates_nonneg x p)
      exact le_of_not_gt (fun hp => hb ⟨p, hpa, hp⟩)
    let k := C.vertex.symm a
    by_cases hk : k = Fin.last (n + 1)
    · have he : C.vertex (Fin.last (n + 1)) = a :=
        (congrArg C.vertex hk).symm.trans (C.vertex.apply_symm_apply a)
      refine ⟨a, C.vertex 0, ?_, ?_, fun p hpa _ => hz p hpa⟩
      · rw [← he]
        exact C.vne (by simp)
      · rw [← he]
        exact C.closing
    · obtain ⟨i, hi⟩ := Fin.exists_castSucc_eq.mpr hk
      have he : C.vertex i.castSucc = a :=
        (congrArg C.vertex hi).trans (C.vertex.apply_symm_apply a)
      refine ⟨a, C.vertex i.succ, ?_, ?_, fun p hpa _ => hz p hpa⟩
      · rw [← he]
        exact C.vne (by simp)
      · rw [← he]
        exact C.consecutive i

theorem traversal_surjective : Function.Surjective C.traversal := by
  letI : Fintype P := Fintype.ofEquiv (Fin (n + 2)) C.vertex
  intro x
  obtain ⟨a, b, hne, hab, hs⟩ := C.support_pair x
  rcases C.edges a b hne hab with ⟨i, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · obtain ⟨t, ht⟩ := orderNerveComparablePath_of_support (C.consecutive i)
      (C.vne (by simp)) x hs
    change x ∈ Set.range (C.prefix.trans C.lastEdge)
    rw [Path.trans_range]
    exact Or.inl ((arcConcat_range n (orderNerveRealizationVertex ∘ C.vertex) C.edge x).mpr
      ⟨i, t, ht⟩)
  · obtain ⟨t, ht⟩ := orderNerveComparablePath_of_support (C.consecutive i)
      (C.vne (by simp)) x (fun p h₀ h₁ => hs p h₁ h₀)
    change x ∈ Set.range (C.prefix.trans C.lastEdge)
    rw [Path.trans_range]
    exact Or.inl ((arcConcat_range n (orderNerveRealizationVertex ∘ C.vertex) C.edge x).mpr
      ⟨i, t, ht⟩)
  · obtain ⟨t, ht⟩ := orderNerveComparablePath_of_support C.closing
      (C.vne (by simp)) x hs
    change x ∈ Set.range (C.prefix.trans C.lastEdge)
    rw [Path.trans_range]
    exact Or.inr ⟨t, ht⟩
  · obtain ⟨t, ht⟩ := orderNerveComparablePath_of_support C.closing
      (C.vne (by simp)) x (fun p h₀ h₁ => hs p h₁ h₀)
    change x ∈ Set.range (C.prefix.trans C.lastEdge)
    rw [Path.trans_range]
    exact Or.inr ⟨t, ht⟩

def boundaryHomeomorph : orderNerveRealization P ≃ₜ UnitBoundary (Fin 2 → ℝ) :=
  (simpleLoopBoundaryHomeomorph C.traversal C.traversal_surjective C.traversal_fiber).symm

end FinitePosetCycle
end FiniteChains.Comb
