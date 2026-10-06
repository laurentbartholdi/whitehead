module

public import RequestProject.TopologicalSingular.SingularHornFilling
public import RequestProject.TopologicalSingular.SimplexFaceIntersections

@[expose] public section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.TopologicalSingular
universe u
variable {X : Type u} [TopologicalSpace X] {n : ℕ}

noncomputable def singularDegeneracy (i : Fin (n + 1)) (tau : Simplex X n) :
    Simplex X (n + 1) := (simplices X).σ i tau

@[simp] theorem singular_face_const (i : Fin (n + 2)) (x : X) :
    face i (ContinuousMap.const (Domain (n + 1)) x) =
      ContinuousMap.const (Domain n) x := rfl

@[simp] theorem singular_degeneracy_const (i : Fin (n + 1)) (x : X) :
    singularDegeneracy i (ContinuousMap.const (Domain n) x) =
      ContinuousMap.const (Domain (n + 1)) x := rfl

@[simp] theorem singular_face_degeneracy_self (i : Fin (n + 1)) (tau : Simplex X n) :
    face i.castSucc (singularDegeneracy i tau) = tau :=
  CategoryTheory.ConcreteCategory.congr_hom ((simplices X).δ_comp_σ_self (i := i)) tau

@[simp] theorem singular_face_degeneracy_succ (i : Fin (n + 1)) (tau : Simplex X n) :
    face i.succ (singularDegeneracy i tau) = tau :=
  CategoryTheory.ConcreteCategory.congr_hom ((simplices X).δ_comp_σ_succ (i := i)) tau

theorem singular_face_degeneracy_le (i : Fin (n + 2)) (j : Fin (n + 1))
    (h : i ≤ j.castSucc) (tau : Simplex X (n + 1)) :
    face i.castSucc (singularDegeneracy j.succ tau) =
      singularDegeneracy j (face i tau) :=
  CategoryTheory.ConcreteCategory.congr_hom ((simplices X).δ_comp_σ_of_le h) tau

theorem singular_face_degeneracy_gt (i : Fin (n + 2)) (j : Fin (n + 1))
    (h : j.castSucc < i) (tau : Simplex X (n + 1)) :
    face i.succ (singularDegeneracy j.castSucc tau) =
      singularDegeneracy j (face i tau) :=
  CategoryTheory.ConcreteCategory.congr_hom ((simplices X).δ_comp_σ_of_gt h) tau

/-- Algebraic face compatibility suffices for a genuine topological horn filler. -/
theorem singular_horn_filler_of_face_compatible {Y : Type} [TopologicalSpace Y]
    (i : Fin (n + 3)) (g : ∀ j : Fin (n + 3), j ≠ i → Simplex Y (n + 1))
    (hg : ∀ (j : Fin (n + 3)) (k : Fin (n + 2))
      (hj : j ≠ i) (hk : j.succAbove k ≠ i),
      face k (g j hj) = face (k.predAbove j) (g (j.succAbove k) hk)) :
    ∃ tau : Simplex Y (n + 2), ∀ (j : Fin (n + 3)) (hj : j ≠ i),
      face j tau = g j hj := by
  apply singular_horn_filler_exists i g
  intro j k hj hk z w h
  by_cases hjk : j = k
  · subst k
    have hzw := simplex_face_injective j h
    subst w
    rfl
  obtain ⟨a, ha⟩ := Fin.exists_succAbove_eq (Ne.symm hjk)
  have hz : z.val a = 0 := by
    rw [← simplex_face_coordinate_succAbove j z a, ha, h]
    exact simplex_face_coordinate_zero k w
  obtain ⟨q, hq⟩ := domain_zero_coordinate_face z a hz
  have hw : w = stdSimplex.map (SimplexCategory.δ (a.predAbove j)) q := by
    apply simplex_face_injective k
    rw [← h, ← hq]
    simpa only [ha] using simplex_double_face_swap j a q
  have hka : j.succAbove a ≠ i := by simpa only [ha] using hk
  have he := congrArg (fun t : Simplex Y n => t q) (hg j a hj hka)
  simpa only [face_apply, ha, hq, hw] using he

end FiniteChains.TopologicalSingular
