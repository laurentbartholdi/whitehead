import RequestProject.TopologicalSingular.SingularSimplicialHelpers
import RequestProject.TopologicalSingular.TetrahedronStickShell
import RequestProject.TopologicalSingular.BasedTriangleHomotopy

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.TopologicalSingular
variable {X : Type} [TopologicalSpace X] {x : X}

/-- A singular triangle whose three edges are the constant edge at `x`. -/
structure PointedSingularTriangle (X : Type) [TopologicalSpace X] (x : X) where
  map : Simplex X 2
  based : ∀ i : Fin 3, face i map = ContinuousMap.const (Domain 1) x

namespace PointedSingularTriangle

noncomputable def pi2 (a : PointedSingularTriangle X x) :
    Additive (HomotopyGroup (Fin 2) X x) :=
  Additive.ofMul (Quotient.mk _ (basedTriangleSquare a.map a.based))

def constant (x : X) : PointedSingularTriangle X x :=
  ⟨ContinuousMap.const (Domain 2) x, fun _ => rfl⟩

@[simp] theorem constant_pi2 (x : X) : (constant x).pi2 = 0 := by
  unfold pi2 constant
  rw [basedTriangleSquare_const, ← HomotopyGroup.one_def]
  rfl

theorem pi2_congr (a b : PointedSingularTriangle X x) (h : a.map = b.map) :
    a.pi2 = b.pi2 := by
  cases a
  cases b
  cases h
  rfl

theorem degeneracy_zero_faces (a : PointedSingularTriangle X x) (i : Fin 4) :
    face i (singularDegeneracy 0 a.map) =
      ![a.map, a.map, (constant x).map, (constant x).map] i := by
  fin_cases i
  · exact singular_face_degeneracy_self 0 a.map
  · exact singular_face_degeneracy_succ 0 a.map
  · simpa [a.based, singular_degeneracy_const, constant, Fin.succ, Fin.castSucc, Fin.castAdd] using
      singular_face_degeneracy_gt 1 0 (by decide) a.map
  · simpa [a.based, singular_degeneracy_const, constant, Fin.succ, Fin.castSucc, Fin.castAdd] using
      singular_face_degeneracy_gt 2 0 (by decide) a.map

theorem degeneracy_one_faces (a : PointedSingularTriangle X x) (i : Fin 4) :
    face i (singularDegeneracy 1 a.map) =
      ![(constant x).map, a.map, a.map, (constant x).map] i := by
  fin_cases i
  · simpa [a.based, singular_degeneracy_const, constant, Fin.succ, Fin.castSucc, Fin.castAdd] using
      singular_face_degeneracy_le 0 0 (by decide) a.map
  · exact singular_face_degeneracy_self 1 a.map
  · exact singular_face_degeneracy_succ 1 a.map
  · simpa [a.based, singular_degeneracy_const, constant, Fin.succ, Fin.castSucc, Fin.castAdd] using
      singular_face_degeneracy_gt 2 1 (by decide) a.map

theorem degeneracy_two_faces (a : PointedSingularTriangle X x) (i : Fin 4) :
    face i (singularDegeneracy 2 a.map) =
      ![(constant x).map, (constant x).map, a.map, a.map] i := by
  fin_cases i
  · simpa [a.based, singular_degeneracy_const, constant, Fin.succ, Fin.castSucc, Fin.castAdd] using
      singular_face_degeneracy_le 0 1 (by decide) a.map
  · simpa [a.based, singular_degeneracy_const, constant, Fin.succ, Fin.castSucc, Fin.castAdd] using
      singular_face_degeneracy_le 1 1 (by decide) a.map
  · exact singular_face_degeneracy_self 2 a.map
  · exact singular_face_degeneracy_succ 2 a.map

theorem tetrahedron_face_pi2 (tau : Simplex X 3)
    (hedge : ∀ (i : Fin 4) (j : Fin 3),
      face j (face i tau) = ContinuousMap.const (Domain 1) x)
    (i : Fin 4) (a : PointedSingularTriangle X x) (ha : face i tau = a.map) :
    tetrahedronFacePi2Class tau hedge i = a.pi2 := by
  change (PointedSingularTriangle.mk (face i tau) (hedge i)).pi2 = a.pi2
  exact pi2_congr _ _ ha

/-- Multiplication obtained from the cubical shell when the first face is constant. -/
theorem first_face_constant_relation (a b c : PointedSingularTriangle X x)
    (tau : Simplex X 3)
    (hfaces : ∀ i : Fin 4,
      face i tau = ![(constant x).map, a.map, b.map, c.map] i) :
    a.pi2 + c.pi2 = b.pi2 := by
  have hedge : ∀ (i : Fin 4) (j : Fin 3),
      face j (face i tau) = ContinuousMap.const (Domain 1) x := by
    intro i j
    rw [hfaces]
    fin_cases i <;> simp [a.based, b.based, c.based, constant]
  have h := tetrahedronStickShell_face_relation tau hedge (hfaces 0)
  rw [tetrahedron_face_pi2 tau hedge 1 a (hfaces 1),
    tetrahedron_face_pi2 tau hedge 3 c (hfaces 3),
    tetrahedron_face_pi2 tau hedge 2 b (hfaces 2)] at h
  exact h

end PointedSingularTriangle
end FiniteChains.TopologicalSingular
