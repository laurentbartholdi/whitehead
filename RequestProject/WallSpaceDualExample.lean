module

public import RequestProject.WallSpaceDualConnected

@[expose] public section

/-!
# Wall spaces: the hypotheses are not vacuous

Two models of `FiniteChains.WallSpace` are exhibited.

* `FiniteChains.WallExamples.cubeWalls` — the three coordinate walls of the three-cube.  Its
  dual is the whole three-cube: all eight orientations are consistent, the model has a
  genuine three-dimensional cell (`cubeDual_nonempty_CbC`), and therefore
  `cubeDual_ker_eq_range` is a statement with content.
* `FiniteChains.WallExamples.triangleWalls` — three points, the `i`-th wall separating the
  `i`-th point from the other two.  Here the dual is strictly larger than the space itself:
  the orientation choosing the "large" side of every wall is consistent although the three
  large sides have empty common intersection (`triangle_dual_not_point`).  This is the
  standard example showing that Sageev's dual adds the missing median points.
-/

namespace FiniteChains

open RollerBridge

namespace WallExamples

/-! ## The three-cube -/

/-- The wall space of the three-cube: the points are the vertices of the cube and the walls
are the three coordinate hyperplanes. -/
def cubeWalls : WallSpace (Fin 3 → Bool) (Fin 3) where
  side i x := x i
  sep := by
    intro x y h
    by_contra hc
    push_neg at hc
    exact h (funext fun i => hc i)
  fin := fun _ _ => Set.toFinite _

/-- Every orientation of the three coordinate walls is consistent: it is realised by a
vertex of the cube. -/
theorem cubeWalls_dualW (x₀ : Fin 3 → Bool) : cubeWalls.dualW x₀ = Set.univ := by
  ext A
  simp only [Set.mem_univ, iff_true, WallSpace.mem_dualW]
  intro i j
  exact ⟨cubeWalls.flipOn x₀ A, rfl, rfl⟩

/-- The dual of the three-cube is at most three dimensional. -/
theorem cubeWalls_dim (x₀ : Fin 3 → Bool) :
    ∀ A ∈ cubeWalls.dualW x₀, ∀ s : Finset (Finset (Fin 3)),
      (∀ B ∈ s, B ∈ cubeWalls.dualW x₀ ∧ B ⊆ A ∧ B.card + 1 = A.card) → s.card ≤ 3 :=
  WallSpace.dualW_dim_le (by simp) x₀

/-- The three coordinate walls of the cube are pairwise distinct. -/
theorem cubeWalls_reduced : cubeWalls.Reduced := by
  intro i j b c h
  by_contra hij
  have hx : cubeWalls.side i (fun k => if k = i then b else !c) = b := by
    show (if i = i then b else !c) = b
    simp
  have h2 := (h _).1 hx
  have h3 : cubeWalls.side j (fun k => if k = i then b else !c) = !c := by
    show (if j = i then b else !c) = !c
    rw [if_neg (Ne.symm hij)]
  rw [h2] at h3
  exact (Bool.not_ne_self c) h3.symm

/-- The cube complex dual to the wall space of the three-cube. -/
noncomputable def cubeDual : RollerModel (Fin 3) :=
  cubeWalls.dualModel (fun _ => false) (cubeWalls_dim _)

theorem cubeDual_W : cubeDual.W = Set.univ := cubeWalls_dualW _

theorem cubeDual_mem (A : Finset (Fin 3)) : A ∈ cubeDual.W := by
  rw [cubeDual_W]; trivial

/-- The vertex of the dual opposite to the base vertex. -/
noncomputable def cubeDual.top : cubeDual.Vtx := ⟨{0, 1, 2}, cubeDual_mem _⟩

/-- The three descending neighbours of the top vertex. -/
noncomputable def cubeDual.face (i : Fin 3) : cubeDual.Vtx :=
  ⟨({0, 1, 2} : Finset (Fin 3)).erase i, cubeDual_mem _⟩

theorem cubeDual.face_mem (i : Fin 3) : cubeDual.face i ∈ cubeDual.dnR cubeDual.top := by
  refine ⟨Finset.erase_subset _ _, ?_⟩
  have hi : i ∈ ({0, 1, 2} : Finset (Fin 3)) := by fin_cases i <;> decide
  show (({0, 1, 2} : Finset (Fin 3)).erase i).card + 1 = ({0, 1, 2} : Finset (Fin 3)).card
  rw [Finset.card_erase_of_mem hi]
  fin_cases i <;> decide

theorem cubeDual.face_ne {i j : Fin 3} (h : i ≠ j) : cubeDual.face i ≠ cubeDual.face j := by
  intro hc
  have hval : ({0, 1, 2} : Finset (Fin 3)).erase i = ({0, 1, 2} : Finset (Fin 3)).erase j :=
    congrArg Subtype.val hc
  have hj : j ∈ ({0, 1, 2} : Finset (Fin 3)).erase i :=
    Finset.mem_erase.2 ⟨Ne.symm h, by fin_cases j <;> decide⟩
  rw [hval] at hj
  exact (Finset.mem_erase.1 hj).1 rfl

/-- The dual of the three-cube really has a three-dimensional cell. -/
theorem cubeDual_nonempty_CbC : Nonempty cubeDual.toDescCubeStr.CbC :=
  DescCubeStr.nonempty_CbC (S := cubeDual.toDescCubeStr) (cubeDual.face_mem 0)
    (cubeDual.face_mem 1) (cubeDual.face_mem 2) (cubeDual.face_ne (by decide))
    (cubeDual.face_ne (by decide)) (cubeDual.face_ne (by decide))

/-- `ker d₂ = im d₃` for the cube complex dual to the wall space of the three-cube. -/
theorem cubeDual_ker_eq_range :
    LinearMap.ker cubeDual.toDescCubeStr.d₂ = LinearMap.range cubeDual.toDescCubeStr.d₃ :=
  cubeDual.ker_d₂_eq_range_d₃

/-! ## Three points, three walls: the dual is strictly larger -/

/-- Three points with three walls, the `i`-th wall separating the point `i` from the other
two. -/
def triangleWalls : WallSpace (Fin 3) (Fin 3) where
  side i x := decide (x = i)
  sep := by
    intro x y h
    exact ⟨x, by simp [Ne.symm h]⟩
  fin := fun _ _ => Set.toFinite _

/-- **The dual of a wall space can be strictly larger than the space itself.**  For three
points with their three walls, the orientation choosing the large side of every wall (the
coordinate set `{0}` based at the point `0`) is a vertex of the dual which is not the image
of any of the three points; it is the missing median of the three points. -/
theorem triangle_dual_not_point :
    ∃ A ∈ triangleWalls.dualW 0, ∀ x : Fin 3, A ≠ triangleWalls.coord 0 x := by
  refine ⟨{0}, ?_, ?_⟩
  · intro i j
    fin_cases i <;> fin_cases j <;> decide
  · intro x h
    have h' := congrFun (congrArg (triangleWalls.flipOn 0) h) x
    rw [WallSpace.flipOn_coord] at h'
    revert h'
    fin_cases x <;> decide

/-- The three walls of the three points are pairwise distinct. -/
theorem triangleWalls_reduced : triangleWalls.Reduced := by
  show ∀ (i j : Fin 3) (b c : Bool),
    (∀ x : Fin 3, triangleWalls.side i x = b ↔ triangleWalls.side j x = c) → i = j
  decide

/-- The dual of the three points, as a gated Roller model: a median graph. -/
noncomputable def triangleDual : GatedRollerModel (Fin 3) :=
  triangleWalls.gatedDualModel triangleWalls_reduced 0 (WallSpace.dualW_dim_le (by simp) 0)

/-- The graph of the dual of the three points is connected. -/
theorem triangleDual_connected : (triangleDual.graph).Connected := triangleDual.connected

/-- The dual of the three-cube, as a gated Roller model. -/
noncomputable def cubeGatedDual : GatedRollerModel (Fin 3) :=
  cubeWalls.gatedDualModel cubeWalls_reduced (fun _ => false) (cubeWalls_dim _)

/-- The graph of the dual of the three-cube is connected, and the number of separating walls
is its edge metric. -/
theorem cubeGatedDual_connected : (cubeGatedDual.graph).Connected := cubeGatedDual.connected

theorem cubeGatedDual_dist (u v : cubeGatedDual.Vtx) :
    (cubeGatedDual.graph).dist u v = dsym u.1 v.1 :=
  cubeGatedDual.dist_eq_dsym u v

end WallExamples

end FiniteChains
