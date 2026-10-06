import Mathlib.Topology.CWComplex.Classical.Basic
import Mathlib.Analysis.Normed.Module.Connected

/-! Actual paths from arbitrary points of an original classical CW complex
to its original vertices. This uses only characteristic disks and the finite
lower-cell boundary axiom. No order-nerve model is substituted for the space.
Pending Lean verification. -/

noncomputable section
open scoped Classical
open Set Topology Metric

namespace FiniteChains.ClassicalCW

variable {X : Type} [TopologicalSpace X] [CWComplex (Set.univ : Set X)]

def vertexPoint (v : RelCWComplex.cell (Set.univ : Set X) 0) : X :=
  RelCWComplex.map 0 v ![]

/-- Any two points in a single characteristic closed disk are joined in
the actual image of that disk, including points on its attached boundary. -/
theorem closedCell_joined (n : ℕ) (j : RelCWComplex.cell (Set.univ : Set X) n)
    {x y : X} (hx : x ∈ RelCWComplex.closedCell n j)
    (hy : y ∈ RelCWComplex.closedCell n j) :
    JoinedIn (RelCWComplex.closedCell n j) x y := by
  obtain ⟨a, ha, rfl⟩ := hx
  obtain ⟨b, hb, rfl⟩ := hy
  exact ((isPathConnected_closedBall (E := Fin n → ℝ) zero_le_one).joinedIn a ha b hb).map_continuousOn
    (RelCWComplex.continuousOn n j)

theorem closedCell_joined_vertex (n : ℕ)
    (j : RelCWComplex.cell (Set.univ : Set X) n) {x : X}
    (hx : x ∈ RelCWComplex.closedCell n j) :
    ∃ v : RelCWComplex.cell (Set.univ : Set X) 0, Joined x (vertexPoint v) := by
  induction n using Nat.strong_induction_on generalizing x with
  | h n ih =>
    by_cases hn : n = 0
    · subst n
      refine ⟨j, ?_⟩
      have he : x = vertexPoint j := by
        simpa only [RelCWComplex.closedCell_zero_eq_singleton, Set.mem_singleton_iff,
          vertexPoint] using hx
      simpa only [he] using (Joined.refl (vertexPoint j))
    · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
      letI : Nonempty (Fin n) := ⟨⟨0, hnpos⟩⟩
      let a : Fin n → ℝ := fun _ => 1
      have ha : a ∈ sphere (0 : Fin n → ℝ) 1 := by
        simp only [Metric.mem_sphere, dist_zero_right, a, pi_norm_const, norm_one]
      obtain ⟨I, hI⟩ := Topology.CWComplex.mapsTo' (C := (Set.univ : Set X)) n j
      obtain ⟨m, hmn, k, _, hk⟩ := by
        simpa only [Set.mem_iUnion] using hI ha
      obtain ⟨v, hv⟩ := ih m hmn k hk
      refine ⟨v, ?_⟩
      have hp : Joined x (RelCWComplex.map n j a) :=
        (closedCell_joined n j hx
          ⟨a, Metric.sphere_subset_closedBall ha, rfl⟩).joined
      exact hp.trans hv

/-- Every actual point has an actual continuous path to an original
zero-cell. The CW complex need not be finite or connected. -/
theorem point_joined_vertex (x : X) :
    ∃ v : RelCWComplex.cell (Set.univ : Set X) 0, Joined x (vertexPoint v) := by
  have hx : x ∈ ⋃ n, ⋃ j : RelCWComplex.cell (Set.univ : Set X) n,
      RelCWComplex.closedCell n j := by rw [CWComplex.union]; trivial
  obtain ⟨n, j, hx⟩ := by simpa only [Set.mem_iUnion] using hx
  exact closedCell_joined_vertex n j hx

def pointVertex (x : X) : RelCWComplex.cell (Set.univ : Set X) 0 :=
  Classical.choose (point_joined_vertex x)

def pointVertexPath (x : X) : Path x (vertexPoint (pointVertex x)) :=
  (Classical.choose_spec (point_joined_vertex x)).somePath

end FiniteChains.ClassicalCW
