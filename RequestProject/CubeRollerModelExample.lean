module

public import RequestProject.CubeRollerModel

@[expose] public section

/-!
# Models of the Roller axioms

The hypotheses of `FiniteChains.RollerModel` (a median-closed family of finite sets of
hyperplanes, based at `∅`, of dimension at most three) are not vacuous.  This file exhibits
two models, a finite and an infinite one, and checks in both that the complex really has
three-dimensional cells, so that `FiniteChains.RollerModel.ker_d₂_eq_range_d₃` is a statement
with content.

* `FiniteChains.RollerExamples.cube3` — the three-cube itself: all subsets of a three element
  set of hyperplanes.
* `FiniteChains.RollerExamples.octantR` — the cubulated positive octant of three-space in
  Roller coordinates: the hyperplanes are indexed by `ℕ × Fin 3` (three families of parallel
  walls) and a vertex is a finite set of them which is downward closed in every family.  This
  is an infinite three-dimensional complex.
-/

namespace FiniteChains

namespace RollerExamples

/-! ## The three-cube -/

/-- The three-cube: every subset of the three hyperplanes is a vertex. -/
def cube3 : RollerModel (Fin 3) where
  W := Set.univ
  base_mem := trivial
  med_mem := fun _ _ _ => trivial
  dim_le := by
    intro A _ s hs
    have h : s.card ≤ A.card :=
      RollerModel.card_dn_le (fun B hB => ⟨(hs B hB).2.1, (hs B hB).2.2⟩)
    have hA : A.card ≤ 3 := by simpa using Finset.card_le_univ A
    omega

/-- The vertex of the three-cube opposite to the base vertex. -/
def cube3.top : cube3.Vtx := ⟨{0, 1, 2}, trivial⟩

/-- The three descending neighbours of the top vertex. -/
def cube3.face (i : Fin 3) : cube3.Vtx := ⟨({0, 1, 2} : Finset (Fin 3)).erase i, trivial⟩

theorem cube3.face_mem (i : Fin 3) : cube3.face i ∈ cube3.dnR cube3.top := by
  refine ⟨Finset.erase_subset _ _, ?_⟩
  have hi : i ∈ ({0, 1, 2} : Finset (Fin 3)) := by fin_cases i <;> decide
  show (({0, 1, 2} : Finset (Fin 3)).erase i).card + 1 = ({0, 1, 2} : Finset (Fin 3)).card
  rw [Finset.card_erase_of_mem hi]
  fin_cases i <;> decide

theorem cube3.face_ne {i j : Fin 3} (h : i ≠ j) : cube3.face i ≠ cube3.face j := by
  intro hc
  have hval : ({0, 1, 2} : Finset (Fin 3)).erase i = ({0, 1, 2} : Finset (Fin 3)).erase j :=
    congrArg Subtype.val hc
  have hj : j ∈ ({0, 1, 2} : Finset (Fin 3)).erase i :=
    Finset.mem_erase.2 ⟨Ne.symm h, by fin_cases j <;> decide⟩
  rw [hval] at hj
  exact (Finset.mem_erase.1 hj).1 rfl

/-- The three-cube model really has a three-dimensional cell. -/
theorem cube3_nonempty_CbC : Nonempty cube3.toDescCubeStr.CbC :=
  DescCubeStr.nonempty_CbC (S := cube3.toDescCubeStr) (cube3.face_mem 0) (cube3.face_mem 1)
    (cube3.face_mem 2) (cube3.face_ne (by decide)) (cube3.face_ne (by decide))
    (cube3.face_ne (by decide))

/-- The vanishing of the second homology applies to the three-cube. -/
theorem cube3_ker_eq_range :
    LinearMap.ker cube3.toDescCubeStr.d₂ = LinearMap.range cube3.toDescCubeStr.d₃ :=
  cube3.ker_d₂_eq_range_d₃

/-! ## The cubulated positive octant -/

/-- A finite set of walls is *downward closed* when, in each of the three families of
parallel walls, it contains an initial segment. -/
def Down (A : Finset (ℕ × Fin 3)) : Prop := ∀ (n : ℕ) (j : Fin 3), (n + 1, j) ∈ A → (n, j) ∈ A

theorem Down.le_mem {A : Finset (ℕ × Fin 3)} (hA : Down A) {n m : ℕ} {j : Fin 3}
    (hm : (m, j) ∈ A) (hnm : n ≤ m) : (n, j) ∈ A := by
  induction m with
  | zero =>
    obtain rfl : n = 0 := Nat.le_zero.1 hnm
    exact hm
  | succ k ih =>
    rcases Nat.lt_or_ge n (k + 1) with h | h
    · exact ih (hA k j hm) (by omega)
    · obtain rfl : n = k + 1 := le_antisymm hnm h
      exact hm

/-- The cubulated positive octant of three-space, in Roller coordinates. -/
def octantR : RollerModel (ℕ × Fin 3) where
  W := {A | Down A}
  base_mem := by
    intro n j h
    simp at h
  med_mem := by
    intro A B C hA hB hC n j h
    simp only [medFinset, Finset.mem_union, Finset.mem_inter] at h ⊢
    rcases h with (⟨h1, h2⟩ | ⟨h1, h2⟩) | ⟨h1, h2⟩
    · exact Or.inl (Or.inl ⟨hA n j h1, hB n j h2⟩)
    · exact Or.inl (Or.inr ⟨hB n j h1, hC n j h2⟩)
    · exact Or.inr ⟨hA n j h1, hC n j h2⟩
  dim_le := by
    intro A hA s hs
    classical
    set T : Finset (ℕ × Fin 3) := A.filter (fun p => (p.1 + 1, p.2) ∉ A) with hTdef
    have hAD : Down A := hA
    have hbound : s.card ≤ T.card := by
      refine RollerModel.card_dn_le_of_tops (fun B hB => ⟨(hs B hB).2.1, (hs B hB).2.2⟩) ?_
      intro B hB p hp hpB
      obtain ⟨hBW, hBsub, hBcard⟩ := hs B hB
      have hBD : Down B := hBW
      have hBe : B = A.erase p := RollerModel.eq_erase_of_notMem hBsub hBcard hp hpB
      refine Finset.mem_filter.2 ⟨hp, ?_⟩
      intro hcon
      have hne : (p.1 + 1, p.2) ≠ p := by
        intro hq
        exact absurd (congrArg Prod.fst hq) (by omega)
      have hmem : (p.1 + 1, p.2) ∈ B := by
        rw [hBe]
        exact Finset.mem_erase.2 ⟨hne, hcon⟩
      have : (p.1, p.2) ∈ B := hBD p.1 p.2 hmem
      exact hpB (by simpa using this)
    have hT : T.card ≤ 3 := by
      have hinj : Set.InjOn (fun p : ℕ × Fin 3 => p.2) T := by
        intro p hp q hq hpq
        have hpA : p ∈ A := (Finset.mem_filter.1 hp).1
        have hqA : q ∈ A := (Finset.mem_filter.1 hq).1
        have hpT : (p.1 + 1, p.2) ∉ A := (Finset.mem_filter.1 hp).2
        have hqT : (q.1 + 1, q.2) ∉ A := (Finset.mem_filter.1 hq).2
        have hj : p.2 = q.2 := hpq
        have h1 : ¬ p.1 < q.1 := by
          intro hlt
          refine hpT ?_
          have : (q.1, p.2) ∈ A := by rw [hj]; simpa using hqA
          exact hAD.le_mem this (by omega)
        have h2 : ¬ q.1 < p.1 := by
          intro hlt
          refine hqT ?_
          have hq2 : (p.1, q.2) ∈ A := by rw [← hj]; simpa using hpA
          exact hAD.le_mem hq2 (by omega)
        have : p.1 = q.1 := by omega
        exact Prod.ext this hj
      have := Finset.card_le_card_of_injOn (f := fun p : ℕ × Fin 3 => p.2)
        (t := (Finset.univ : Finset (Fin 3))) (fun a _ => by simp) hinj
      simpa using this
    omega

/-- A set of walls all of which are the first wall of their family is downward closed. -/
theorem down_of_first_zero {X : Finset (ℕ × Fin 3)} (h : ∀ p ∈ X, p.1 = 0) : Down X := by
  intro n j hn
  exact absurd (h _ hn) (by omega)

/-- The three walls nearest to the base vertex, one in each family: the top vertex of the
unit cube at the origin. -/
def topSet : Finset (ℕ × Fin 3) := {(0, 0), (0, 1), (0, 2)}

theorem first_eq_zero_of_mem_topSet {p : ℕ × Fin 3} (hp : p ∈ topSet) : p.1 = 0 := by
  simp only [topSet, Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl <;> rfl

theorem mem_topSet (i : Fin 3) : ((0 : ℕ), i) ∈ topSet := by
  fin_cases i <;> decide

theorem card_topSet : topSet.card = 3 := by decide

/-- The top vertex of the unit cube at the origin of the octant. -/
def octantR.top : octantR.Vtx :=
  ⟨topSet, down_of_first_zero fun _ hp => first_eq_zero_of_mem_topSet hp⟩

/-- Its three descending neighbours. -/
def octantR.face (i : Fin 3) : octantR.Vtx :=
  ⟨topSet.erase (0, i),
    down_of_first_zero fun _ hp => first_eq_zero_of_mem_topSet (Finset.mem_of_mem_erase hp)⟩

theorem octantR.face_mem (i : Fin 3) : octantR.face i ∈ octantR.dnR octantR.top := by
  refine ⟨?_, ?_⟩
  · show topSet.erase (0, i) ⊆ topSet
    exact Finset.erase_subset _ _
  show (topSet.erase (0, i)).card + 1 = topSet.card
  rw [Finset.card_erase_of_mem (mem_topSet i), card_topSet]

theorem octantR.face_ne {i j : Fin 3} (h : i ≠ j) : octantR.face i ≠ octantR.face j := by
  intro hc
  have hval : topSet.erase (0, i) = topSet.erase (0, j) := congrArg Subtype.val hc
  have hj : ((0 : ℕ), j) ∈ topSet.erase (0, i) :=
    Finset.mem_erase.2 ⟨fun hcon => h (congrArg Prod.snd hcon).symm, mem_topSet j⟩
  rw [hval] at hj
  exact (Finset.mem_erase.1 hj).1 rfl

/-- The octant model really has three-dimensional cells. -/
theorem octantR_nonempty_CbC : Nonempty octantR.toDescCubeStr.CbC :=
  DescCubeStr.nonempty_CbC (S := octantR.toDescCubeStr) (octantR.face_mem 0)
    (octantR.face_mem 1) (octantR.face_mem 2) (octantR.face_ne (by decide))
    (octantR.face_ne (by decide)) (octantR.face_ne (by decide))

/-- The vanishing of the second homology applies to the infinite octant complex. -/
theorem octantR_ker_eq_range :
    LinearMap.ker octantR.toDescCubeStr.d₂ = LinearMap.range octantR.toDescCubeStr.d₃ :=
  octantR.ker_d₂_eq_range_d₃

end RollerExamples

end FiniteChains
