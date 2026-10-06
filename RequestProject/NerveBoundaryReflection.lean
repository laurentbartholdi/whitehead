import RequestProject.NerveDegreeTransfer

/-! Reflection of actual fillings under deletion of an acyclic attaching piece. -/
namespace FiniteChains.Nerve
universe u
variable {P : Type u} [Preorder P]

/-- A homogeneous chain in `B` that bounds in `U` already bounds in `B`. -/
def ReflectsBoundsIn (U B : P → Prop) (n : ℕ) : Prop :=
  ∀ c ∈ IncOn B, lengthProjection n c = c →
    (∃ y ∈ IncOn U, bdry y = c) → ∃ y ∈ IncOn B, bdry y = c

/-- The injectivity half of the chain gluing argument. Only intersection cycles
in the degree of the chain being filled need to bound. -/
theorem reflectsBoundsIn_union_of_unmixed {A B U : P → Prop} {n : ℕ}
    (hmix : ∀ a b : P, a ≤ b → U a → U b → (A a ∧ A b) ∨ (B a ∧ B b))
    (hJ : FillsDegreeIn (fun p => A p ∧ B p) n) : ReflectsBoundsIn U A n := by
  intro c hc hd hbound
  obtain ⟨y, hy, hdy⟩ := hbound
  obtain ⟨a₀, ha₀, b₀, hb₀, hsplit⟩ := exists_split_of_unmixed hmix hy
  let a := lengthProjection (n + 1) a₀
  let b := lengthProjection (n + 1) b₀
  have ha : a ∈ IncOn A := lengthProjection_mem_incOn _ ha₀
  have hb : b ∈ IncOn B := lengthProjection_mem_incOn _ hb₀
  have hsum : bdry a + bdry b = c := by
    rw [← map_add, ← map_add, ← hsplit, ← lengthProjection_bdry, hdy, hd]
  have hdbA : bdry b ∈ IncOn A := by
    have he : bdry b = c - bdry a := by rw [← hsum]; abel
    rw [he]
    exact AddSubgroup.sub_mem _ hc (bdry_mem_incOn ha)
  have hdbJ : bdry b ∈ IncOn (fun p => A p ∧ B p) := by
    rw [← incOn_inf]
    exact ⟨hdbA, bdry_mem_incOn hb⟩
  have hdbd : lengthProjection n (bdry b) = bdry b := by
    rw [lengthProjection_bdry]
    exact congrArg bdry (lengthProjection_idempotent _ _)
  obtain ⟨z, hz, hdz⟩ := hJ (bdry b) hdbJ hdbd (by simp [bdry_bdry])
  refine ⟨a + z, AddSubgroup.add_mem _ ha (incOn_mono (fun _ h => h.1) hz), ?_⟩
  rw [map_add, hdz, hsum]

theorem reflectsBoundsIn_trans {U B C : P → Prop} {n : ℕ}
    (hCB : ∀ p, C p → B p) (hUB : ReflectsBoundsIn U B n)
    (hBC : ReflectsBoundsIn B C n) : ReflectsBoundsIn U C n := by
  intro c hc hd hbound
  exact hBC c hc hd (hUB c (incOn_mono hCB hc) hd hbound)

end FiniteChains.Nerve
