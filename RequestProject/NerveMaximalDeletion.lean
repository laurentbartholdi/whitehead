import RequestProject.NerveBoundaryReflection

/-! Both homology comparisons for deleting a maximal cell, with explicit finite chains. -/
namespace FiniteChains.Nerve
universe u
variable {P : Type u} [PartialOrder P]

private theorem maximalDeletion_unmixed {C : P → Prop} {t : P}
    (hmax : ∀ x, C x → t ≤ x → x = t) :
    ∀ a b : P, a ≤ b → C a → C b →
      ((C a ∧ a ≠ t) ∧ (C b ∧ b ≠ t)) ∨ ((C a ∧ a ≤ t) ∧ (C b ∧ b ≤ t)) := by
  intro a b hab ha hb
  by_cases hbt : b = t
  · exact Or.inr ⟨⟨ha, hbt ▸ hab⟩, ⟨hb, hbt.le⟩⟩
  · refine Or.inl ⟨⟨ha, ?_⟩, ⟨hb, hbt⟩⟩
    intro hat
    exact hbt (hmax b hb (hat ▸ hab))

/-- A filling of a cycle avoiding the top cell can be chosen to avoid it as well. -/
theorem reflectsBoundsIn_delete_maximal {C : P → Prop} {t : P} {n : ℕ}
    (hmax : ∀ x, C x → t ≤ x → x = t)
    (hJ : FillsDegreeIn (fun x => C x ∧ x < t) n) :
    ReflectsBoundsIn C (fun x => C x ∧ x ≠ t) n := by
  apply reflectsBoundsIn_union_of_unmixed (maximalDeletion_unmixed hmax)
  apply fillsDegreeIn_congr (A := fun x => C x ∧ x < t) _ hJ
  intro x
  constructor
  · rintro ⟨hx, hxt⟩
    exact ⟨⟨hx, hxt.ne⟩, ⟨hx, hxt.le⟩⟩
  · rintro ⟨⟨hx, hne⟩, ⟨_, hle⟩⟩
    exact ⟨hx, lt_of_le_of_ne hle hne⟩

/-- Every cycle can be moved off the maximal cell by a finite boundary when
the punctured lower link fills cycles one degree lower. -/
theorem generatesDegreeIn_delete_maximal {C : P → Prop} {t : P} {n : ℕ}
    (ht : C t) (hmax : ∀ x, C x → t ≤ x → x = t)
    (hJ : FillsDegreeIn (fun x => C x ∧ x < t) n) :
    GeneratesDegreeIn C (fun x => C x ∧ x ≠ t) (n + 1) := by
  have hcone : AcyclicIn (fun x => C x ∧ x ≤ t) := by
    let b : {x : P // C x ∧ x ≤ t} := ⟨t, ht, le_refl _⟩
    apply acyclicIn_of_subtype (fun x => C x ∧ x ≤ t) ⟨t, ht, le_refl _⟩
    intro c hc hd
    exact exists_bdry_eq_of_cycle id b monotone_id (fun _ => le_refl _)
      (fun x => x.2.2) hc hd
  apply generatesDegreeIn_union_of_unmixed
    (B := fun x => C x ∧ x ≤ t)
    (fun x => ⟨fun hx => by
      by_cases he : x = t
      · exact Or.inr ⟨hx, he.le⟩
      · exact Or.inl ⟨hx, he⟩,
      fun h => h.elim (fun h => h.1) (fun h => h.1)⟩)
    (maximalDeletion_unmixed hmax)
  · intro c hc _ hd
    exact ⟨c, hc, 0, AddSubgroup.zero_mem _, hd, by simp⟩
  · exact generatesDegreeIn_of_acyclicRelIn (acyclicRelIn_of_acyclicIn hcone)
  · apply fillsDegreeIn_congr (A := fun x => C x ∧ x < t) _ hJ
    intro x
    constructor
    · rintro ⟨hx, hxt⟩
      exact ⟨⟨hx, hxt.ne⟩, ⟨hx, hxt.le⟩⟩
    · rintro ⟨⟨hx, hne⟩, ⟨_, hle⟩⟩
      exact ⟨hx, lt_of_le_of_ne hle hne⟩

end FiniteChains.Nerve
