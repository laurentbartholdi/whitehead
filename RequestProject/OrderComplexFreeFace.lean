module

public import RequestProject.OrderComplexRetraction

@[expose] public section

/-! The first half of an elementary face-poset collapse: delete the free face while
retaining its unique coface. The resulting monotone retraction reflects homotopies. -/
namespace FiniteChains.Comb
variable {P : Type} [PartialOrder P]

theorem injIn_delete_free_face {C : P → Prop} {f t : P}
    (ht : C t) (hft : f ≤ t) (hne : t ≠ f)
    (hunique : ∀ x, C x → f ≤ x → x ≠ f → x = t) :
    InjIn C (fun x => C x ∧ x ≠ f) := by
  classical
  let r : {x : P // C x} → P := fun x => if x.1 = f then t else x.1
  have hr : Monotone r := by
    intro x y hxy
    by_cases hx : x.1 = f
    · by_cases hy : y.1 = f
      · simp [r, hx, hy]
      · have hyt : y.1 = t := hunique y.1 y.2 (hx ▸ hxy) hy
        simp [r, hx, hyt]
    · by_cases hy : y.1 = f
      · have hxf : x.1 ≤ f := hy ▸ hxy
        simpa [r, hx, hy] using hxf.trans hft
      · simpa [r, hx, hy] using hxy
  apply injIn_of_monotone_retraction (fun _ h => h.1) r hr
  · intro x
    by_cases hx : x.1 = f
    · simpa [r, hx] using And.intro ht hne
    · simpa [r, hx] using And.intro x.2 hx
  · intro x hx
    simp [r, hx.2]

/-- Deleting a maximal cell reflects homotopies when its remaining boundary is connected
and simply connected. The boundary is the actual strict lower face poset in the stage. -/
theorem injIn_delete_maximal {C : P → Prop} {t : P}
    (hmax : ∀ x, C x → t ≤ x → x = t)
    (hne : ∃ x, C x ∧ x < t)
    (hconn : ConnectedIn (fun x => C x ∧ x < t))
    (hsc : SimplyConnectedIn (fun x => C x ∧ x < t)) :
    InjIn C (fun x => C x ∧ x ≠ t) := by
  obtain ⟨j, hj⟩ := hne
  apply injIn_union_of_unmixed
    (B := fun x => C x ∧ x ≤ t) (J := fun x => C x ∧ x < t)
    (j0 := j) (hJconn := hconn) (hJsc := hsc) (hj0 := hj)
  · intro a b hab ha hb
    by_cases hbt : b = t
    · right
      exact ⟨⟨ha, hbt ▸ hab⟩, ⟨hb, hbt.le⟩⟩
    · left
      refine ⟨⟨ha, ?_⟩, ⟨hb, hbt⟩⟩
      intro hat
      exact hbt (hmax b hb (hat ▸ hab))
  · intro x
    constructor
    · rintro ⟨hx, hxt⟩
      exact ⟨⟨hx, hxt.ne⟩, ⟨hx, hxt.le⟩⟩
    · rintro ⟨⟨hx, hne⟩, ⟨_, hle⟩⟩
      exact ⟨hx, lt_of_le_of_ne hle hne⟩

end FiniteChains.Comb
