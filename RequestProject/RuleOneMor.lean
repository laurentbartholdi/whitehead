module

public import RequestProject.GenerationIterate
public import RequestProject.Pi2FreeGenerator

@[expose] public section

/-!
# The three moves of rule 1 as structural maps with the generation property

Rule 1 of the operation `T` of Lemma 3.9 is performed, for each extra generator `z`, in three
moves:

1. freely adjoin a new generator `b_z` (no new relator);
2. adjoin a stable letter `a_z` together with the relator `a_z b_z a_z⁻¹ = z b_z`;
3. eliminate `z` by the defining relation `z = [a_z,b_z]` (a Tietze transformation).

All three are already known in this development to satisfy the generation equation (3.3)
(`RequestProject/Pi2FreeGenerator.lean`, `RequestProject/Pi2ExtensionInjective.lean`).  This
file records each of them as a **structural map** `PresMor` of
`RequestProject/GenerationStep.lean` carrying the predicate `FiniteChains.Generates`, so that
they can be composed with each other and with rules 2 and 3.

* `FiniteChains.freeMor`, `FiniteChains.generates_freeMor` — the free adjunction;
* `FiniteChains.generates_hnnMor` — the stable-letter move, with no hypothesis except the two
  infinite-order statements which the paper verifies by killing the old group;
* `FiniteChains.generates_tietzeMor` — the Tietze move, with no hypothesis at all.
-/

namespace FiniteChains

open MonoidAlgebra

universe u

variable {α : Type u} [Fintype α] [DecidableEq α] {J : Type u} [Fintype J] [DecidableEq J]
variable (ρ : J → FreeGroup α)

/-! ### The free adjunction -/

omit [Fintype α] [Fintype J] [DecidableEq J] in
/-- The new generator does not occur in any relator, so its row of the Fox matrix
vanishes. -/
theorem foxMatrix_extFree_none (j : J) : foxMatrixPres (extFree ρ) none j = 0 := by
  have h : @fox (Option α) _ none (extFree ρ j) = 0 :=
    fox_map_of_not_mem_range Option.some (by simp) (ρ j)
  show quotRingHom ℤ (relSub (extFree ρ)) (fox none (extFree ρ j)) = 0
  rw [h, map_zero]

/-- The map on two-chains induced by the free adjunction: the coefficients are read in the
enlarged group ring. -/
noncomputable def freeCells (y : J → MonoidAlgebra ℤ (PresGroup ρ)) :
    J → MonoidAlgebra ℤ (PresGroup (extFree ρ)) := fun j => extRingHomFree ρ (y j)

omit [Fintype α] [DecidableEq J] in
theorem isFoxCycle_freeCells {y : J → MonoidAlgebra ℤ (PresGroup ρ)} (hy : IsFoxCycle ρ y) :
    IsFoxCycle (extFree ρ) (freeCells ρ y) := by
  intro io
  cases io with
  | none =>
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [foxMatrix_extFree_none, mul_zero]
  | some i =>
      have h : ∀ j : J, freeCells ρ y j * foxMatrixPres (extFree ρ) (some i) j
          = extRingHomFree ρ (y j * foxMatrixPres ρ i j) := by
        intro j
        rw [foxMatrix_extFree, freeCells, map_mul]
      rw [Finset.sum_congr rfl fun j _ => h j, ← map_sum, hy i, map_zero]

/-- **The free adjunction as a structural map.** -/
noncomputable def freeMor : PresMor ρ (extFree ρ) where
  hom := extHomFree ρ
  cells := freeCells ρ
  cells_add := fun y z => by
    funext j
    exact map_add (extRingHomFree ρ) _ _
  cells_smul := fun c y => by
    funext j
    exact map_mul (extRingHomFree ρ) c (y j)
  cells_cycle := fun _ hy => isFoxCycle_freeCells ρ hy
  cells_aug := fun y hy j => by
    rw [show freeCells ρ y j = extRingHomFree ρ (y j) from rfl, augPres_extRingHomFree, hy j]

omit [Fintype α] [DecidableEq J] in
/-- **Equation (3.3) for the free adjunction.** -/
theorem generates_freeMor : Generates (freeMor ρ) := fun _ hv => freeCycle_mem_span ρ hv

/-! ### The two one-generator, one-relator moves -/

omit [Fintype α] [DecidableEq J] in
/-- **Equation (3.3) for the Tietze move of rule 1**, with no hypothesis. -/
theorem generates_tietzeMor (s : FreeGroup α) : Generates (extMor ρ (tietzeWord s)) :=
  generates_extMor ρ _ (fun x hx => by rwa [foxNew_tietze ρ s, mul_one] at hx)
    (extHom_tietze_injective ρ s)

omit [Fintype α] [DecidableEq J] in
/-- **Equation (3.3) for the stable-letter move of rule 1.**  The two hypotheses are the
infinite-order statements which the paper checks by killing the old group. -/
theorem generates_hnnMor (u v : FreeGroup α)
    (hu : ¬ IsOfFinOrder (QuotientGroup.mk u : PresGroup ρ))
    (hv : ¬ IsOfFinOrder (QuotientGroup.mk v : PresGroup ρ)) :
    Generates (extMor ρ (hnnWord u v)) := by
  have hinj := extHom_hnn_injective ρ u v hu hv
  have hord : ¬ IsOfFinOrder (QuotientGroup.mk (FreeGroup.map Option.some v) :
      PresGroup (extRel ρ (hnnWord u v))) := by
    simpa using not_isOfFinOrder_map_of_injective hinj hv
  exact generates_extMor ρ _
    (fun x hx => mul_one_sub_single_eq_zero hord x (by rwa [foxNew_hnn ρ u v] at hx)) hinj

end FiniteChains
