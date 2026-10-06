module

public import RequestProject.RuleOneMor

@[expose] public section

/-!
# The elimination move of rule 1

The third move of rule 1 of the operation `T` of Lemma 3.9 *removes* the extra generator `z`
by its defining relation `z = [a_z,b_z]`.  In the language of presentations this is the
inverse of the Tietze extension `FiniteChains.extMor ρ (tietzeWord s)`: the presentation
`⟨x, z | r, z = s⟩` collapses back to `⟨x | r⟩`.

This file builds that move as a structural map and proves the generation equation (3.3) for
it.  The argument is the one-line argument for an invertible move: the elimination is a
two-sided inverse of the extension on two-chains, so every Fox cycle downstairs is the image
of a Fox cycle upstairs.

* `FiniteChains.Generates.of_cells_leftInverse` — a structural map which has a structural
  section on two-chains satisfies (3.3);
* `FiniteChains.elimMor` — the elimination move;
* `FiniteChains.generates_elimMor` — **equation (3.3) for the elimination move**.
-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains

open MonoidAlgebra

universe u

section General

variable {α J α' J' : Type u} [DecidableEq α] [Fintype J] [DecidableEq α'] [Fintype J']
  {ρ : J → FreeGroup α} {ρ' : J' → FreeGroup α'}

/-- **An invertible move satisfies (3.3).**  If `g : P' → P` has a structural section
`f : P → P'` on two-chains, then every Fox cycle of `P` is the image under `g` of a Fox cycle
of `P'`, namely of the image of the cycle under `f`. -/
theorem Generates.of_cells_leftInverse (f : PresMor ρ ρ') (g : PresMor ρ' ρ)
    (h : ∀ y, g.cells (f.cells y) = y) : Generates g := by
  intro v hv
  exact Submodule.subset_span ⟨f.cells v, f.cells_cycle v hv, (h v).symm⟩

end General

variable {α : Type u} [Fintype α] [DecidableEq α] {J : Type u} [Fintype J] [DecidableEq J]
variable (ρ : J → FreeGroup α) (s : FreeGroup α)

/-- The map of group rings induced by the retraction which eliminates the new generator. -/
noncomputable def tietzeRetractRing :
    MonoidAlgebra ℤ (PresGroup (extRel ρ (tietzeWord s))) →+* MonoidAlgebra ℤ (PresGroup ρ) :=
  MonoidAlgebra.mapDomainRingHom ℤ (tietzeRetract ρ s)

omit [Fintype α] [DecidableEq α] [Fintype J] [DecidableEq J] in
/-- The retraction undoes the extension on group rings. -/
theorem tietzeRetractRing_extRingHom (x : MonoidAlgebra ℤ (PresGroup ρ)) :
    tietzeRetractRing ρ s (extRingHom ρ (tietzeWord s) x) = x := by
  show MonoidAlgebra.mapDomain (tietzeRetract ρ s)
      (MonoidAlgebra.mapDomain (extHom ρ (tietzeWord s)) x) = x
  rw [← MonoidAlgebra.mapDomain_comp]
  have h : (⇑(tietzeRetract ρ s) ∘ ⇑(extHom ρ (tietzeWord s))) = id := by
    funext g
    induction g using QuotientGroup.induction_on with
    | H w =>
        show tietzeRetract ρ s (QuotientGroup.mk (FreeGroup.map Option.some w)) = _
        show (QuotientGroup.mk (tietzeLift s (FreeGroup.map Option.some w)) : PresGroup ρ) = _
        rw [tietzeLift_map_some]
        rfl
  rw [h, MonoidAlgebra.mapDomain_id]

/-- The map on two-chains of the elimination move: the coefficient of the new two-cell is
dropped and the others are read in the old group ring. -/
noncomputable def elimCells (v : Option J → MonoidAlgebra ℤ (PresGroup (extRel ρ (tietzeWord s)))) :
    J → MonoidAlgebra ℤ (PresGroup ρ) := fun j => tietzeRetractRing ρ s (v (some j))

omit [Fintype α] [DecidableEq J] in
theorem isFoxCycle_elimCells {v : Option J → MonoidAlgebra ℤ (PresGroup (extRel ρ (tietzeWord s)))}
    (hv : IsFoxCycle (extRel ρ (tietzeWord s)) v) : IsFoxCycle ρ (elimCells ρ s v) := by
  obtain ⟨-, hold⟩ := extCycle_tietze ρ s hv
  intro i
  have h := congrArg (tietzeRetractRing ρ s) (hold i)
  rw [map_sum, map_zero] at h
  rw [← h]
  exact Finset.sum_congr rfl fun j _ => by
    rw [map_mul, tietzeRetractRing_extRingHom]
    rfl

/-- **The elimination move of rule 1 as a structural map.** -/
noncomputable def elimMor : PresMor (extRel ρ (tietzeWord s)) ρ where
  hom := tietzeRetract ρ s
  cells := elimCells ρ s
  cells_add := fun v w => by
    funext j
    exact map_add (tietzeRetractRing ρ s) _ _
  cells_smul := fun c v => by
    funext j
    exact map_mul (tietzeRetractRing ρ s) c (v (some j))
  cells_cycle := fun _ hv => isFoxCycle_elimCells ρ s hv
  cells_aug := fun v hv j => by
    have haug : ∀ x : MonoidAlgebra ℤ (PresGroup (extRel ρ (tietzeWord s))),
        augPres ρ (tietzeRetractRing ρ s x) = augPres (extRel ρ (tietzeWord s)) x :=
      fun x => augQ_mapDomain (tietzeRetract ρ s) x
    show augPres ρ (tietzeRetractRing ρ s (v (some j))) = 0
    rw [haug, hv (some j)]

omit [Fintype α] [DecidableEq J] in
/-- **Equation (3.3) for the elimination move**, with no hypothesis: the elimination inverts
the Tietze extension on two-chains. -/
theorem generates_elimMor : Generates (elimMor ρ s) := by
  refine Generates.of_cells_leftInverse (extMor ρ (tietzeWord s)) (elimMor ρ s) fun y => ?_
  funext j
  show tietzeRetractRing ρ s (extCycleImage ρ (tietzeWord s) y (some j)) = y j
  show tietzeRetractRing ρ s (extRingHom ρ (tietzeWord s) (y j)) = y j
  rw [tietzeRetractRing_extRingHom]

end FiniteChains
