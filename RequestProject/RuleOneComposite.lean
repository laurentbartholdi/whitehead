module

public import RequestProject.LemmaStructural

@[expose] public section

/-!
# Rule 1 for one extra generator, without any hypothesis

Rule 1 of the operation `T` of Lemma 3.9 replaces an extra generator `z` by a commutator
`[a_z,b_z]`.  The paper performs it in three moves: freely adjoin `b_z`, adjoin the stable
letter `a_z` with `a_z b_z a_z⁻¹ = z b_z`, and eliminate `z` through `z = [a_z,b_z]`.  The
stable-letter move requires that the two elements `b_z` and `z b_z` have infinite order, and
the paper checks this "by killing `G(P)`".

This file verifies that remark in the combinatorial model and assembles the two extension
moves into a single sequence of moves, so that rule 1 of Lemma 3.9 is available **with no
hypothesis at all**.

* `FiniteChains.not_isOfFinOrder_newGen`, `FiniteChains.not_isOfFinOrder_mul_newGen` — after
  freely adjoining `b`, both `b` and `z b` have infinite order, as seen by the homomorphism
  which kills the old generators and sends `b` to a generator of `ℤ`;
* `FiniteChains.ruleOnePath` — **rule 1 for one extra generator as a sequence of moves**, and
  `FiniteChains.generates_ruleOnePath`, `FiniteChains.isCockcroft_ruleOnePath` — equation
  (3.3) and the preservation of the Cockcroft property for it.
-/

namespace FiniteChains

open MonoidAlgebra

universe u

variable {α J : Type u} (ρ : J → FreeGroup α)

/-- The homomorphism which kills the old generators and sends the freely adjoined one to a
generator of `ℤ`. -/
def killOld : FreeGroup (Option α) →* Multiplicative ℤ :=
  FreeGroup.lift fun o : Option α =>
    match o with
    | none => Multiplicative.ofAdd (1 : ℤ)
    | some _ => 1

@[simp] theorem killOld_of_none {α : Type u} :
    killOld (FreeGroup.of (none : Option α)) = Multiplicative.ofAdd (1 : ℤ) := by
  simp [killOld]

theorem killOld_map_some {α : Type u} (w : FreeGroup α) : killOld (FreeGroup.map Option.some w) = 1 := by
  have h : (killOld (α := α)).comp (FreeGroup.map (f := Option.some)) = 1 :=
    FreeGroup.ext_hom _ _ fun i => by simp [killOld]
  exact congrArg (fun F : FreeGroup α →* Multiplicative ℤ => F w) h

/-- The homomorphism descends to the presented group of the free adjunction: the old relators
are words in the old generators. -/
def killOldPres : PresGroup (extFree ρ) →* Multiplicative ℤ :=
  QuotientGroup.lift _ killOld (by
    refine Subgroup.normalClosure_le_normal ?_
    rintro _ ⟨j, rfl⟩
    exact killOld_map_some (ρ j))

@[simp] theorem killOldPres_mk (w : FreeGroup (Option α)) :
    killOldPres ρ (QuotientGroup.mk w) = killOld w := rfl

/-- **The freely adjoined generator has infinite order.** -/
theorem not_isOfFinOrder_newGen :
    ¬ IsOfFinOrder (QuotientGroup.mk (FreeGroup.of (none : Option α)) : PresGroup (extFree ρ)) := by
  refine not_isOfFinOrder_of_map (killOldPres ρ) ?_
  rw [killOldPres_mk, killOld_of_none]
  exact not_isOfFinOrder_ofAdd_one

/-- **`z b` has infinite order** for every old word `z`: killing the old group leaves a
generator of `ℤ`. -/
theorem not_isOfFinOrder_mul_newGen (z : FreeGroup α) :
    ¬ IsOfFinOrder (QuotientGroup.mk
      (FreeGroup.map Option.some z * FreeGroup.of (none : Option α)) : PresGroup (extFree ρ)) := by
  refine not_isOfFinOrder_of_map (killOldPres ρ) ?_
  rw [killOldPres_mk, map_mul, killOld_map_some, killOld_of_none, one_mul]
  exact not_isOfFinOrder_ofAdd_one

/-! ### The two extension moves of rule 1, composed -/

variable (P : PresPoint.{u}) (z : FreeGroup P.gens)

/-- The stable letter of rule 1 conjugates `b` to `z b`. -/
abbrev ruleOneRelator : FreeGroup (Option (Option P.gens)) :=
  hnnWord (FreeGroup.of (none : Option P.gens))
    (FreeGroup.map Option.some z * FreeGroup.of (none : Option P.gens))

/-- **Rule 1 for one extra generator `z`, as a sequence of elementary moves**: freely adjoin
`b`, then adjoin the stable letter `a` with `a b a⁻¹ = z b`.  In the resulting presentation
`z = [a,b]`, which is what rule 1 achieves; no hypothesis is needed. -/
def ruleOnePath : TPath P (P.free.ext (ruleOneRelator P z)) :=
  .cons (TMove.freeGen P)
    (.cons (TMove.hnn P.free _ _ (not_isOfFinOrder_newGen P.rel)
      (not_isOfFinOrder_mul_newGen P.rel z)) (.nil _))

/-- **Equation (3.3) for rule 1**, with no hypothesis. -/
theorem generates_ruleOnePath : Generates (ruleOnePath P z).mor :=
  (ruleOnePath P z).generates

/-- **Rule 1 preserves the Cockcroft property**, with no hypothesis. -/
theorem isCockcroft_ruleOnePath (hP : IsCockcroft P.rel) :
    IsCockcroft (P.free.ext (ruleOneRelator P z)).rel :=
  (ruleOnePath P z).isCockcroft hP

end FiniteChains
