module

public import RequestProject.CockcroftKill
public import RequestProject.AsphericalChains

@[expose] public section

/-!
# The pass of `CockcroftKillStep` is not vacuous

`RequestProject/CockcroftKill.lean` reduces the extension step of Section 3 to a single
statement about Cockcroft complexes and fundamental groups
(`FiniteChains.Comb.CockcroftKillStep`).  This file checks that the data it asks for really
can occur: for the presentation complex of a finite **aspherical presentation with trivial
group** — that is, a contractible presentation complex — the pass exists, and it is the naive
one: adjoin a cancelling generator–relator pair.

* `FiniteChains.pi1Trivial_of_presGroup_subsingleton` — any cellular map into the
  presentation complex of a presentation of the trivial group kills `π₁`;
* `FiniteChains.isCockcroft_presComplex_of_aspherical` — an aspherical presentation complex is
  Cockcroft (it has no spherical classes at all);
* `FiniteChains.cockcroftKillData_of_aspherical_trivial` — the pass for such a complex;
* `FiniteChains.nonempty_cockcroftKillData_presRho` — the example `⟨x ∣ x⟩`.

This says nothing about the general case, which is the content of Lemmas 3.9 and 3.10 of the
paper; it only shows that `FiniteChains.Comb.CockcroftKillData` is an inhabited notion, so the
reduction is not vacuous.
-/

namespace FiniteChains

universe u

variable {α J : Type u}

/-! ### Maps into a presentation complex of the trivial group -/

/-- **A cellular map into the presentation complex of a presentation of the trivial group
kills `π₁`.**  The fundamental group of the presentation complex is the presented group
(`FiniteChains.Comb.pi1PresEquiv`), so every edge loop of the target is null-homotopic. -/
theorem pi1Trivial_of_presGroup_subsingleton {X : Comb.Complex2.{u}} {β Kc : Type u}
    [DecidableEq β] {σ : Kc → FreeGroup β} (hσ : Subsingleton (PresGroup σ))
    (h : Comb.Hom X (Comb.presComplex σ)) : Comb.Pi1Trivial h := by
  intro a m _
  haveI : Subsingleton (Comb.Pi1 (Comb.presComplex σ) PUnit.unit) :=
    Equiv.subsingleton (Comb.pi1PresEquiv σ).toEquiv
  have hcl : Comb.loopClass σ (Comb.mapPath h m) = 1 := Subsingleton.elim _ _
  exact Quotient.exact hcl

/-! ### An aspherical presentation complex is Cockcroft -/

/-- An aspherical presentation complex has no spherical classes, hence is Cockcroft. -/
theorem isCockcroft_presComplex_of_aspherical {β Kc : Type u} [Fintype β] [DecidableEq β]
    [Fintype Kc] [DecidableEq Kc] {σ : Kc → FreeGroup β} (hσ : Aspherical σ) :
    Comb.IsCockcroft (Comb.presComplex σ) := by
  intro x₀ c hc
  have hzero : c = 0 := pi2Trivial_presComplex_of_aspherical hσ x₀ c hc
  rw [hzero, map_zero]

/-! ### The pass for a contractible presentation complex -/

variable [Fintype α] [DecidableEq α] [Fintype J] [DecidableEq J]

/-- **The pass of `FiniteChains.Comb.CockcroftKillStep` for the presentation complex of a
finite aspherical presentation of the trivial group.**  Adjoining a cancelling
generator–relator pair keeps the presentation aspherical
(`FiniteChains.aspherical_iterCancel`) and does not change the group
(`FiniteChains.extHom_cancel_surjective`), so the enlarged complex is again Cockcroft and the
fundamental group of the source dies in it (it is trivial to begin with).  One edge and one
two-cell are added. -/
noncomputable def cockcroftKillData_of_aspherical_trivial {ρ : J → FreeGroup α}
    (hρ : Aspherical ρ) (htriv : Subsingleton (PresGroup ρ)) :
    Comb.CockcroftKillData (Comb.presComplex ρ) where
  next := Comb.presComplex (iterCancel ρ 1)
  hom := iterCancelInc ρ 0
  injV := fun _ _ _ => Subsingleton.elim (α := PUnit.{u + 1}) _ _
  injE := Option.some_injective _
  injF := Option.some_injective _
  conn := isConnected_presComplex_aspherical _
  cock := isCockcroft_presComplex_of_aspherical (aspherical_iterCancel hρ 1)
  kill := by
    refine pi1Trivial_of_presGroup_subsingleton ?_ _
    refine ⟨fun x y => ?_⟩
    obtain ⟨x', rfl⟩ := extHom_cancel_surjective ρ x
    obtain ⟨y', rfl⟩ := extHom_cancel_surjective ρ y
    rw [Subsingleton.elim x' y']
  finE := Subtype.finite
  finF := Subtype.finite
  adds := ⟨⟨none, fun _ h => Option.some_ne_none _ h⟩⟩

/-- The presentation `⟨x ∣ x⟩` presents the trivial group: its single relator is the single
generator, so the relator subgroup is everything. -/
theorem subsingleton_presGroup_presRho : Subsingleton (PresGroup presRho) := by
  have hmem : ∀ w : FreeGroup Unit, w ∈ relSub presRho := by
    intro w
    refine FreeGroup.induction_on w (one_mem _) (fun x => ?_) (fun x hx => inv_mem hx)
      (fun x y hx hy => mul_mem hx hy)
    exact Subgroup.subset_normalClosure ⟨(), by cases x; rfl⟩
  refine ⟨fun x y => ?_⟩
  induction x using QuotientGroup.induction_on with
  | _ a =>
    induction y using QuotientGroup.induction_on with
    | _ b => exact QuotientGroup.eq.2 (hmem _)

/-- **The notion is inhabited**: the presentation `⟨x ∣ x⟩` of the trivial group is aspherical
and its complex admits the pass. -/
theorem nonempty_cockcroftKillData_presRho :
    Nonempty (Comb.CockcroftKillData (Comb.presComplex presRho)) :=
  ⟨cockcroftKillData_of_aspherical_trivial aspherical_presRho subsingleton_presGroup_presRho⟩

end FiniteChains
