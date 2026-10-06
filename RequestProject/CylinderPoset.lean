module

public import RequestProject.NerveSupport

@[expose] public section

/-!
# The combinatorial mapping cylinder of a map of posets, with its outer end

This file defines the **modified chamber** directly as the mapping cylinder of a monotone map
`a : Σ →o X`, with the copy of `Σ` singled out as the *outer end* — the end on which the mirrors
sit — and proves, at chain level, what the gluing argument needs from it: the cylinder
deformation-retracts onto its copy of `X`, so a cylinder piece contributes only the images of
the cycles of that copy.

* `FiniteChains.Comb.CylP a` — the poset `X ⊕ Σ` with `s ≤ x` iff `a s ≤ x`; its order complex
  is the mapping cylinder of the map of order complexes induced by `a`;
* `FiniteChains.Comb.cylIn`, `FiniteChains.Comb.cylOuter` — the two inclusions (base and outer
  end), both monotone and injective;
* `FiniteChains.Comb.cylRetr` — the retraction `Sum.elim id a`, monotone, with
  `cylRetr ∘ cylIn = id` and `cylRetr ∘ cylOuter = a`;
* `FiniteChains.Comb.le_cylIn_cylRetr` — `p ≤ ι (r p)` for every `p`: the identity is below the
  retraction, which is exactly what makes the prism operator of
  `RequestProject/NervePrism.lean` a chain homotopy between them;
* `FiniteChains.Comb.cylPrism_identity` — `∂ P + P ∂ = (ι r)_* − id`;
* `FiniteChains.Comb.cycle_sub_retract_eq_bdry` and
  `FiniteChains.Comb.exists_cycle_on_base_of_cycle` — **every cycle of the cylinder differs by a
  boundary from a cycle supported on the base copy of `X`**, and that cycle is the image of the
  original one under the retraction.

Only the outer end is *not* collapsed: `cylOuter` is injective and the subcomplex it spans is
where the gluing to the rest of the object happens.  Nothing here constructs a covering or
computes `π₁`.
-/

namespace FiniteChains
namespace Comb

universe u

open Nerve

variable {X Sg : Type u} [Preorder X] [Preorder Sg]

/-- The poset underlying the mapping cylinder of a monotone map `a : Σ →o X`. -/
def CylP (_a : Sg →o X) : Type u := X ⊕ Sg

namespace CylP

variable (a : Sg →o X)

/-- The order of the mapping cylinder: the two ends keep their own orders, and an element of the
outer end lies below the elements of `X` above its image. -/
protected def le : CylP a → CylP a → Prop
  | Sum.inl x, Sum.inl y => x ≤ y
  | Sum.inl _, Sum.inr _ => False
  | Sum.inr s, Sum.inl y => a s ≤ y
  | Sum.inr s, Sum.inr t => s ≤ t

instance : Preorder (CylP a) where
  le := CylP.le a
  le_refl p := by
    cases p with
    | inl x => exact le_refl x
    | inr s => exact le_refl s
  le_trans p q r hpq hqr := by
    cases p with
    | inl x =>
        cases q with
        | inl y =>
            cases r with
            | inl z => exact le_trans hpq hqr
            | inr t => exact hqr.elim
        | inr t => exact hpq.elim
    | inr s =>
        cases q with
        | inl y =>
            cases r with
            | inl z => exact le_trans hpq hqr
            | inr t => exact hqr.elim
        | inr t =>
            cases r with
            | inl z => exact le_trans (a.monotone hpq) hqr
            | inr u => exact le_trans hpq hqr

end CylP

variable (a : Sg →o X)

/-- The inclusion of the base. -/
def cylIn (x : X) : CylP a := Sum.inl x

/-- The inclusion of the **outer end**. -/
def cylOuter (s : Sg) : CylP a := Sum.inr s

/-- The retraction of the cylinder onto its base. -/
def cylRetr : CylP a → X := Sum.elim id a

@[simp] theorem cylRetr_cylIn (x : X) : cylRetr a (cylIn a x) = x := rfl

@[simp] theorem cylRetr_cylOuter (s : Sg) : cylRetr a (cylOuter a s) = a s := rfl

theorem cylIn_injective : Function.Injective (cylIn a) := fun _ _ h => Sum.inl_injective h

/-- The outer end is retained: its inclusion is injective. -/
theorem cylOuter_injective : Function.Injective (cylOuter a) := fun _ _ h => Sum.inr_injective h

theorem cylIn_monotone : Monotone (cylIn a) := fun _ _ h => h

theorem cylOuter_monotone : Monotone (cylOuter a) := fun _ _ h => h

theorem cylRetr_monotone : Monotone (cylRetr a) := by
  intro p q hpq
  cases p with
  | inl x =>
      cases q with
      | inl y => exact hpq
      | inr t => exact hpq.elim
  | inr s =>
      cases q with
      | inl y => exact hpq
      | inr t => exact a.monotone hpq

/-- The composite `ι ∘ r`, the "collapse the cylinder onto its base" map. -/
def cylCollapse : CylP a → CylP a := fun p => cylIn a (cylRetr a p)

theorem cylCollapse_monotone : Monotone (cylCollapse a) :=
  (cylIn_monotone a).comp (cylRetr_monotone a)

/-- The identity lies below the collapse: this is what makes the prism operator a chain
homotopy between them. -/
theorem le_cylIn_cylRetr (p : CylP a) : p ≤ cylCollapse a p := by
  cases p with
  | inl x => exact le_refl x
  | inr s => exact le_refl (a s)

/-! ### The chain homotopy -/

/-- **The cylinder deformation-retracts onto its base, at chain level**:
`∂ P + P ∂ = (ι r)_* − id`. -/
theorem cylPrism_identity (z : Ch (CylP a)) :
    bdry (prism id (cylCollapse a) z) + prism id (cylCollapse a) (bdry z) =
      cmap (cylCollapse a) z - z := by
  have := bdry_prism_add_prism_bdry (P := CylP a) id (cylCollapse a) z
  simpa using this

theorem prism_mem_inc_cyl {z : Ch (CylP a)} (hz : z ∈ Inc (CylP a)) :
    prism id (cylCollapse a) z ∈ Inc (CylP a) :=
  prism_mem_inc monotone_id (cylCollapse_monotone a) (le_cylIn_cylRetr a) hz

/-- **Every cycle of the cylinder differs by a boundary from its image under the retraction.** -/
theorem cycle_sub_retract_eq_bdry {z : Ch (CylP a)} (hz : z ∈ Inc (CylP a))
    (hcyc : bdry z = 0) :
    ∃ y ∈ Inc (CylP a), cmap (cylCollapse a) z - z = bdry y := by
  refine ⟨prism id (cylCollapse a) z, prism_mem_inc_cyl a hz, ?_⟩
  have h := cylPrism_identity a z
  rw [hcyc, map_zero, add_zero] at h
  exact h.symm

/-- The image of a chain under the collapse is supported on the base copy of `X`. -/
theorem cmap_cylCollapse_mem_incOn {z : Ch (CylP a)} (hz : z ∈ Inc (CylP a)) :
    cmap (cylCollapse a) z ∈ IncOn (fun p : CylP a => ∃ x : X, p = cylIn a x) := by
  refine AddSubgroup.closure_induction
    (p := fun y _ => cmap (cylCollapse a) y ∈
      IncOn (fun p : CylP a => ∃ x : X, p = cylIn a x)) ?_ ?_ ?_ ?_ hz
  · rintro y ⟨l, hl, rfl⟩
    rw [cmap_of]
    refine of_mem_incOn
      (List.isChain_map_of_isChain _ (fun _ _ h => cylCollapse_monotone a h) hl) ?_
    intro p hp
    obtain ⟨q, -, rfl⟩ := List.mem_map.1 hp
    exact ⟨cylRetr a q, rfl⟩
  · simp
  · intro y w _ _ hy hw
    simpa using AddSubgroup.add_mem _ hy hw
  · intro y _ hy
    simpa using AddSubgroup.neg_mem _ hy

/-- **A cylinder piece contributes only the images of the cycles of its copy of the base.**
Every cycle of the cylinder is, up to a boundary, a cycle supported on the base copy of `X`. -/
theorem exists_cycle_on_base_of_cycle {z : Ch (CylP a)} (hz : z ∈ Inc (CylP a))
    (hcyc : bdry z = 0) :
    ∃ w ∈ IncOn (fun p : CylP a => ∃ x : X, p = cylIn a x), ∃ y ∈ Inc (CylP a),
      bdry w = 0 ∧ z = w - bdry y := by
  refine ⟨cmap (cylCollapse a) z, cmap_cylCollapse_mem_incOn a hz, ?_⟩
  obtain ⟨y, hy, hbdy⟩ := cycle_sub_retract_eq_bdry a hz hcyc
  refine ⟨y, hy, ?_, ?_⟩
  · rw [← cmap_bdry, hcyc, map_zero]
  · rw [← hbdy]
    abel

end Comb
end FiniteChains
