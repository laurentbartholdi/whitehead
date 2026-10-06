module

public import RequestProject.TopologicalSingular.SingularChainHomotopy

@[expose] public section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.TopologicalSingular
open CategoryTheory
universe u

noncomputable def shortComplexCycleClass (S : ShortComplex (ModuleCat.{u} ℤ))
    (c : S.X₂) (hc : S.g c = 0) : S.homology :=
  S.homologyπ (S.moduleCatCyclesIso.inv ⟨c, hc⟩)

theorem shortComplexCycleClass_i (S : ShortComplex (ModuleCat.{u} ℤ))
    (c : S.X₂) (hc : S.g c = 0) :
    S.homologyι (shortComplexCycleClass S c hc) = S.pOpcycles c := by
  have he := congrArg (fun f => f (S.moduleCatCyclesIso.inv ⟨c, hc⟩)) S.homology_π_ι
  change S.homologyι (shortComplexCycleClass S c hc) =
    S.pOpcycles (S.iCycles (S.moduleCatCyclesIso.inv ⟨c, hc⟩)) at he
  have hi : S.iCycles (S.moduleCatCyclesIso.inv ⟨c, hc⟩) = c :=
    congrArg (fun f => f ⟨c, hc⟩) S.moduleCatCyclesIso_inv_iCycles
  rwa [hi] at he

theorem shortComplexCycleClass_eq_iff (S : ShortComplex (ModuleCat.{u} ℤ))
    (c d : S.X₂) (hc : S.g c = 0) (hd : S.g d = 0) :
    shortComplexCycleClass S c hc = shortComplexCycleClass S d hd ↔
      c - d ∈ LinearMap.range S.f.hom := by
  constructor
  · intro h
    apply (S.moduleCat_pOpcycles_eq_iff c d).mp
    simpa only [shortComplexCycleClass_i] using congrArg S.homologyι h
  · intro h
    apply (ModuleCat.mono_iff_injective S.homologyι).mp inferInstance
    rw [shortComplexCycleClass_i, shortComplexCycleClass_i]
    exact (S.moduleCat_pOpcycles_eq_iff c d).mpr h

theorem shortComplexCycleClass_zero (S : ShortComplex (ModuleCat.{u} ℤ)) :
    shortComplexCycleClass S 0 (map_zero S.g.hom) = 0 := by
  apply (ModuleCat.mono_iff_injective S.homologyι).mp inferInstance
  rw [shortComplexCycleClass_i, map_zero, map_zero]

theorem shortComplexCycleClass_add (S : ShortComplex (ModuleCat.{u} ℤ))
    (c d : S.X₂) (hc : S.g c = 0) (hd : S.g d = 0) :
    shortComplexCycleClass S (c + d) (by rw [map_add, hc, hd, add_zero]) =
      shortComplexCycleClass S c hc + shortComplexCycleClass S d hd := by
  apply (ModuleCat.mono_iff_injective S.homologyι).mp inferInstance
  simp only [map_add, shortComplexCycleClass_i]

theorem shortComplexCycleClass_natural {S T : ShortComplex (ModuleCat.{u} ℤ)}
    (φ : S ⟶ T) (c : S.X₂) (hc : S.g c = 0) (ht : T.g (φ.τ₂ c) = 0) :
    (ShortComplex.homologyMap φ) (shortComplexCycleClass S c hc) =
      shortComplexCycleClass T (φ.τ₂ c) ht := by
  apply (ModuleCat.mono_iff_injective T.homologyι).mp inferInstance
  rw [shortComplexCycleClass_i]
  have he := congrArg (fun f => f (S.moduleCatCyclesIso.inv ⟨c, hc⟩))
    (ShortComplex.π_homologyMap_ι φ)
  change T.homologyι ((ShortComplex.homologyMap φ) (shortComplexCycleClass S c hc)) =
    T.pOpcycles (φ.τ₂ (S.iCycles (S.moduleCatCyclesIso.inv ⟨c, hc⟩))) at he
  have hi : S.iCycles (S.moduleCatCyclesIso.inv ⟨c, hc⟩) = c :=
    congrArg (fun f => f ⟨c, hc⟩) S.moduleCatCyclesIso_inv_iCycles
  rwa [hi] at he

variable {X : Type u} [TopologicalSpace X]

theorem singularCycle_condition (n : ℕ) {c : Chain X (n + 1)} (hc : boundary n c = 0) :
    ((complex X).sc (n + 1)).g c = 0 := by
  change (complex X).d (n + 1) ((ComplexShape.down ℕ).next (n + 1)) c = 0
  rw [ChainComplex.next_nat_succ, complex_d]
  exact hc

/-- The actual Mathlib homology class of an explicit positive-degree cycle. -/
noncomputable def singularCycleClass (n : ℕ) (c : Chain X (n + 1)) (hc : boundary n c = 0) :
    (complex X).homology (n + 1) :=
  shortComplexCycleClass ((complex X).sc (n + 1)) c (singularCycle_condition n hc)

theorem singularCycleClass_eq_iff (n : ℕ) (c d : Chain X (n + 1))
    (hc : boundary n c = 0) (hd : boundary n d = 0) :
    singularCycleClass n c hc = singularCycleClass n d hd ↔
      c - d ∈ LinearMap.range (boundary (n + 1)) := by
  rw [singularCycleClass, singularCycleClass, shortComplexCycleClass_eq_iff]
  change c - d ∈ LinearMap.range
    ((complex X).d ((ComplexShape.down ℕ).prev (n + 1)) (n + 1)).hom ↔ _
  rw [ChainComplex.prev, complex_d]
  rfl

theorem singularCycleClass_zero (n : ℕ) : singularCycleClass (X := X) n 0 (map_zero _) = 0 :=
  shortComplexCycleClass_zero _

theorem singularCycleClass_add (n : ℕ) (c d : Chain X (n + 1))
    (hc : boundary n c = 0) (hd : boundary n d = 0) :
    singularCycleClass n (c + d) (by rw [map_add, hc, hd, add_zero]) =
      singularCycleClass n c hc + singularCycleClass n d hd :=
  shortComplexCycleClass_add _ _ _ _ _

theorem singularCycleClass_natural {Y : Type u} [TopologicalSpace Y] (f : C(X, Y))
    (n : ℕ) (c : Chain X (n + 1)) (hc : boundary n c = 0) :
    (HomologicalComplex.homologyMap (chainMap f) (n + 1)) (singularCycleClass n c hc) =
      singularCycleClass n (map f (n + 1) c) (by rw [← map_boundary, hc, map_zero]) := by
  exact shortComplexCycleClass_natural
    ((HomologicalComplex.shortComplexFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) (n + 1)).map
      (chainMap f)) c (singularCycle_condition n hc) _

end FiniteChains.TopologicalSingular
