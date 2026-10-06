module

public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Topology.Maps.Basic

@[expose] public section

/-! Two quotient maps with exactly the same fibers identify their targets by
an actual homeomorphism. Its value on every quotient representative is fixed. -/

noncomputable section
namespace FiniteChains
open Topology

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (f : X → Y) (g : X → Z) (hf : IsQuotientMap f) (hg : IsQuotientMap g)
    (hfg : ∀ a b, f a = f b ↔ g a = g b)

def sameFiberForward (y : Y) : Z := g (hf.surjective y).choose

include hfg in
omit [TopologicalSpace Z] in
theorem sameFiberForward_apply (x : X) :
    sameFiberForward f g hf (f x) = g x :=
  (hfg _ _).mp (hf.surjective (f x)).choose_spec

def quotientSameFibersHomeomorph : Y ≃ₜ Z where
  toFun := sameFiberForward f g hf
  invFun := sameFiberForward g f hg
  left_inv y := by
    obtain ⟨x, rfl⟩ := hf.surjective y
    rw [sameFiberForward_apply f g hf hfg]
    exact sameFiberForward_apply g f hg (fun a b => (hfg a b).symm) x
  right_inv z := by
    obtain ⟨x, rfl⟩ := hg.surjective z
    rw [sameFiberForward_apply g f hg (fun a b => (hfg a b).symm)]
    exact sameFiberForward_apply f g hf hfg x
  continuous_toFun := by
    apply hf.continuous_iff.mpr
    have he : sameFiberForward f g hf ∘ f = g :=
      funext (sameFiberForward_apply f g hf hfg)
    rw [he]
    exact hg.continuous
  continuous_invFun := by
    apply hg.continuous_iff.mpr
    have he : sameFiberForward g f hg ∘ g = f :=
      funext (sameFiberForward_apply g f hg (fun a b => (hfg a b).symm))
    rw [he]
    exact hf.continuous

@[simp] theorem quotientSameFibersHomeomorph_apply (x : X) :
    quotientSameFibersHomeomorph f g hf hg hfg (f x) = g x :=
  sameFiberForward_apply f g hf hfg x

end FiniteChains
