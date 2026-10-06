import RequestProject.PosetCoverDownTransform

namespace FiniteChains.Comb
universe u
variable {P Q : Type u} [PartialOrder P] [PartialOrder Q] {f : P → Q}
namespace IsPosetCover
variable (hf : IsPosetCover f)
include hf

/-- Canonical lift of an upward order homotopy through an actual poset cover. -/
noncomputable def upTransform (g : Q → Q) (hg : ∀ q, q ≤ g q) (a : P) : P :=
  Classical.choose (hf.up a (g (f a)) (hg (f a)))

theorem upTransform_spec (g : Q → Q) (hg : ∀ q, q ≤ g q) (a : P) :
    a ≤ hf.upTransform g hg a ∧ f (hf.upTransform g hg a) = g (f a) :=
  (Classical.choose_spec (hf.up a (g (f a)) (hg (f a)))).1

theorem upTransform_monotone (g : Q → Q) (hm : Monotone g) (hg : ∀ q, q ≤ g q) :
    Monotone (hf.upTransform g hg) := by
  intro a b hab
  obtain ⟨c, hac, hcb, hfc⟩ := hf.exists_interval_lift
    (hab.trans (hf.upTransform_spec g hg b).1) (g (f a)) (hg (f a))
    (by rw [(hf.upTransform_spec g hg b).2]; exact hm (hf.mono hab))
  have hc : c = hf.upTransform g hg a := hf.up_inj hac
    (hf.upTransform_spec g hg a).1 (hfc.trans (hf.upTransform_spec g hg a).2.symm)
  exact hc ▸ hcb

theorem le_upTransform (g : Q → Q) (hg : ∀ q, q ≤ g q) (a : P) :
    a ≤ hf.upTransform g hg a := (hf.upTransform_spec g hg a).1

theorem upTransform_fixed (g : Q → Q) (hg : ∀ q, q ≤ g q) (a : P)
    (ha : g (f a) = f a) : hf.upTransform g hg a = a :=
  hf.up_inj (hf.le_upTransform g hg a) (le_refl a)
    ((hf.upTransform_spec g hg a).2.trans ha)

theorem strictMono : StrictMono f := by
  intro a b h
  apply lt_of_le_of_ne (hf.mono h.le)
  intro he
  have hb : b = a := hf.up_inj h.le (le_refl a) he.symm
  exact (ne_of_lt h) hb.symm

end IsPosetCover
end FiniteChains.Comb
