import RequestProject.PosetCoverDownTransform

/-! The two legs of a contraction lift into the same sheet of a poset cover. -/
namespace FiniteChains.Comb.IsPosetCover
universe u
variable {P Q : Type u} [PartialOrder P] [PartialOrder Q] {f : P → Q}
variable (hf : IsPosetCover f) (g : Q → Q) (hg : ∀ q, g q ≤ q)
  (b : Q) (hb : ∀ q, g q ≤ b)

/-- Lift the upper leg from the canonical lower lift, rather than independently
choosing a lift of the endpoint. -/
noncomputable def roofTransform (a : P) : P :=
  Classical.choose (hf.up (hf.downTransform g hg a) b
    ((hf.downTransform_spec g hg a).2 ▸ hb (f a)))

theorem roofTransform_spec (a : P) :
    hf.downTransform g hg a ≤ hf.roofTransform g hg b hb a ∧
      f (hf.roofTransform g hg b hb a) = b :=
  (Classical.choose_spec (hf.up (hf.downTransform g hg a) b
    ((hf.downTransform_spec g hg a).2 ▸ hb (f a)))).1

/-- Comparable vertices have exactly the same lifted endpoint. -/
theorem roofTransform_comparable_equal (hmono : Monotone g)
    {a a' : P} (haa' : a ≤ a') :
    hf.roofTransform g hg b hb a = hf.roofTransform g hg b hb a' := by
  have ha := hf.roofTransform_spec g hg b hb a
  have ha' := hf.roofTransform_spec g hg b hb a'
  exact hf.up_inj ha.1
    ((hf.downTransform_monotone g hmono hg haa').trans ha'.1)
    (ha.2.trans ha'.2.symm)

theorem roofTransform_monotone (hmono : Monotone g) :
    Monotone (hf.roofTransform g hg b hb) := by
  intro a a' haa'
  exact le_of_eq (hf.roofTransform_comparable_equal g hg b hb hmono haa')

end FiniteChains.Comb.IsPosetCover
