module

public import RequestProject.PosetCoverUpTransform

@[expose] public section

/-! Lift a comparable map from a previously chosen lift, preserving its sheet. -/
namespace FiniteChains.Comb.IsPosetCover
universe u
variable {P Q R : Type u} [PartialOrder P] [PartialOrder Q] [Preorder R]
  {f : P → Q} (hf : IsPosetCover f)

noncomputable def lowerMapLift (a : R → P) (b : R → Q)
    (hab : ∀ x, b x ≤ f (a x)) (x : R) : P :=
  Classical.choose (hf.down (a x) (b x) (hab x))

omit [Preorder R] in
theorem lowerMapLift_spec (a : R → P) (b : R → Q)
    (hab : ∀ x, b x ≤ f (a x)) (x : R) :
    hf.lowerMapLift a b hab x ≤ a x ∧ f (hf.lowerMapLift a b hab x) = b x :=
  (Classical.choose_spec (hf.down (a x) (b x) (hab x))).1

theorem lowerMapLift_monotone (a : R → P) (b : R → Q)
    (ha : Monotone a) (hb : Monotone b) (hab : ∀ x, b x ≤ f (a x)) :
    Monotone (hf.lowerMapLift a b hab) := by
  intro x y hxy
  have hx := hf.lowerMapLift_spec a b hab x
  have hy := hf.lowerMapLift_spec a b hab y
  obtain ⟨c, hxc, hcy, hfc⟩ := hf.exists_interval_lift (hx.1.trans (ha hxy)) (b y)
    (hx.2 ▸ hb hxy) (hab y)
  have he := hf.down_inj hcy hy.1 (hfc.trans hy.2.symm)
  exact he ▸ hxc

noncomputable def upperMapLift (a : R → P) (b : R → Q)
    (hab : ∀ x, f (a x) ≤ b x) (x : R) : P :=
  Classical.choose (hf.up (a x) (b x) (hab x))

omit [Preorder R] in
theorem upperMapLift_spec (a : R → P) (b : R → Q)
    (hab : ∀ x, f (a x) ≤ b x) (x : R) :
    a x ≤ hf.upperMapLift a b hab x ∧ f (hf.upperMapLift a b hab x) = b x :=
  (Classical.choose_spec (hf.up (a x) (b x) (hab x))).1

theorem upperMapLift_monotone (a : R → P) (b : R → Q)
    (ha : Monotone a) (hb : Monotone b) (hab : ∀ x, f (a x) ≤ b x) :
    Monotone (hf.upperMapLift a b hab) := by
  intro x y hxy
  have hx := hf.upperMapLift_spec a b hab x
  have hy := hf.upperMapLift_spec a b hab y
  obtain ⟨c, hxc, hcy, hfc⟩ := hf.exists_interval_lift ((ha hxy).trans hy.1) (b x)
    (hab x) (hy.2 ▸ hb hxy)
  have he := hf.up_inj hxc hx.1 (hfc.trans hx.2.symm)
  exact he ▸ hcy

/-- A constant endpoint lifts to a map constant on every comparability component. -/
theorem upperMapLift_constant_comparable (a : R → P) (ha : Monotone a)
    (b : Q) (hab : ∀ x, f (a x) ≤ b) {x y : R} (hxy : x ≤ y) :
    hf.upperMapLift a (fun _ => b) hab x = hf.upperMapLift a (fun _ => b) hab y := by
  have hx := hf.upperMapLift_spec a (fun _ => b) hab x
  have hy := hf.upperMapLift_spec a (fun _ => b) hab y
  exact hf.up_inj hx.1 ((ha hxy).trans hy.1) (hx.2.trans hy.2.symm)

include hf in
/-- Relabelling the base by an order isomorphism preserves actual interval lifting. -/
theorem postcomp_orderIso {S : Type u} [PartialOrder S] (e : Q ≃o S) :
    IsPosetCover (fun x => e (f x)) := by
  refine ⟨e.monotone.comp hf.mono, e.surjective.comp hf.surj, ?_, ?_⟩
  · intro a q h
    obtain ⟨b, hb, huniq⟩ := hf.up a (e.symm q) (by
      simpa only [e.symm_apply_apply] using e.symm.monotone h)
    refine ⟨b, ⟨hb.1, by rw [hb.2, e.apply_symm_apply]⟩, ?_⟩
    intro c hc
    exact huniq c ⟨hc.1, by simpa only [e.symm_apply_apply] using congrArg e.symm hc.2⟩
  · intro a q h
    obtain ⟨b, hb, huniq⟩ := hf.down a (e.symm q) (by
      simpa only [e.symm_apply_apply] using e.symm.monotone h)
    refine ⟨b, ⟨hb.1, by rw [hb.2, e.apply_symm_apply]⟩, ?_⟩
    intro c hc
    exact huniq c ⟨hc.1, by simpa only [e.symm_apply_apply] using congrArg e.symm hc.2⟩

end FiniteChains.Comb.IsPosetCover
