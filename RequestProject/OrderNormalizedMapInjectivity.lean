module

public import RequestProject.OrderNormalizationNaturality

@[expose] public section

/-! Faithfulness of actual normalized strict maps on retained vertex sets. -/
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb
universe u
variable {P Q : Type u} [PartialOrder P] [PartialOrder Q]

/-- A monotone map injective on the vertices supporting a strict two-chain reflects
zero of its actual normalized chain image. -/
theorem normalizedStrictChain2_zero_of_injOn (f : P → Q) (hf : Monotone f)
    (S : Set P) (hinj : Set.InjOn f S) (r : StrictOrdTri P →₀ ℤ)
    (hr : ∀ t ∈ r.support, t.1.1 ∈ S ∧ t.1.2.1 ∈ S ∧ t.1.2.2 ∈ S)
    (hz : normalizedStrictChain2 f hf r = 0) : r = 0 := by
  classical
  let D := {t : StrictOrdTri P // t.1.1 ∈ S ∧ t.1.2.1 ∈ S ∧ t.1.2.2 ∈ S}
  let incl : D → StrictOrdTri P := Subtype.val
  have hstrict (t : D) : f t.1.1.1 < f t.1.1.2.1 ∧ f t.1.1.2.1 < f t.1.1.2.2 := by
    constructor
    · exact lt_of_le_of_ne (hf t.1.2.1.le)
        (fun he => t.1.2.1.ne (hinj t.2.1 t.2.2.1 he))
    · exact lt_of_le_of_ne (hf t.1.2.2.le)
        (fun he => t.1.2.2.ne (hinj t.2.2.1 t.2.2.2 he))
  let image : D → StrictOrdTri Q := fun t =>
    ⟨(f t.1.1.1, f t.1.1.2.1, f t.1.1.2.2), hstrict t⟩
  have himage : Function.Injective image := by
    intro a b he
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · exact hinj a.2.1 b.2.1 (congrArg (fun t : StrictOrdTri Q => t.1.1) he)
    · apply Prod.ext
      · exact hinj a.2.2.1 b.2.2.1 (congrArg (fun t : StrictOrdTri Q => t.1.2.1) he)
      · exact hinj a.2.2.2 b.2.2.2 (congrArg (fun t : StrictOrdTri Q => t.1.2.2) he)
  let z := r.comapDomain incl Subtype.val_injective.injOn
  have hrecon : Finsupp.mapDomain incl z = r := by
    apply Finsupp.mapDomain_comapDomain _ Subtype.val_injective
    intro t ht
    exact ⟨⟨t, hr t ht⟩, rfl⟩
  have hmap (w : D →₀ ℤ) :
      normalizedStrictChain2 f hf (Finsupp.mapDomain incl w) = Finsupp.mapDomain image w := by
    induction w using Finsupp.induction_linear with
    | zero => simp
    | add w z hw hz => simp only [Finsupp.mapDomain_add, map_add, hw, hz]
    | single t n =>
        rw [Finsupp.mapDomain_single, normalizedStrictChain2_single, Finsupp.mapDomain_single]
        have hn : normalizeOrdTriangle ((orderCxMap f hf).onF ((strictOrderIncl P).onF (incl t))) =
            Finsupp.single (image t) 1 := by
          change (if h : f t.1.1.1 < f t.1.1.2.1 ∧ f t.1.1.2.1 < f t.1.1.2.2 then
            Finsupp.single (⟨(f t.1.1.1, f t.1.1.2.1, f t.1.1.2.2), h⟩ : StrictOrdTri Q) 1
            else 0) = Finsupp.single (image t) 1
          rw [dif_pos (hstrict t)]
        rw [hn]
        simp
  have hz' : Finsupp.mapDomain image z = 0 := by rw [← hmap, hrecon, hz]
  have he : z = 0 := Finsupp.mapDomain_injective himage (hz'.trans Finsupp.mapDomain_zero.symm)
  rw [← hrecon, he, Finsupp.mapDomain_zero]

end FiniteChains.Comb
