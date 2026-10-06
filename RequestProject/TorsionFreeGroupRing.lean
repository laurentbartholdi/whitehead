import Mathlib

/-!
# Group rings of torsion-free abelian groups are integral domains

Lemma 2.1 of the paper is applied with `H ◁ Q` torsion-free abelian; its proof
uses that the coefficient ring `k[H]` is an integral domain.  This file proves
that statement in Lean, with no finiteness assumption on `H`:

* a torsion-free abelian group has the `UniqueSums` (resp. `UniqueProds`)
  property, because every pair of finite subsets lives in a finitely generated
  subgroup, which is free abelian of finite rank, hence orderable
  (`FiniteChains.uniqueSums_of_isAddTorsionFree`,
  `FiniteChains.uniqueProds_of_isMulTorsionFree`);
* consequently `k[H]` has no zero divisors and is an integral domain for any
  integral domain `k` (`FiniteChains.monoidAlgebra_isDomain`), in particular for
  `k = ℤ` and `k = 𝔽ₚ`, the two cases used in the paper.
-/

namespace FiniteChains

open scoped Classical in
/-- **A torsion-free abelian group has unique sums.**  Two nonempty finite subsets always
contain a pair whose sum is achieved only once. -/
theorem uniqueSums_of_isAddTorsionFree (A : Type*) [AddCommGroup A] [IsAddTorsionFree A] :
    UniqueSums A := by
  constructor
  intro S T hS hT
  -- the finitely generated subgroup containing both finite sets
  set G : AddSubgroup A := AddSubgroup.closure ((S ∪ T : Finset A) : Set A) with hG
  haveI : AddGroup.FG G := by
    rw [hG]; exact AddGroup.closure_finset_fg (S ∪ T)
  haveI : Module.Finite ℤ G := inferInstance
  haveI : IsAddTorsionFree G := Function.Injective.isAddTorsionFree
    (f := (AddSubgroup.subtype G)) Subtype.val_injective
  haveI : Module.IsTorsionFree ℤ G := inferInstance
  haveI : Module.Free ℤ G := Module.free_of_finite_type_torsion_free' (R := ℤ) (M := G)
  haveI : TwoUniqueSums G :=
    TwoUniqueSums.of_injective_addHom
      ((Module.Free.chooseBasis ℤ G).repr.toLinearMap.toAddMonoidHom.toAddHom)
      (Module.Free.chooseBasis ℤ G).repr.injective inferInstance
  haveI : UniqueSums G := inferInstance
  -- pull the two finite sets back into the subgroup
  have hSG : ∀ a ∈ S, a ∈ G := fun a ha =>
    AddSubgroup.subset_closure (by simp [ha])
  have hTG : ∀ b ∈ T, b ∈ G := fun b hb =>
    AddSubgroup.subset_closure (by simp [hb])
  set S' : Finset G := S.subtype (· ∈ G) with hS'
  set T' : Finset G := T.subtype (· ∈ G) with hT'
  have hS'ne : S'.Nonempty := by
    obtain ⟨a, ha⟩ := hS
    exact ⟨⟨a, hSG a ha⟩, by simpa [hS', Finset.mem_subtype] using ha⟩
  have hT'ne : T'.Nonempty := by
    obtain ⟨b, hb⟩ := hT
    exact ⟨⟨b, hTG b hb⟩, by simpa [hT', Finset.mem_subtype] using hb⟩
  obtain ⟨a0, ha0, b0, hb0, huniq⟩ := UniqueSums.uniqueAdd_of_nonempty hS'ne hT'ne
  refine ⟨(a0 : A), by simpa [hS', Finset.mem_subtype] using ha0,
    (b0 : A), by simpa [hT', Finset.mem_subtype] using hb0, ?_⟩
  intro a b ha hb hab
  have ha' : (⟨a, hSG a ha⟩ : G) ∈ S' := by simpa [hS', Finset.mem_subtype] using ha
  have hb' : (⟨b, hTG b hb⟩ : G) ∈ T' := by simpa [hT', Finset.mem_subtype] using hb
  have : ((⟨a, hSG a ha⟩ : G) + ⟨b, hTG b hb⟩) = a0 + b0 := Subtype.ext (by simpa using hab)
  obtain ⟨h1, h2⟩ := huniq ha' hb' this
  exact ⟨congrArg Subtype.val h1, congrArg Subtype.val h2⟩

/-- **A torsion-free abelian group has unique products** (multiplicative form). -/
theorem uniqueProds_of_isMulTorsionFree (H : Type*) [CommGroup H] [IsMulTorsionFree H] :
    UniqueProds H := by
  haveI : IsAddTorsionFree (Additive H) := inferInstance
  haveI : UniqueSums (Additive H) := uniqueSums_of_isAddTorsionFree (Additive H)
  haveI : UniqueProds (Multiplicative (Additive H)) := inferInstance
  exact UniqueProds.of_injective_mulHom
    (MulEquiv.multiplicativeAdditive H).symm.toMonoidHom.toMulHom
    (MulEquiv.multiplicativeAdditive H).symm.injective inferInstance

/-- **The group ring of a torsion-free abelian group over an integral domain is an integral
domain.**  This is the hypothesis on the coefficient ring `k[H]` used in Lemma 2.1, for
`k = ℤ` and `k = 𝔽ₚ`. -/
theorem monoidAlgebra_isDomain (k : Type*) [CommRing k] [IsDomain k]
    (H : Type*) [CommGroup H] [IsMulTorsionFree H] :
    IsDomain (MonoidAlgebra k H) := by
  haveI : UniqueProds H := uniqueProds_of_isMulTorsionFree H
  infer_instance

/-- The case `k = ℤ` of `monoidAlgebra_isDomain`, used in the integral requirement (2.2). -/
theorem intMonoidAlgebra_isDomain (H : Type*) [CommGroup H] [IsMulTorsionFree H] :
    IsDomain (MonoidAlgebra ℤ H) :=
  monoidAlgebra_isDomain ℤ H

/-- The case `k = 𝔽ₚ` of `monoidAlgebra_isDomain`, used in the requirements modulo a prime. -/
theorem zmodMonoidAlgebra_isDomain (p : ℕ) [Fact p.Prime] (H : Type*) [CommGroup H]
    [IsMulTorsionFree H] : IsDomain (MonoidAlgebra (ZMod p) H) :=
  monoidAlgebra_isDomain (ZMod p) H

end FiniteChains
