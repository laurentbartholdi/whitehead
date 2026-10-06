import Mathlib

open scoped commutatorElement

/-!
# The group computation of Lemma 3.1

Lemma 3.1 builds, over an acyclic complex `D` with presentation
`⟨x_i (i ∈ I) | r_j (j ∈ J)⟩` and exponent-sum matrix `M`, the complex

  `Y_D = ⟨x_i, a_i, b_i | r_j, x_i[a_i,b_i]⁻¹, [a_i,a_k], [a_i,b_k], [b_i,a_k], [b_i,b_k]⟩`,

and computes `G(Y_D) = ⊕_i (ℤ a_i ⊕ ℤ b_i)`.  The group-theoretic heart of that
computation is the elimination step proved here: after `x_i` has been eliminated
by `x_i = [a_i, b_i]`, the cross-commutators make the elements
`U_i = [a_i, b_i]` commute, the relators `r_j` become `∏_i U_i^{M_{ij}} = 1`,
and surjectivity of the exponent-sum matrix `M` — which holds because `D` is
acyclic, `M` being then an isomorphism — forces `U_i = 1` for every `i`.
Consequently all the generators `a_i, b_i` commute.

Only this group theory is formalized; the passage from the complex to the
presentation, and the homotopy-theoretic half of Lemma 3.1 (Cockcroftness of
`Y_D` and the vanishing on `π₂`), are not.
-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains

variable {G : Type*} [Group G] {I J : Type*}

/-- The commutator `U i = ⁅a i, b i⁆` of the `i`-th added pair of generators. -/
def pairComm (a b : I → G) (i : I) : G := ⁅a i, b i⁆

/-- The cross-commutator relations of `Y_D`: generators with different indices commute. -/
def CrossCommuting (a b : I → G) : Prop :=
  ∀ i k : I, i ≠ k →
    Commute (a i) (a k) ∧ Commute (a i) (b k) ∧ Commute (b i) (a k) ∧ Commute (b i) (b k)

/-- The cross-commutators make the elements `U_i` commute. -/
theorem commute_pairComm (a b : I → G) (hab : CrossCommuting a b) (i k : I) :
    Commute (pairComm a b i) (pairComm a b k) := by
  classical
  by_cases hik : i = k
  · subst hik; exact Commute.refl _
  · obtain ⟨haa, hab', hba, hbb⟩ := hab i k hik
    have ha : Commute (a i) (pairComm a b k) :=
      ((haa.mul_right hab').mul_right haa.inv_right).mul_right hab'.inv_right
    have hb : Commute (b i) (pairComm a b k) :=
      ((hba.mul_right hbb).mul_right hba.inv_right).mul_right hbb.inv_right
    exact ((ha.mul_left hb).mul_left ha.inv_left).mul_left hb.inv_left

theorem commute_pairComm_zpow (a b : I → G) (hab : CrossCommuting a b) (i k : I) (m n : ℤ) :
    Commute (pairComm a b i ^ m) (pairComm a b k ^ n) :=
  (commute_pairComm a b hab i k).zpow_zpow m n

/-- The relator `∏_i U_i^{c_i}`, as an unordered product of pairwise commuting elements. -/
noncomputable def relatorProd (a b : I → G) (hab : CrossCommuting a b) (c : I →₀ ℤ) : G :=
  c.support.noncommProd (fun i => pairComm a b i ^ c i)
    (fun x _ y _ _ => commute_pairComm_zpow a b hab x y _ _)

/-- **The elimination step of Lemma 3.1.**  If the added pairs cross-commute, if each
relator becomes `∏_i U_i^{M_{ij}} = 1`, and if the exponent-sum matrix `M` is surjective,
then every `U_i` is trivial. -/
theorem pairComm_eq_one (a b : I → G) (hab : CrossCommuting a b) (M : J → (I →₀ ℤ))
    (hrel : ∀ j, relatorProd a b hab (M j) = 1)
    (hsurj : Function.Surjective (Finsupp.linearCombination ℤ M)) :
    ∀ i, pairComm a b i = 1 := by
  classical
  set S : Set G := Set.range (pairComm a b) with hS
  have hcomm : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x := by
    rintro _ ⟨i, rfl⟩ _ ⟨k, rfl⟩
    exact commute_pairComm a b hab i k
  haveI : IsMulCommutative (Subgroup.closure S) :=
    Subgroup.isMulCommutative_closure (fun x hx y hy _ => hcomm x hx y hy)
  open scoped IsMulCommutative in
  letI : CommGroup (Subgroup.closure S) := inferInstance
  set V : I → Subgroup.closure S := fun i =>
    ⟨pairComm a b i, Subgroup.subset_closure ⟨i, rfl⟩⟩ with hV
  set phi : (I →₀ ℤ) →+ Additive (Subgroup.closure S) :=
    Finsupp.liftAddHom fun i => zmultiplesHom (Additive (Subgroup.closure S))
      (Additive.ofMul (V i)) with hphi
  have hphi_single : ∀ (i : I) (n : ℤ),
      Additive.toMul (phi (Finsupp.single i n)) = V i ^ n := by
    intro i n
    rw [hphi, Finsupp.liftAddHom_apply_single]
    rfl
  have hphi_prod : ∀ c : I →₀ ℤ,
      Additive.toMul (phi c) = ∏ i ∈ c.support, V i ^ c i := by
    intro c
    have hgen : ∀ (s : Finset I) (c : I →₀ ℤ), c.support ⊆ s →
        Additive.toMul (phi c) = ∏ i ∈ s, V i ^ c i := by
      intro s
      induction s using Finset.induction with
      | empty =>
          intro c hc
          have hc0 : c = 0 := by
            refine Finsupp.ext fun i => ?_
            by_contra hi
            exact absurd (hc (Finsupp.mem_support_iff.mpr hi)) (by simp)
          subst hc0
          simp [hphi]
      | insert i s hi ih =>
          intro c hc
          have hsplit : c = Finsupp.single i (c i) + c.erase i := by
            refine Finsupp.ext fun k => ?_
            by_cases hk : k = i <;> simp [hk, Finsupp.erase_ne]
          have herase : (c.erase i).support ⊆ s := by
            intro k hk
            rw [Finsupp.support_erase] at hk
            have hne : k ≠ i := Finset.ne_of_mem_erase hk
            have hk' : k ∈ c.support := Finset.mem_of_mem_erase hk
            rcases Finset.mem_insert.mp (hc hk') with h | h
            · exact absurd h hne
            · exact h
          rw [Finset.prod_insert hi]
          conv_lhs => rw [hsplit]
          rw [map_add]
          have : Additive.toMul (phi (Finsupp.single i (c i)) + phi (c.erase i)) =
              Additive.toMul (phi (Finsupp.single i (c i))) *
                Additive.toMul (phi (c.erase i)) := rfl
          rw [this, hphi_single, ih (c.erase i) herase]
          refine congrArg (fun z => V i ^ c i * z) (Finset.prod_congr rfl fun k hk => ?_)
          have hne : k ≠ i := fun h => hi (h ▸ hk)
          rw [Finsupp.erase_ne hne]
    exact hgen c.support c (Finset.Subset.refl _)
  -- the relators say that `phi` kills every column of `M`
  have hphiM : ∀ j, phi (M j) = 0 := by
    intro j
    have hval : Additive.toMul (phi (M j)) = 1 := by
      apply Subtype.ext
      rw [hphi_prod, ← Finset.noncommProd_eq_prod]
      show (Subgroup.subtype _) ((M j).support.noncommProd (fun i => V i ^ (M j) i) _) = _
      rw [Finset.map_noncommProd (M j).support (fun i => V i ^ (M j) i) _
        ((Subgroup.closure S).subtype)]
      have hcast : ((M j).support.noncommProd
          (fun i => (Subgroup.closure S).subtype (V i ^ (M j) i)) (by
            intro x _ y _ _
            exact commute_pairComm_zpow a b hab x y _ _)) = relatorProd a b hab (M j) := by
        rfl
      rw [hcast, hrel j]
      rfl
    exact hval
  -- hence it kills the whole image of `M`
  have hzero : ∀ c : J →₀ ℤ, phi (Finsupp.linearCombination ℤ M c) = 0 := by
    intro c
    rw [Finsupp.linearCombination_apply, Finsupp.sum, map_sum]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [AddMonoidHom.map_zsmul, hphiM j, smul_zero]
  intro i
  obtain ⟨c, hc⟩ := hsurj (Finsupp.single i 1)
  have h0 : phi (Finsupp.single i (1 : ℤ)) = 0 := by rw [← hc]; exact hzero c
  have h1 : V i = 1 := by
    have hval := hphi_single i 1
    rw [h0] at hval
    simpa using hval.symm
  exact congrArg Subtype.val h1

/-- **Consequence.**  In the situation of Lemma 3.1 all the added generators commute, so the
group they generate is abelian. -/
theorem commute_gens (a b : I → G) (hab : CrossCommuting a b) (M : J → (I →₀ ℤ))
    (hrel : ∀ j, relatorProd a b hab (M j) = 1)
    (hsurj : Function.Surjective (Finsupp.linearCombination ℤ M)) :
    ∀ x ∈ Set.range a ∪ Set.range b, ∀ y ∈ Set.range a ∪ Set.range b, x * y = y * x := by
  classical
  have hU := pairComm_eq_one a b hab M hrel hsurj
  have hself : ∀ i, Commute (a i) (b i) := by
    intro i
    rw [← commutatorElement_eq_one_iff_commute]
    exact hU i
  rintro x (⟨i, rfl⟩ | ⟨i, rfl⟩) y (⟨k, rfl⟩ | ⟨k, rfl⟩) <;> by_cases hik : i = k
  · subst hik; rfl
  · exact (hab i k hik).1
  · subst hik; exact hself i
  · exact (hab i k hik).2.1
  · subst hik; exact (hself i).symm
  · exact (hab i k hik).2.2.1
  · subst hik; rfl
  · exact (hab i k hik).2.2.2

end FiniteChains
