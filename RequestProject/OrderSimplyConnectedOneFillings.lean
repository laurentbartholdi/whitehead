module

public import RequestProject.OrderComponentLabels
public import RequestProject.CellularHomotopyChain
public import RequestProject.OrderNervePositiveFillings

@[expose] public section

/-! Finite one-cycle fillings when every component has trivial edge-path pi1. -/
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb
universe u
variable {P : Type u} [PartialOrder P]

/-- A componentwise path contraction gives actual finite cellular fillings.
Connectedness or finiteness of the whole poset is not required. -/
theorem order_oneCycle_filling_of_simplyConnected (hsc : SimplyConnected (orderCx P))
    (c : OrdEdge P →₀ ℤ) (hc : bdry1 (orderCx P) c = 0) :
    ∃ y : OrdTri P →₀ ℤ, bdry2 (orderCx P) y = c := by
  classical
  let r : P → P := fun v => Quotient.out (orderComponentLabel P v)
  have hr (e : OrdEdge P) : r e.1.1 = r e.1.2 :=
    congrArg Quotient.out (orderComponentLabel_eq_of_le e.2)
  have hreach (v : P) : Reach (orderCx P) (r v) v :=
    (orderComponentLabel_eq_iff _ _).mp (Quotient.out_eq _)
  choose p hp using hreach
  have hface (e : (orderCx P).E) : ∃ y : OrdTri P →₀ ℤ,
      bdry2 (orderCx P) y = Finsupp.single e (1 : ℤ) + pathChain (p e.1.1) -
        pathChain (p e.1.2) := by
    let l := p e.1.1 ++ [(e, true)] ++ revPath (p e.1.2)
    have hrev : IsPath (orderCx P).src (orderCx P).tgt (revPath (p e.1.2))
        e.1.2 (r e.1.1) := by
      rw [hr e]
      exact isPath_revPath (hp e.1.2)
    have hl : IsPath (orderCx P).src (orderCx P).tgt l (r e.1.1) (r e.1.1) :=
      ((hp e.1.1).append (show IsPath (orderCx P).src (orderCx P).tgt
        [(e, true)] e.1.1 e.1.2 from ⟨rfl, rfl⟩)).append hrev
    obtain ⟨y, hy⟩ := (hsc _ l hl).exists_boundary
    refine ⟨y, ?_⟩
    simpa [l, pathChain_append, pathChain_cons, pathChain_revPath,
      sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hy
  choose f hf using hface
  let s : (P →₀ ℤ) →ₗ[ℤ] (OrdEdge P →₀ ℤ) :=
    Finsupp.linearCombination ℤ (fun v => pathChain (p v))
  let t : (OrdEdge P →₀ ℤ) →ₗ[ℤ] (OrdTri P →₀ ℤ) :=
    Finsupp.linearCombination ℤ f
  have hs (v : P) : s (Finsupp.single v 1) = pathChain (p v) := by
    simp [s]
  have ht (z : OrdEdge P →₀ ℤ) : bdry2 (orderCx P) (t z) =
      z - s (bdry1 (orderCx P) z) := by
    induction z using Finsupp.induction_linear with
    | zero => simp
    | add z w hz hw => rw [map_add, map_add, hz, hw, map_add, map_add]; abel
    | single e n =>
      change bdry2 (orderCx P) (Finsupp.linearCombination ℤ f (Finsupp.single e n)) = _
      rw [Finsupp.linearCombination_single, map_smul, hf, bdry1_single,
        map_smul, map_sub, hs, hs, smul_sub, smul_add, smul_sub]
      simp only [Finsupp.smul_single, smul_eq_mul, mul_one]
      simp only [orderCx]
      abel
  exact ⟨t c, by rw [ht, hc, map_zero, sub_zero]⟩

theorem nerve_oneCycle_filling_of_simplyConnected (hsc : SimplyConnected (orderCx P))
    (c : Nerve.Ch P) (hi : c ∈ Nerve.Inc P)
    (hd : Nerve.lengthProjection 2 c = c) (hc : Nerve.bdry c = 0) :
    ∃ y ∈ Nerve.Inc P, Nerve.bdry y = c := by
  have he : ordNerveChain1 (decodeOrdNerve1 c) = c := by
    rw [ordNerveChain1_decode hi, hd]
  have hcyc : bdry1 (orderCx P) (decodeOrdNerve1 c) = 0 :=
    (ordNerveChain1_cycle_iff _).mp (by rw [he]; exact hc)
  obtain ⟨y, hy⟩ := order_oneCycle_filling_of_simplyConnected hsc _ hcyc
  refine ⟨ordNerveChain2 y, ordNerveChain2_mem_inc y, ?_⟩
  rw [← ordNerveChain1_bdry2, hy, he]

end FiniteChains.Comb
