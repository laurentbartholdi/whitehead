import RequestProject.PresCocycleCoverFoxBoundary
import RequestProject.PresPosetGroupEquiv
import RequestProject.PresPosetConnected
import RequestProject.ConnectedCellularZeroFillings

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

set_option maxHeartbeats 1600000

namespace FiniteChains.PresModel.PresCocycleCover
open Comb
universe u
variable {α J : Type u} (w : J → List (α × Bool))
  (N : Subgroup (FreeGroup α)) [N.Normal] (hword : ∀ j, FreeGroup.mk (w j) ∈ N)

theorem quotient_monodromy_alphaFree :
    ((Coc w (qof N) (quotient_relators_close w N hword)).monodromy (ptBase w)).comp
      (alphaFree w) = QuotientGroup.mk' N := by
  apply FreeGroup.ext_hom
  intro i
  rw (config := { transparency := .default }) [MonoidHom.comp_apply, alphaFree_of]

theorem quotient_monodromy_surjective : Function.Surjective
    ((Coc w (qof N) (quotient_relators_close w N hword)).monodromy (ptBase w)) := by
  intro g
  obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective N g
  exact ⟨alphaFree w x, (DFunLike.congr_fun
    (quotient_monodromy_alphaFree w N hword) x).trans hx⟩

theorem quotient_isConnected (hpos : ∀ j, 0 < (w j).length) :
    IsConnected (orderCx (QuotientCover w N hword)) :=
  (Coc w (qof N) (quotient_relators_close w N hword)).cover_isConnected (ptBase w)
    (presPos_isConnected w (fun j => List.length_pos_iff.mp (hpos j)))
    (quotient_monodromy_surjective w N hword)

variable (ρ : J → FreeGroup α) (hw : ∀ j, FreeGroup.mk (w j) = ρ j)
  (hpos : ∀ j, 0 < (w j).length) (H : Subgroup (PresGroup ρ)) [H.Normal]

abbrev subgroupPreimage : Subgroup (FreeGroup α) := H.comap (QuotientGroup.mk' (relSub ρ))

include hw in
omit [H.Normal] in
theorem subgroupPreimage_contains_relators (j : J) :
    FreeGroup.mk (w j) ∈ subgroupPreimage ρ H := by
  change (QuotientGroup.mk (FreeGroup.mk (w j)) : PresGroup ρ) ∈ H
  rw (config := { transparency := .default }) [hw j, (QuotientGroup.eq_one_iff _).mpr
    (Subgroup.subset_normalClosure (Set.mem_range_self j))]
  exact H.one_mem

abbrev SubgroupCover := QuotientCover w (subgroupPreimage ρ H)
  (subgroupPreimage_contains_relators w ρ hw H)
abbrev subgroupCoc := Coc w (qof (subgroupPreimage ρ H))
  (quotient_relators_close w (subgroupPreimage ρ H)
    (subgroupPreimage_contains_relators w ρ hw H))

include hpos in
/-- Reading identifies the actual monodromy kernel with the specified original subgroup. -/
theorem subgroup_monodromy_kernel_iff (z : Pi1 (orderCx (PresPos w)) (ptBase w)) :
    (subgroupCoc w ρ hw H).monodromy (ptBase w) z = 1 ↔ readingPresW ρ w hw z ∈ H := by
  obtain ⟨g, rfl⟩ := alphaHomW_surjective w ρ hw hpos z
  induction g using QuotientGroup.induction_on with
  | _ x =>
    rw [readingPresW_alphaHomW]
    change (subgroupCoc w ρ hw H).monodromy (ptBase w) (alphaFree w x) = 1 ↔ _
    rw [show (subgroupCoc w ρ hw H).monodromy (ptBase w) (alphaFree w x) =
        QuotientGroup.mk x from DFunLike.congr_fun (quotient_monodromy_alphaFree w
          (subgroupPreimage ρ H) (subgroupPreimage_contains_relators w ρ hw H)) x]
    exact QuotientGroup.eq_one_iff x

def subgroupKernelHom : ((subgroupCoc w ρ hw H).monodromy (ptBase w)).ker →* H :=
  ((readingPresW ρ w hw).comp
    ((subgroupCoc w ρ hw H).monodromy (ptBase w)).ker.subtype).codRestrict H (by
      intro z
      exact (subgroup_monodromy_kernel_iff w ρ hw hpos H z.val).mp z.property)

theorem subgroupKernelHom_bijective : Function.Bijective (subgroupKernelHom w ρ hw hpos H) := by
  constructor
  · intro z t he
    apply Subtype.ext
    exact readingPresW_injective w ρ hw hpos (congrArg Subtype.val he)
  · intro g
    let z := alphaHomW ρ w hw g.val
    have hz : (subgroupCoc w ρ hw H).monodromy (ptBase w) z = 1 :=
      (subgroup_monodromy_kernel_iff w ρ hw hpos H z).mpr (by
        rw [show readingPresW ρ w hw z = g.val from readingPresW_alphaHomW ρ w hw g.val]
        exact g.property)
    refine ⟨⟨z, hz⟩, ?_⟩
    apply Subtype.ext
    exact readingPresW_alphaHomW ρ w hw g.val

/-- Fundamental group of the genuine covering, with its original subgroup marking. -/
noncomputable def subgroupCoverPi1Equiv :
    Pi1 (orderCx (SubgroupCover w ρ hw H)) ((subgroupCoc w ρ hw H).coverBase (ptBase w)) ≃* H :=
  ((subgroupCoc w ρ hw H).coverPi1KernelEquiv (ptBase w)).trans
    (MulEquiv.ofBijective (subgroupKernelHom w ρ hw hpos H)
      (subgroupKernelHom_bijective w ρ hw hpos H))

include hpos in
theorem subgroupCover_pi1_perfect (hperf : ⁅H, H⁆ = H) :
    commutator (Pi1 (orderCx (SubgroupCover w ρ hw H))
      ((subgroupCoc w ρ hw H).coverBase (ptBase w))) = ⊤ := by
  have hH : commutator H = ⊤ := by
    apply top_unique
    intro g _
    have hg : g.val ∈ (commutator H).map H.subtype := by
      rw (config := { transparency := .default }) [H.map_subtype_commutator, hperf]
      exact g.property
    obtain ⟨x, hx, he⟩ := hg
    exact (Subtype.ext he : x = g) ▸ hx
  let e := (subgroupCoverPi1Equiv w ρ hw hpos H).symm
  have hr : e.toMonoidHom.range = ⊤ := MonoidHom.range_eq_top.mpr e.surjective
  have he := map_commutator_eq H e.toMonoidHom
  rw (config := { transparency := .default }) [hH, Subgroup.map_top_of_surjective _ e.surjective, hr, ← commutator_def] at he
  exact he.symm

include hpos in
/-- Perfectness supplies genuine strict one-cycle fillings, with no finite-cell restriction. -/
theorem subgroupCover_one_cycle_filling (hperf : ⁅H, H⁆ = H)
    (c : StrictOrdEdge (SubgroupCover w ρ hw H) →₀ ℤ)
    (hc : Comb.bdry1 (strictOrderCx (SubgroupCover w ρ hw H)) c = 0) :
    ∃ d : StrictOrdTri (SubgroupCover w ρ hw H) →₀ ℤ,
      Comb.bdry2 (strictOrderCx (SubgroupCover w ρ hw H)) d = c := by
  let C := SubgroupCover w ρ hw H
  have hweak : Comb.bdry1 (orderCx C) (chain1 (strictOrderIncl C) c) = 0 := by
    rw (config := { transparency := .default }) [bdry1_chain1, hc, map_zero]
  obtain ⟨d, hd⟩ := oneCycle_filling_of_perfect_pi1 (orderCx C)
    ((subgroupCoc w ρ hw H).coverBase (ptBase w))
    (quotient_isConnected w (subgroupPreimage ρ H)
      (subgroupPreimage_contains_relators w ρ hw H) hpos)
    (subgroupCover_pi1_perfect w ρ hw hpos H hperf) _ hweak
  exact ⟨normalizeOrdChain2 d, by
    rw (config := { transparency := .default }) [bdry2_normalizeOrdChain2, hd]
    exact normalizeOrdChain1_inclusion c⟩

variable [DecidableEq α]

include hpos in
/-- The specified perfect subgroup and finite-support Fox tests give a genuinely acyclic poset cover. -/
theorem subgroupCover_isAcyclic
    (hsat : ∀ v : J →₀ MonoidAlgebra ℤ (PresGroup ρ), FoxSat (foxMatrixPres ρ) v H)
    (hperf : ⁅H, H⁆ = H) : IsAcyclic (strictOrderCx (SubgroupCover w ρ hw H)) := by
  let N := subgroupPreimage ρ H
  have hR : relSub ρ ≤ N := by
    intro r hr
    change (QuotientGroup.mk r : PresGroup ρ) ∈ H
    rw (config := { transparency := .default }) [(QuotientGroup.eq_one_iff r).mpr hr]
    exact H.one_mem
  have hNeq : presSub ρ N = H :=
    Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) H
  have hinj : Function.Injective (coverSecondBoundary N ρ) := by
    apply fs_injective_boundary_of_foxSat ρ N hR
    intro v
    rw (config := { transparency := .default }) [hNeq]
    exact hsat v
  have hwfun : (fun j => FreeGroup.mk (w j)) = ρ := funext hw
  have hi : Function.Injective (coverSecondBoundary N (fun j => FreeGroup.mk (w j))) := by
    rw (config := { transparency := .default }) [hwfun]
    exact hinj
  refine ⟨?_, subgroupCover_one_cycle_filling w ρ hw hpos H hperf, ?_⟩
  · apply (injective_iff_map_eq_zero _).mpr
    exact quotient_two_cycle_zero w N (subgroupPreimage_contains_relators w ρ hw H) hpos hi
  · exact strict_order_zeroCycle_filling_of_connected (P := SubgroupCover w ρ hw H)
      ((subgroupCoc w ρ hw H).coverBase (ptBase w))
      (quotient_isConnected w N (subgroupPreimage_contains_relators w ρ hw H) hpos)

end FiniteChains.PresModel.PresCocycleCover
