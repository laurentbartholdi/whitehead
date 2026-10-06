import RequestProject.ChamberQuotientEquivariantGeneration
import RequestProject.ChamberZConnected
import RequestProject.OrderUniversalTetLift
import RequestProject.OrderNervePositiveFillings

/-! Genuine quotient universal-cover generation in the full homogeneous nerve. -/
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

set_option maxHeartbeats 800000

namespace FiniteChains.Davis
open RACG Mirror Comb Nerve
universe u
variable {V : Type u} [DecidableEq V] [Fintype V] {A : CommRel V}
  {X : Type u} [PartialOrder X] {att : NeSpx A →o X}

theorem qUniversal_generatesDegreeIn_base (x : X) (hx : IsConnected (orderCx X)) :
    GeneratesDegreeIn (fun _ : UOrder (Qpos A X att) (qNew x) => True)
      (fun p => InQBase (uOrderEnd p)) 3 := by
  letI : Nonempty X := ⟨x⟩
  let a : Zpos A X (IsGamma A) att := zNew ⟨1, isGamma_one⟩ x
  let S : Set (UOrder (Qpos A X att) (qNew x)) := {p | InQBase (uOrderEnd p)}
  intro c hc hd hcyc
  let z := decodeOrdNerve2 c
  have hz : ordNerveChain2 z = c := by
    rw (config := { transparency := .default }) [ordNerveChain2_decode (incOn_le_inc _ hc), hd]
  have hzc : Comb.bdry2 (orderCx (UOrder (Qpos A X att) (qNew x))) z = 0 :=
    (ordNerveChain2_cycle_iff z).mp (by rw (config := { transparency := .default }) [hz]; exact hcyc)
  have hgen := exists_qCover_base_cellular_cycle a
    (zpos_isConnected hx) (chain2 uOrderHom z) ((uOrderHom_cycle_iff z).mpr hzc)
  simp only [a, zProj_zNew] at hgen
  obtain ⟨d, hds, hdc, y, he⟩ := hgen
  obtain ⟨b, hbc, hbd⟩ := exists_qCover_base_cycle_preimage d hds hdc
  change (OrdTri S →₀ ℤ) at b
  have hbcN : Nerve.bdry (ordNerveChain2 (P := S) b) = 0 :=
    (ordNerveChain2_cycle_iff (P := S) b).mpr hbc
  obtain ⟨v, hv⟩ := exists_uOrder_three_chain y
  have hbd' : chain2 uOrderHom (chain2 (ordSubposetIncl S) b) = d := by
    change Finsupp.mapDomain uOrderFace (Finsupp.mapDomain (ordSubposetIncl S).onF b) = d
    rw (config := { transparency := .default }) [← Finsupp.mapDomain_comp]
    exact hbd
  let b' : OrdTri (UOrder (Qpos A X att) (qNew x)) →₀ ℤ :=
    chain2 (ordSubposetIncl S) b
  have hb' : chain2 uOrderHom b' = d := hbd'
  have hze : z = b' + ordBoundary3 v := by
    apply uOrderHom_chain2_injective
    rw (config := { transparency := .default }) [map_add, hb', uOrderHom_ordBoundary3, hv]
    exact he
  refine ⟨cmap (Subtype.val : S → UOrder (Qpos A X att) (qNew x)) (ordNerveChain2 b),
    cmap_val_mem_incOn _ (ordNerveChain2_mem_inc b), ordNerveChain3 v, ?_, ?_, ?_⟩
  · simpa only [cmap_id] using cmap_mem_incOn_of_maps (f := id) monotone_id
      (fun _ => True.intro) (ordNerveChain3_mem_inc v)
  · rw (config := { transparency := .default }) [← cmap_bdry, hbcN, map_zero]
  · rw (config := { transparency := .default }) [← hz, hze, map_add, ordNerveChain2_ordBoundary3]
    congr 1
    exact ordNerveChain2_chain2 Subtype.val monotone_subtypeVal b

end FiniteChains.Davis
