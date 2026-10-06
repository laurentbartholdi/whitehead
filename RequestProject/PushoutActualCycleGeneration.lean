module

public import RequestProject.PushoutRelativeCopyLabels
public import RequestProject.PushoutUniversalCellEmbedding
public import RequestProject.PushoutOldCoverHomology
public import RequestProject.AcyclicLiftedSubcomplex

@[expose] public section

/-! Actual regular-cover descent in degree two. Every universal-cover
two-cycle is a finite sum of images of genuine cycles in copies of the
universal cover of L. The component filters, fillings and old H2 vanishing
are all constructed in the imported files. Unverified source. -/

noncomputable section
open scoped Classical
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb.PushoutRelativeCopies
universe u v
variable {D K L : Complex2.{u}} {Q : Type v} [Group Q]
  (p : Hom D K) (hp : IsCovering p) (a : DeckAction D Q) (hr : IsRegular p a)
  (he : ∀ q e, p.onE (a.smulE q e) = p.onE e)
  (hf : ∀ q f, p.onF (a.smulF q f) = p.onF f)
  (i : Hom D L) (hiV : Function.Injective i.onV) (hiE : Function.Injective i.onE)
  (hiF : Function.Injective i.onF) (hDconn : IsConnected D) (hL : IsConnected L)
  (d₀ : D.V) (ht : Pi1Trivial i) (hD : IsAcyclic D)
  (hT : IsConnected (target p i hiV hiE))

def oldFaceChains : Submodule ℤ
    (UF (target p i hiV hiE) (root p i hiV hiE hiF (i.onV d₀)) →₀ ℤ) where
  carrier := {c | ∀ f, ¬ oldFace p i hiV hiE hiF (i.onV d₀) f → c f = 0}
  zero_mem' := fun _ _ => rfl
  add_mem' hc hd f hf := by simp only [Finsupp.add_apply, hc f hf, hd f hf, add_zero]
  smul_mem' n c hc f hf := by simp only [Finsupp.smul_apply, hc f hf, smul_zero]

include hp hr he hf hDconn ht hD hT in
theorem oldFaceChains_cycle_zero
    (c : UF (target p i hiV hiE) (root p i hiV hiE hiF (i.onV d₀)) →₀ ℤ)
    (hc : c ∈ oldFaceChains p i hiV hiE hiF d₀)
    (hz : bdry2 (uCover (target p i hiV hiE) (root p i hiV hiE hiF (i.onV d₀))) c = 0) : c = 0 := by
  have hzero : ∀ z : UF (target p i hiV hiE)
      (pushV p i (i.onV d₀)) →₀ ℤ,
      (∀ f ∈ z.support, ∃ k : K.F, f.val.2 = Sum.inl k) →
        bdry2 (uCover (target p i hiV hiE) (pushV p i (i.onV d₀))) z = 0 → z = 0 := by
    rw [pushV_of_mem p hiV]
    exact PushoutOldCover.old_two_cycle_zero p hp a hr he hf i hiV hiE hiF
      hDconn d₀ ht hT hD
  apply hzero c _ hz
  intro f hf'
  by_contra hn
  exact (Finsupp.mem_support_iff.mp hf') (hc f hn)

set_option maxHeartbeats 800000 in
include hp hr he hDconn hL ht hD hT in
theorem copy_filter_completion
    (c : UF (target p i hiV hiE) (root p i hiV hiE hiF (i.onV d₀)) →₀ ℤ)
    (hc : bdry2 (uCover (target p i hiV hiE) (root p i hiV hiE hiF (i.onV d₀))) c = 0)
    (g : Pi1 (target p i hiV hiE) (root p i hiV hiE hiF (i.onV d₀))) :
    ∃ z : UF (target p i hiV hiE) (root p i hiV hiE hiF (i.onV d₀)) →₀ ℤ,
      z ∈ Pi2FromSub (pushoutMap p i hiV hiE hiF) (root p i hiV hiE hiF (i.onV d₀)) ∧
      bdry2 (uCover (target p i hiV hiE) (root p i hiV hiE hiF (i.onV d₀))) z = 0 ∧
      c.filter (fun f => faceLabel p i hiV hiE hiF (i.onV d₀) f =
        UniversalCopy.vertices (pushoutMap p i hiV hiE hiF) (i.onV d₀) g) - z ∈
          oldFaceChains p i hiV hiE hiF d₀ := by
  let φ := UniversalCopy.map (pushoutMap p i hiV hiE hiF) (i.onV d₀) g
  let φ2 : (UF L (i.onV d₀) →₀ ℤ) →ₗ[ℤ]
      (UF (target p i hiV hiE) (root p i hiV hiE hiF (i.onV d₀)) →₀ ℤ) := chain2 φ
  let s := UniversalCopy.vertices (pushoutMap p i hiV hiE hiF) (i.onV d₀) g
  let d := c.filter (fun f => faceLabel p i hiV hiE hiF (i.onV d₀) f = s)
  have hφE : Function.Injective φ.onE := UniversalCopy.map_injective_E
    (pushoutMap p i hiV hiE hiF) (i.onV d₀)
    (PushoutSheets.univLift_edges_injective p hp a hr he i hiV hiE hiF hDconn hL d₀ ht) g
  have hφF : Function.Injective φ.onF := UniversalCopy.map_injective_F
    (pushoutMap p i hiV hiE hiF) (i.onV d₀)
    (PushoutSheets.univLift_faces_injective p hp a hr he i hiV hiE hiF hDconn hL d₀ ht) g
  have hd : ∀ f ∉ Set.range φ.onF, d f = 0 := by
    intro f hf'
    have hn : faceLabel p i hiV hiE hiF (i.onV d₀) f ≠ s := fun hl =>
      hf' (face_range_of_label p i hiV hiE hiF (i.onV d₀) hT hL g f hl)
    simp [d, hn]
  obtain ⟨b, hb⟩ := (Finsupp.mem_range_mapDomain_iff φ.onF hφF d).mpr hd
  change UF L (i.onV d₀) →₀ ℤ at b
  have hb' : φ2 b = d := hb
  have hdr : relativeBoundary p i hiV hiE hiF (i.onV d₀) d = 0 := by
    rw [show d = c.filter (fun f => faceLabel p i hiV hiE hiF (i.onV d₀) f = s) from rfl,
      relative_boundary_filter p i hiV hiE hiF (i.onV d₀) hT hL]
    have hcr : relativeBoundary p i hiV hiE hiF (i.onV d₀) c = 0 := by
      change (bdry2 (uCover (target p i hiV hiE) (root p i hiV hiE hiF (i.onV d₀))) c).filter _ = 0
      rw [hc, Finsupp.filter_zero]
    rw [hcr, Finsupp.filter_zero]
  have hbs : ∀ e ∈ (Comb.bdry2 (uCover L (i.onV d₀)) b).support, e.val.2 ∈ Set.range i.onE := by
    intro e he'
    by_contra hn
    have hnot : ¬ oldEdge p i hiV hiE hiF (i.onV d₀) (φ.onE e) :=
      fun hh => hn ((oldEdge_map_iff p i hiV hiE hiF (i.onV d₀) g e).mp hh)
    have hcoeff : Comb.bdry2 (uCover L (i.onV d₀)) b e = 0 := by
      have hh := congrArg (fun z => z (φ.onE e)) hdr
      have hbd : bdry2 (uCover (target p i hiV hiE) (root p i hiV hiE hiF (i.onV d₀))) d =
          chain1 φ (bdry2 (uCover L (i.onV d₀)) b) := by
        exact (congrArg (bdry2 (uCover (target p i hiV hiE)
          (root p i hiV hiE hiF (i.onV d₀)))) hb'.symm).trans (bdry2_chain2 φ b)
      change ((bdry2 (uCover (target p i hiV hiE) (root p i hiV hiE hiF (i.onV d₀))) d).filter
        (fun e => ¬ oldEdge p i hiV hiE hiF (i.onV d₀) e))
        (φ.onE e) = 0 at hh
      rw [Finsupp.filter_apply, if_pos hnot, hbd] at hh
      exact (Finsupp.mapDomain_apply_of_injective hφE _ e).symm.trans hh
    exact (Finsupp.mem_support_iff.mp he') hcoeff
  obtain ⟨w, hw, hwb⟩ := AcyclicLiftedSubcomplex.one_cycle_filling i hiV hiE hDconn d₀ ht hL hD
    (bdry2 (uCover L (i.onV d₀)) b) hbs (bdry1_bdry2 (X := uCover L (i.onV d₀)) b)
  have hcycle : bdry2 (uCover L (i.onV d₀)) (b - w) = 0 := by rw [map_sub, hwb, sub_self]
  refine ⟨φ2 (b - w), UniversalCopy.cycle_image_mem
    (pushoutMap p i hiV hiE hiF) (i.onV d₀) g (b - w) hcycle, ?_, ?_⟩
  · change bdry2 (uCover (target p i hiV hiE) (root p i hiV hiE hiF (i.onV d₀)))
      (chain2 φ (b - w)) = 0
    rw [bdry2_chain2, hcycle, map_zero]
  · have heq : d - φ2 (b - w) = φ2 w := by rw [map_sub, hb']; abel
    change d - φ2 (b - w) ∈ oldFaceChains p i hiV hiE hiF d₀
    rw [heq]
    intro f hf'
    by_contra hn
    have hm : f ∈ (Finsupp.mapDomain φ.onF w).support := Finsupp.mem_support_iff.mpr hn
    obtain ⟨t, ht', htf⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hm)
    apply hf'
    rw [← htf]
    exact (oldFace_map_iff p i hiV hiE hiF (i.onV d₀) g t).mpr (hw t ht')

include hp hr he hf hDconn hL ht hD hT in
/-- The actual finite-support spherical generation statement at the core
base point. No `Pi2GeneratedByUpstairs` or exactness input remains. -/
theorem cycle_mem_span_at_core
    (c : UF (target p i hiV hiE) (root p i hiV hiE hiF (i.onV d₀)) →₀ ℤ)
    (hc : bdry2 (uCover (target p i hiV hiE) (root p i hiV hiE hiF (i.onV d₀))) c = 0) :
    c ∈ Submodule.span ℤ
      (Pi2FromSub (pushoutMap p i hiV hiE hiF) (root p i hiV hiE hiF (i.onV d₀))) := by
  let label := faceLabel p i hiV hiE hiF (i.onV d₀)
  let S := c.support.image label
  let W := oldFaceChains p i hiV hiE hiF d₀
  let P : Submodule ℤ (UF (target p i hiV hiE) (root p i hiV hiE hiF (i.onV d₀)) →₀ ℤ) := Submodule.span ℤ
    (Pi2FromSub (pushoutMap p i hiV hiE hiF) (root p i hiV hiE hiF (i.onV d₀)))
  have hpiece (s : {s // s ∈ S}) :
      ∃ z, z ∈ P ∧ bdry2 (uCover (target p i hiV hiE) (root p i hiV hiE hiF (i.onV d₀))) z = 0 ∧
        c.filter (fun f => label f = s.val) - z ∈ W := by
    by_cases hs : s.val = ∅
    · refine ⟨0, P.zero_mem, map_zero _, ?_⟩
      rw [sub_zero]
      intro f hf'
      have hn : label f ≠ s.val := by
        rw [hs]
        exact fun hh => hf' ((faceLabel_empty_iff p i hiV hiE hiF (i.onV d₀) hT hL f).mp hh)
      simp [hn]
    · obtain ⟨f, hf', hfs⟩ := Finset.mem_image.mp s.property
      have hfoff : ¬ oldFace p i hiV hiE hiF (i.onV d₀) f := by
        intro hh
        exact hs (hfs.symm.trans (faceLabel_empty_of_old p i hiV hiE hiF (i.onV d₀) f hh))
      obtain ⟨g, hg⟩ := faceLabel_of_not_old p i hiV hiE hiF (i.onV d₀) hT hL f hfoff
      obtain ⟨z, hz, hzc, hzd⟩ := copy_filter_completion p hp a hr he i hiV hiE hiF
        hDconn hL d₀ ht hD hT c hc g
      refine ⟨z, Submodule.subset_span hz, hzc, ?_⟩
      have hsg : s.val = UniversalCopy.vertices (pushoutMap p i hiV hiE hiF) (i.onV d₀) g :=
        hfs.symm.trans hg
      simpa only [hsg] using hzd
  choose z hz hzc hzd using hpiece
  let zsum := ∑ s : {s // s ∈ S}, z s
  have hzp : zsum ∈ P := P.sum_mem (fun s _ => hz s)
  have hzb : bdry2 (uCover (target p i hiV hiE) (root p i hiV hiE hiF (i.onV d₀))) zsum = 0 := by
    simp only [zsum, map_sum, hzc, Finset.sum_const_zero]
  have hdiff : c - zsum ∈ W := by
    have hh := W.sum_mem (fun s (_ : s ∈ (Finset.univ : Finset {s // s ∈ S})) => hzd s)
    rw [Finset.sum_sub_distrib] at hh
    have hsum : (∑ s : {s // s ∈ S}, c.filter (fun f => label f = s.val)) = c := by
      exact (Finset.sum_coe_sort S (fun s => c.filter (fun f => label f = s))).trans
        (finsupp_sum_label_filters label c)
    rw [hsum] at hh
    exact hh
  have hzero : c - zsum = 0 := oldFaceChains_cycle_zero p hp a hr he hf i hiV hiE hiF
    hDconn d₀ ht hD hT _ hdiff (by rw [map_sub, hc, hzb, sub_self])
  rw [sub_eq_zero.mp hzero]
  exact hzp

end FiniteChains.Comb.PushoutRelativeCopies
