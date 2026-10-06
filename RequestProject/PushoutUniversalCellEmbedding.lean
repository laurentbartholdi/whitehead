module

public import RequestProject.PushoutUniversalEmbedding
public import RequestProject.CombCoveringLift

@[expose] public section

/-! The actual L-copy in the universal pushout is injective on all cells.
The base map itself identifies old cells; source/base vertices and the
covering lifting uniqueness recover them. Unverified source. -/

noncomputable section
open scoped Classical
namespace FiniteChains.Comb.PushoutSheets
universe u v
variable {D K L : Complex2.{u}} {Q : Type v} [Group Q]
  (p : Hom D K) (hp : IsCovering p) (a : DeckAction D Q) (hr : IsRegular p a)
  (he : ∀ q e, p.onE (a.smulE q e) = p.onE e)
  (i : Hom D L) (hiV : Function.Injective i.onV) (hiE : Function.Injective i.onE)
  (hiF : Function.Injective i.onF)

include hp hiV hiE in
theorem pushE_injective_at_source {e f : L.E}
    (hs : L.src e = L.src f) (hf : pushE p i e = pushE p i f) : e = f := by
  by_cases heD : ∃ d, i.onE d = e
  · obtain ⟨d, rfl⟩ := heD
    rw [pushE_of_mem p hiE] at hf
    by_cases hfD : ∃ e, i.onE e = f
    · obtain ⟨e, rfl⟩ := hfD
      rw [pushE_of_mem p hiE] at hf
      have hsrc : D.src d = D.src e := hiV (by simpa only [i.src_onE] using hs)
      have hproj : p.onE d = p.onE e := Sum.inl.inj hf
      have hh := liftGerm_unique hp (x := (d, true)) (y := (e, true)) rfl hsrc.symm
        (congrArg (fun z => (z, true)) hproj)
      exact congrArg i.onE (congrArg Prod.fst hh)
    · rw [pushE_of_off p i ⟨f, fun d hd => hfD ⟨d, hd⟩⟩] at hf
      exact (Sum.inl_ne_inr hf).elim
  · rw [pushE_of_off p i ⟨e, fun d hd => heD ⟨d, hd⟩⟩] at hf
    by_cases hfD : ∃ d, i.onE d = f
    · obtain ⟨d, rfl⟩ := hfD
      rw [pushE_of_mem p hiE] at hf
      exact (Sum.inr_ne_inl hf).elim
    · rw [pushE_of_off p i ⟨f, fun d hd => hfD ⟨d, hd⟩⟩] at hf
      exact congrArg (fun x : OffE i => x.val) (Sum.inr.inj hf)

include hp hiV hiF in
theorem pushF_injective_at_base {e f : L.F}
    (hs : L.base e = L.base f) (hf : pushF p i e = pushF p i f) : e = f := by
  by_cases heD : ∃ d, i.onF d = e
  · obtain ⟨d, rfl⟩ := heD
    rw [pushF_of_mem p hiF] at hf
    by_cases hfD : ∃ e, i.onF e = f
    · obtain ⟨e, rfl⟩ := hfD
      rw [pushF_of_mem p hiF] at hf
      have hbase : D.base d = D.base e := hiV (by simpa only [i.base_onF] using hs)
      have hproj : p.onF d = p.onF e := Sum.inl.inj hf
      have hh : d = e := hp.cell.1 (Subtype.ext (Prod.ext hproj hbase))
      exact congrArg i.onF hh
    · rw [pushF_of_off p i ⟨f, fun d hd => hfD ⟨d, hd⟩⟩] at hf
      exact (Sum.inl_ne_inr hf).elim
  · rw [pushF_of_off p i ⟨e, fun d hd => heD ⟨d, hd⟩⟩] at hf
    by_cases hfD : ∃ d, i.onF d = f
    · obtain ⟨d, rfl⟩ := hfD
      rw [pushF_of_mem p hiF] at hf
      exact (Sum.inr_ne_inl hf).elim
    · rw [pushF_of_off p i ⟨f, fun d hd => hfD ⟨d, hd⟩⟩] at hf
      exact congrArg (fun x : OffF i => x.val) (Sum.inr.inj hf)

include hp hr he in
theorem univLift_edges_injective (hD : IsConnected D) (hL : IsConnected L)
    (d₀ : D.V) (ht : Pi1Trivial i) :
    Function.Injective (univLift L (pushoutMap p i hiV hiE hiF) (i.onV d₀)).onE := by
  intro e f h
  have hv : e.val.1 = f.val.1 :=
    univLift_vertices_injective p hp a hr he i hiV hiE hiF hD hL d₀ ht
      (congrArg (fun e : UE (pushoutComplex p i hiV hiE)
        ((pushoutMap p i hiV hiE hiF).onV (i.onV d₀)) => e.val.1) h)
  have hs : L.src e.val.2 = L.src f.val.2 :=
    e.property.symm.trans ((congrArg endV hv).trans f.property)
  have hb : e.val.2 = f.val.2 := pushE_injective_at_source p hp i hiV hiE hs
    (congrArg (fun e : UE (pushoutComplex p i hiV hiE)
      ((pushoutMap p i hiV hiE hiF).onV (i.onV d₀)) => e.val.2) h)
  exact Subtype.ext (Prod.ext hv hb)

include hp hr he in
theorem univLift_faces_injective (hD : IsConnected D) (hL : IsConnected L)
    (d₀ : D.V) (ht : Pi1Trivial i) :
    Function.Injective (univLift L (pushoutMap p i hiV hiE hiF) (i.onV d₀)).onF := by
  intro e f h
  have hv : e.val.1 = f.val.1 :=
    univLift_vertices_injective p hp a hr he i hiV hiE hiF hD hL d₀ ht
      (congrArg (fun f : UF (pushoutComplex p i hiV hiE)
        ((pushoutMap p i hiV hiE hiF).onV (i.onV d₀)) => f.val.1) h)
  have hs : L.base e.val.2 = L.base f.val.2 :=
    e.property.symm.trans ((congrArg endV hv).trans f.property)
  have hb : e.val.2 = f.val.2 := pushF_injective_at_base p hp i hiV hiF hs
    (congrArg (fun f : UF (pushoutComplex p i hiV hiE)
      ((pushoutMap p i hiV hiE hiF).onV (i.onV d₀)) => f.val.2) h)
  exact Subtype.ext (Prod.ext hv hb)

end FiniteChains.Comb.PushoutSheets
