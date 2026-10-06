import RequestProject.PushoutFundamentalRetraction
import RequestProject.RegularCoverEdgeLabels
import RequestProject.UniversalCoverPi1Injection

/-! Actual sheet separation in the universal cover of the descent pushout.
The map L→K∪D L identifies old vertices, so fundamental-group injection
alone is insufficient; the regular-cover labels supply the missing test.
No universal-cover embedding hypothesis is assumed. Unverified source. -/

noncomputable section
open scoped Classical

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb
universe u v

namespace EdgeLabels
variable {X : Complex2.{u}} {G : Type v} [Group G]

def vertexRead (w : X.E → G) (hw : ∀ f, read w (X.att f) = 1) (a : X.V) : UV X a → G :=
  Quotient.lift (fun p : PathFrom X a => read w p.val) (fun _ _ h => read_htpy w hw h)

@[simp] theorem vertexRead_mk (w : X.E → G) (hw : ∀ f, read w (X.att f) = 1)
    (a : X.V) (p : PathFrom X a) : vertexRead w hw a (UV.mk p) = read w p.val := rfl
end EdgeLabels

namespace PushoutSheets
variable {D K L : Complex2.{u}} {Q : Type v} [Group Q]
  (p : Hom D K) (hp : IsCovering p) (a : DeckAction D Q) (hr : IsRegular p a)
  (he : ∀ q e, p.onE (a.smulE q e) = p.onE e)
  (i : Hom D L) (hiV : Function.Injective i.onV) (hiE : Function.Injective i.onE)
  (hiF : Function.Injective i.onF)

def potential (v : L.V) : Q := if h : ∃ d, i.onV d = v then
  RegularCoverLabels.sheet p hp a hr h.choose else 1

include hiV in
theorem potential_core (d : D.V) : potential p hp a hr i (i.onV d) =
    RegularCoverLabels.sheet p hp a hr d := by
  have h : ∃ e, i.onV e = i.onV d := ⟨d, rfl⟩
  simp only [potential, dif_pos h, hiV h.choose_spec]

def labels : (pushoutComplex p i hiV hiE).E → Q
  | Sum.inl e => RegularCoverLabels.edge p hp a hr e
  | Sum.inr e => (potential p hp a hr i (L.src e.val))⁻¹ * potential p hp a hr i (L.tgt e.val)

include he in
theorem labels_pushE (e : L.E) : labels p hp a hr i hiV hiE (pushE p i e) =
    (potential p hp a hr i (L.src e))⁻¹ * potential p hp a hr i (L.tgt e) := by
  by_cases h : ∃ d, i.onE d = e
  · obtain ⟨d, rfl⟩ := h
    rw [pushE_of_mem p hiE]
    change RegularCoverLabels.edge p hp a hr (p.onE d) = _
    rw [i.src_onE, i.tgt_onE, potential_core p hp a hr i hiV,
      potential_core p hp a hr i hiV]
    exact RegularCoverLabels.edge_projection p hp a hr he d
  · rw [pushE_of_off p i ⟨e, fun d hd => h ⟨d, hd⟩⟩]
    rfl

include he in
theorem read_pushPath {l : List (L.E × Bool)} {v w : L.V}
    (hl : IsPath L.src L.tgt l v w) :
    EdgeLabels.read (labels p hp a hr i hiV hiE)
      (mapPath (pushoutMap p i hiV hiE hiF) l) =
      (potential p hp a hr i v)⁻¹ * potential p hp a hr i w := by
  rw [EdgeLabels.read_mapPath]
  exact EdgeLabels.read_potential _ (potential p hp a hr i)
    (labels_pushE p hp a hr he i hiV hiE) hl

include he hiF in
theorem labels_rel (f : (pushoutComplex p i hiV hiE).F) :
    EdgeLabels.read (labels p hp a hr i hiV hiE) ((pushoutComplex p i hiV hiE).att f) = 1 := by
  cases f with
  | inl f =>
      change EdgeLabels.read _ (mapPath (pushoutInl p i hiV hiE) (K.att f)) = 1
      rw [EdgeLabels.read_mapPath]
      exact RegularCoverLabels.edge_rel p hp a hr he f
  | inr f =>
      have h := read_pushPath p hp a hr he i hiV hiE hiF (L.att_isLoop f.val)
      simpa only [inv_mul_cancel, pushoutComplex, pushoutMap, mapPath, Sum.elim_inr] using h

include hiV in
/-- An old vertex is determined by its projected vertex together with its
actual deck coordinate. Off-core vertices already retain their labels. -/
theorem pushV_potential_injective {v w : L.V}
    (hv : pushV p i v = pushV p i w)
    (hs : potential p hp a hr i v = potential p hp a hr i w) : v = w := by
  by_cases hvD : ∃ d, i.onV d = v
  · obtain ⟨d, rfl⟩ := hvD
    rw [pushV_of_mem p hiV] at hv
    by_cases hwD : ∃ e, i.onV e = w
    · obtain ⟨e, rfl⟩ := hwD
      rw [pushV_of_mem p hiV] at hv
      rw [potential_core p hp a hr i hiV, potential_core p hp a hr i hiV] at hs
      exact congrArg i.onV (RegularCoverLabels.sheet_fibre_injective p hp a hr
        (Sum.inl.inj hv) hs)
    · rw [pushV_of_off p i ⟨w, fun e he => hwD ⟨e, he⟩⟩] at hv
      exact (Sum.inl_ne_inr hv).elim
  · rw [pushV_of_off p i ⟨v, fun d hd => hvD ⟨d, hd⟩⟩] at hv
    by_cases hwD : ∃ e, i.onV e = w
    · obtain ⟨e, rfl⟩ := hwD
      rw [pushV_of_mem p hiV] at hv
      exact (Sum.inr_ne_inl hv).elim
    · rw [pushV_of_off p i ⟨w, fun e he => hwD ⟨e, he⟩⟩] at hv
      exact congrArg (fun x : OffV i => x.val) (Sum.inr.inj hv)

theorem read_univLift (v₀ : L.V) (v : UV L v₀) :
    EdgeLabels.vertexRead (labels p hp a hr i hiV hiE)
      (labels_rel p hp a hr he i hiV hiE hiF) (pushV p i v₀)
      (univLiftV v₀ (pushoutMap p i hiV hiE hiF) v) =
      (potential p hp a hr i v₀)⁻¹ * potential p hp a hr i (endV v) := by
  induction v using UV.ind with
  | h l => exact read_pushPath p hp a hr he i hiV hiE hiF l.property

include hp hr he in
theorem univLift_endpoint_reflect (v₀ : L.V) {v w : UV L v₀}
    (h : univLiftV v₀ (pushoutMap p i hiV hiE hiF) v =
      univLiftV v₀ (pushoutMap p i hiV hiE hiF) w) : endV v = endV w := by
  apply pushV_potential_injective p hp a hr i hiV
  · have hv := congrArg endV h
    simpa only [endV_univLiftV, pushoutMap] using hv
  · have hv := congrArg (EdgeLabels.vertexRead (labels p hp a hr i hiV hiE)
      (labels_rel p hp a hr he i hiV hiE hiF) (pushV p i v₀)) h
    rw [read_univLift p hp a hr he i hiV hiE hiF v₀ v,
      read_univLift p hp a hr he i hiV hiE hiF v₀ w] at hv
    exact mul_left_cancel hv

include hp hr he in
theorem univLift_vertices_injective (hD : IsConnected D) (hL : IsConnected L)
    (d₀ : D.V) (ht : Pi1Trivial i) :
    Function.Injective (univLiftV (i.onV d₀) (pushoutMap p i hiV hiE hiF)) := by
  intro v w h
  have hv := univLift_endpoint_reflect p hp a hr he i hiV hiE hiF (i.onV d₀) h
  obtain ⟨g, hg, _⟩ := (isRegular_univProj (X := L) (x₀ := i.onV d₀)).simply_transitive v w hv
  change deckV g v = w at hg
  have hfix : deckV (pi1Map (pushoutMap p i hiV hiE hiF) (i.onV d₀) g)
      (univLiftV (i.onV d₀) (pushoutMap p i hiV hiE hiF) v) =
      univLiftV (i.onV d₀) (pushoutMap p i hiV hiE hiF) v := by
    rw [← univLiftV_deckV, hg, h]
  have hgone : g = 1 := PushoutFundamental.pi1_pushoutMap_injective p i hiV hiE hiF hD hL d₀ ht
    ((deckV_free _ _ _ hfix).trans (map_one _).symm)
  rw [hgone, deckV_one] at hg
  exact hg

end PushoutSheets
end FiniteChains.Comb
