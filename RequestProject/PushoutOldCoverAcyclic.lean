module

public import RequestProject.PushoutUniversalEmbedding
public import RequestProject.ZeroPi2Descent
public import RequestProject.CellularChainMapZero
public import RequestProject.DeckChainTransport

@[expose] public section

/-! Genuine copies of the acyclic cover inside the universal cover of
K∪D L, with explicit supported H1 fillings and H2 vanishing. The same
statements hold after every actual deck translation. Unverified source. -/

noncomputable section
open scoped Classical

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb
universe u v

section EmbeddedHomology
variable {D X : Complex2.{u}} (f : Hom D X)
  (hV : Function.Injective f.onV) (hE : Function.Injective f.onE)
  (hF : Function.Injective f.onF) (hD : IsAcyclic D)

include hV hE hD in
theorem embedded_one_cycle_filling (z : X.E →₀ ℤ)
    (hs : ∀ e ∉ Set.range f.onE, z e = 0) (hz : bdry1 X z = 0) :
    ∃ y : X.F →₀ ℤ, (∀ g ∉ Set.range f.onF, y g = 0) ∧ bdry2 X y = z := by
  obtain ⟨c, rfl⟩ := (Finsupp.mem_range_mapDomain_iff f.onE hE z).mpr hs
  change bdry1 X (chain1 f c) = 0 at hz
  have hc : bdry1 D c = 0 := by
    apply Finsupp.mapDomain_injective hV
    change chain0 f (bdry1 D c) = Finsupp.mapDomain f.onV 0
    rw [← bdry1_chain1, hz]
    rfl
  obtain ⟨d, hd⟩ := hD.h1 c hc
  refine ⟨chain2 f d, ?_, ?_⟩
  · intro g hg
    exact Finsupp.mapDomain_notin_range d g hg
  · rw [bdry2_chain2, hd]
    rfl

include hE hF hD in
theorem embedded_two_cycle_zero (z : X.F →₀ ℤ)
    (hs : ∀ e ∉ Set.range f.onF, z e = 0) (hz : bdry2 X z = 0) : z = 0 := by
  obtain ⟨c, rfl⟩ := (Finsupp.mem_range_mapDomain_iff f.onF hF z).mpr hs
  change bdry2 X (chain2 f c) = 0 at hz
  have hc : bdry2 D c = 0 := by
    apply Finsupp.mapDomain_injective hE
    change chain1 f (bdry2 D c) = Finsupp.mapDomain f.onE 0
    rw [← bdry2_chain2, hz]
    rfl
  have hc0 : c = 0 := hD.h2 (hc.trans (map_zero _).symm)
  rw [hc0, Finsupp.mapDomain_zero]
end EmbeddedHomology

namespace PushoutOldCover
variable {D K L : Complex2.{u}} {Q : Type v} [Group Q]
  (p : Hom D K) (hp : IsCovering p) (a : DeckAction D Q) (hr : IsRegular p a)
  (he : ∀ q e, p.onE (a.smulE q e) = p.onE e)
  (i : Hom D L) (hiV : Function.Injective i.onV) (hiE : Function.Injective i.onE)
  (hiF : Function.Injective i.onF) (hconn : IsConnected D) (d₀ : D.V) (ht : Pi1Trivial i)

def oldMap : Hom D (pushoutComplex p i hiV hiE) := (pushoutInl p i hiV hiE).comp p

include hiF ht in
theorem oldMap_pi1Trivial : Pi1Trivial (oldMap p i hiV hiE) := by
  change Pi1Trivial ((pushoutInl p i hiV hiE).comp p)
  rw [← pushout_comm p i hiV hiE hiF]
  exact Pi1Trivial.comp_left _ ht

def oldLift : Hom D (uCover (pushoutComplex p i hiV hiE) (Sum.inl (p.onV d₀))) :=
  liftHom (f := oldMap p i hiV hiE) (d₀ := d₀) hconn
    (oldMap_pi1Trivial p i hiV hiE hiF ht)

theorem oldLift_read (d : D.V) :
    EdgeLabels.vertexRead (PushoutSheets.labels p hp a hr i hiV hiE)
      (PushoutSheets.labels_rel p hp a hr he i hiV hiE hiF) (Sum.inl (p.onV d₀))
      ((oldLift p i hiV hiE hiF hconn d₀ ht).onV d) =
      (RegularCoverLabels.sheet p hp a hr d₀)⁻¹ * RegularCoverLabels.sheet p hp a hr d := by
  change EdgeLabels.read (PushoutSheets.labels p hp a hr i hiV hiE)
    (mapPath (oldMap p i hiV hiE) (cPath hconn d₀ d)) = _
  rw [oldMap, ← mapPath_comp, EdgeLabels.read_mapPath]
  exact RegularCoverLabels.read_projected_path p hp a hr he (cPath_isPath hconn d₀ d)

include hp hr he in
theorem oldLift_injective_V : Function.Injective (oldLift p i hiV hiE hiF hconn d₀ ht).onV := by
  intro d e h
  have hv : p.onV d = p.onV e := by
    have h' := congrArg endV h
    change endV (liftV (oldMap p i hiV hiE) hconn d₀ d) =
      endV (liftV (oldMap p i hiV hiE) hconn d₀ e) at h'
    rw [endV_liftV, endV_liftV] at h'
    exact Sum.inl.inj h'
  have hs := congrArg (EdgeLabels.vertexRead (PushoutSheets.labels p hp a hr i hiV hiE)
    (PushoutSheets.labels_rel p hp a hr he i hiV hiE hiF) (Sum.inl (p.onV d₀))) h
  rw [oldLift_read p hp a hr he i hiV hiE hiF hconn d₀ ht d,
    oldLift_read p hp a hr he i hiV hiE hiF hconn d₀ ht e] at hs
  exact RegularCoverLabels.sheet_fibre_injective p hp a hr hv (mul_left_cancel hs)

include hp hr he in
theorem oldLift_injective_E : Function.Injective (oldLift p i hiV hiE hiF hconn d₀ ht).onE := by
  intro e f h
  have hs : D.src e = D.src f := oldLift_injective_V p hp a hr he i hiV hiE hiF hconn d₀ ht
    (congrArg (fun e : UE (pushoutComplex p i hiV hiE) (Sum.inl (p.onV d₀)) => e.val.1) h)
  have hp' : p.onE e = p.onE f := Sum.inl.inj
    (congrArg (fun e : UE (pushoutComplex p i hiV hiE) (Sum.inl (p.onV d₀)) => e.val.2) h)
  have hg := liftGerm_unique hp (x := (e, true)) (y := (f, true)) rfl hs.symm
    (congrArg (fun e => (e, true)) hp')
  exact congrArg Prod.fst hg

include hp hr he in
theorem oldLift_injective_F : Function.Injective (oldLift p i hiV hiE hiF hconn d₀ ht).onF := by
  intro e f h
  have hs : D.base e = D.base f := oldLift_injective_V p hp a hr he i hiV hiE hiF hconn d₀ ht
    (congrArg (fun e : UF (pushoutComplex p i hiV hiE) (Sum.inl (p.onV d₀)) => e.val.1) h)
  have hp' : p.onF e = p.onF f := Sum.inl.inj
    (congrArg (fun e : UF (pushoutComplex p i hiV hiE) (Sum.inl (p.onV d₀)) => e.val.2) h)
  apply hp.cell.1
  exact Subtype.ext (Prod.ext hp' hs)

def translatedOldLift (g : Pi1 (pushoutComplex p i hiV hiE) (Sum.inl (p.onV d₀))) :
    Hom D (uCover (pushoutComplex p i hiV hiE) (Sum.inl (p.onV d₀))) :=
  ((univDeck _ _).cellHom g).comp (oldLift p i hiV hiE hiF hconn d₀ ht)

include hp hr he in
theorem translatedOldLift_injective_V (g : Pi1 (pushoutComplex p i hiV hiE) (Sum.inl (p.onV d₀))) :
    Function.Injective (translatedOldLift p i hiV hiE hiF hconn d₀ ht g).onV := by
  intro x y h
  apply oldLift_injective_V p hp a hr he i hiV hiE hiF hconn d₀ ht
  have h' := congrArg (deckV g⁻¹) h
  change deckV g⁻¹ (deckV g ((oldLift p i hiV hiE hiF hconn d₀ ht).onV x)) =
    deckV g⁻¹ (deckV g ((oldLift p i hiV hiE hiF hconn d₀ ht).onV y)) at h'
  simpa only [← deckV_mul, inv_mul_cancel, deckV_one] using h'

include hp hr he in
theorem translatedOldLift_injective_E (g : Pi1 (pushoutComplex p i hiV hiE) (Sum.inl (p.onV d₀))) :
    Function.Injective (translatedOldLift p i hiV hiE hiF hconn d₀ ht g).onE := by
  intro x y h
  apply oldLift_injective_E p hp a hr he i hiV hiE hiF hconn d₀ ht
  have h' := congrArg ((univDeck (pushoutComplex p i hiV hiE) (Sum.inl (p.onV d₀))).smulE g⁻¹) h
  change (univDeck (pushoutComplex p i hiV hiE) (Sum.inl (p.onV d₀))).smulE g⁻¹
      ((univDeck (pushoutComplex p i hiV hiE) (Sum.inl (p.onV d₀))).smulE g
        ((oldLift p i hiV hiE hiF hconn d₀ ht).onE x)) =
    (univDeck (pushoutComplex p i hiV hiE) (Sum.inl (p.onV d₀))).smulE g⁻¹
      ((univDeck (pushoutComplex p i hiV hiE) (Sum.inl (p.onV d₀))).smulE g
        ((oldLift p i hiV hiE hiF hconn d₀ ht).onE y)) at h'
  simpa only [← DeckAction.mul_smulE, inv_mul_cancel, DeckAction.one_smulE] using h'

include hp hr he in
theorem translatedOldLift_injective_F (g : Pi1 (pushoutComplex p i hiV hiE) (Sum.inl (p.onV d₀))) :
    Function.Injective (translatedOldLift p i hiV hiE hiF hconn d₀ ht g).onF := by
  intro x y h
  apply oldLift_injective_F p hp a hr he i hiV hiE hiF hconn d₀ ht
  have h' := congrArg ((univDeck (pushoutComplex p i hiV hiE) (Sum.inl (p.onV d₀))).smulF g⁻¹) h
  change (univDeck (pushoutComplex p i hiV hiE) (Sum.inl (p.onV d₀))).smulF g⁻¹
      ((univDeck (pushoutComplex p i hiV hiE) (Sum.inl (p.onV d₀))).smulF g
        ((oldLift p i hiV hiE hiF hconn d₀ ht).onF x)) =
    (univDeck (pushoutComplex p i hiV hiE) (Sum.inl (p.onV d₀))).smulF g⁻¹
      ((univDeck (pushoutComplex p i hiV hiE) (Sum.inl (p.onV d₀))).smulF g
        ((oldLift p i hiV hiE hiF hconn d₀ ht).onF y)) at h'
  simpa only [← DeckAction.mul_smulF, inv_mul_cancel, DeckAction.one_smulF] using h'

include hp hr he in
theorem translated_old_one_cycle_filling (hD : IsAcyclic D)
    (g : Pi1 (pushoutComplex p i hiV hiE) (Sum.inl (p.onV d₀)))
    (z : (uCover (pushoutComplex p i hiV hiE) (Sum.inl (p.onV d₀))).E →₀ ℤ)
    (hs : ∀ e ∉ Set.range (translatedOldLift p i hiV hiE hiF hconn d₀ ht g).onE, z e = 0)
    (hz : bdry1 (uCover (pushoutComplex p i hiV hiE) (Sum.inl (p.onV d₀))) z = 0) :
    ∃ y : (uCover (pushoutComplex p i hiV hiE) (Sum.inl (p.onV d₀))).F →₀ ℤ,
      (∀ f ∉ Set.range (translatedOldLift p i hiV hiE hiF hconn d₀ ht g).onF, y f = 0) ∧
        bdry2 (uCover (pushoutComplex p i hiV hiE) (Sum.inl (p.onV d₀))) y = z :=
  embedded_one_cycle_filling (translatedOldLift p i hiV hiE hiF hconn d₀ ht g)
    (translatedOldLift_injective_V p hp a hr he i hiV hiE hiF hconn d₀ ht g)
    (translatedOldLift_injective_E p hp a hr he i hiV hiE hiF hconn d₀ ht g) hD z hs hz

include hp hr he in
theorem translated_old_two_cycle_zero (hD : IsAcyclic D)
    (g : Pi1 (pushoutComplex p i hiV hiE) (Sum.inl (p.onV d₀)))
    (z : (uCover (pushoutComplex p i hiV hiE) (Sum.inl (p.onV d₀))).F →₀ ℤ)
    (hs : ∀ f ∉ Set.range (translatedOldLift p i hiV hiE hiF hconn d₀ ht g).onF, z f = 0)
    (hz : bdry2 (uCover (pushoutComplex p i hiV hiE) (Sum.inl (p.onV d₀))) z = 0) : z = 0 :=
  embedded_two_cycle_zero (translatedOldLift p i hiV hiE hiF hconn d₀ ht g)
    (translatedOldLift_injective_E p hp a hr he i hiV hiE hiF hconn d₀ ht g)
    (translatedOldLift_injective_F p hp a hr he i hiV hiE hiF hconn d₀ ht g) hD z hs hz

end PushoutOldCover
end FiniteChains.Comb
