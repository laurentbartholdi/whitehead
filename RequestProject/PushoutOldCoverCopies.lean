module

public import RequestProject.PushoutOldCoverAcyclic

@[expose] public section

/-! The actual old copies cover every old cell. Two copies meeting at a
vertex agree after a genuine deck transformation of D, on all cells.
These facts supply the component partition for supported descent chains.
Unverified source. -/

noncomputable section
open scoped Classical

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb.PushoutOldCover
universe u v
variable {D K L : Complex2.{u}} {Q : Type v} [Group Q]
  (p : Hom D K) (hp : IsCovering p) (a : DeckAction D Q) (hr : IsRegular p a)
  (he : ∀ q e, p.onE (a.smulE q e) = p.onE e)
  (hf : ∀ q f, p.onF (a.smulF q f) = p.onF f)
  (i : Hom D L) (hiV : Function.Injective i.onV) (hiE : Function.Injective i.onE)
  (hiF : Function.Injective i.onF) (hconn : IsConnected D) (d₀ : D.V) (ht : Pi1Trivial i)

theorem translated_projection_V
    (g : Pi1 (pushoutComplex p i hiV hiE) (Sum.inl (p.onV d₀))) (d : D.V) :
    endV ((translatedOldLift p i hiV hiE hiF hconn d₀ ht g).onV d) = Sum.inl (p.onV d) := by
  change endV (deckV g (liftV (oldMap p i hiV hiE) hconn d₀ d)) = _
  rw (config := { transparency := .default }) [endV_deckV, endV_liftV]
  rfl

theorem translated_projection_E
    (g : Pi1 (pushoutComplex p i hiV hiE) (Sum.inl (p.onV d₀))) (d : D.E) :
    ((translatedOldLift p i hiV hiE hiF hconn d₀ ht g).onE d).val.2 = Sum.inl (p.onE d) := rfl

theorem translated_projection_F
    (g : Pi1 (pushoutComplex p i hiV hiE) (Sum.inl (p.onV d₀))) (d : D.F) :
    ((translatedOldLift p i hiV hiE hiF hconn d₀ ht g).onF d).val.2 = Sum.inl (p.onF d) := rfl

include hp in
theorem old_vertices_covered
    (v : UV (pushoutComplex p i hiV hiE) (Sum.inl (p.onV d₀))) (k : K.V)
    (hv : endV v = Sum.inl k) :
    ∃ g d, (translatedOldLift p i hiV hiE hiF hconn d₀ ht g).onV d = v := by
  obtain ⟨d, hd⟩ := hp.surjV k
  have hend : endV ((oldLift p i hiV hiE hiF hconn d₀ ht).onV d) = endV v := by
    rw (config := { transparency := .default }) [hv]
    change endV (liftV (oldMap p i hiV hiE) hconn d₀ d) = Sum.inl k
    rw (config := { transparency := .default }) [endV_liftV]
    exact congrArg Sum.inl hd
  obtain ⟨g, hg, _⟩ := (isRegular_univProj (X := pushoutComplex p i hiV hiE)
    (x₀ := Sum.inl (p.onV d₀))).simply_transitive
      ((oldLift p i hiV hiE hiF hconn d₀ ht).onV d) v hend
  exact ⟨g, d, hg⟩

include hp in
theorem old_edges_covered
    (e : UE (pushoutComplex p i hiV hiE) (Sum.inl (p.onV d₀))) (k : K.E)
    (he' : e.val.2 = Sum.inl k) :
    ∃ g d, (translatedOldLift p i hiV hiE hiF hconn d₀ ht g).onE d = e := by
  have hv : endV e.val.1 = Sum.inl (K.src k) := by rw (config := { transparency := .default }) [e.property, he']; rfl
  obtain ⟨g, d, hd⟩ := old_vertices_covered p hp i hiV hiE hiF hconn d₀ ht e.val.1 (K.src k) hv
  have hsrc : K.src k = p.onV d := by
    have h := translated_projection_V p i hiV hiE hiF hconn d₀ ht g d
    rw (config := { transparency := .default }) [hd, hv] at h
    exact Sum.inl.inj h
  obtain ⟨l, ⟨hl, hlp⟩, _⟩ := exists_unique_liftGerm hp d (eb := (k, true)) hsrc
  have hb : l.2 = true := congrArg Prod.snd hlp
  have hs : D.src l.1 = d := by simpa only [germSrc, hb, if_true] using hl
  refine ⟨g, l.1, Subtype.ext (Prod.ext ?_ ?_)⟩
  · have h := (translatedOldLift p i hiV hiE hiF hconn d₀ ht g).src_onE l.1
    exact h.trans ((congrArg _ hs).trans hd)
  · rw (config := { transparency := .default }) [translated_projection_E, he']
    exact congrArg Sum.inl (congrArg Prod.fst hlp)

include hp in
theorem old_faces_covered
    (f : UF (pushoutComplex p i hiV hiE) (Sum.inl (p.onV d₀))) (k : K.F)
    (hf' : f.val.2 = Sum.inl k) :
    ∃ g d, (translatedOldLift p i hiV hiE hiF hconn d₀ ht g).onF d = f := by
  have hv : endV f.val.1 = Sum.inl (K.base k) := by rw (config := { transparency := .default }) [f.property, hf']; rfl
  obtain ⟨g, d, hd⟩ := old_vertices_covered p hp i hiV hiE hiF hconn d₀ ht f.val.1 (K.base k) hv
  have hbase : K.base k = p.onV d := by
    have h := translated_projection_V p i hiV hiE hiF hconn d₀ ht g d
    rw (config := { transparency := .default }) [hd, hv] at h
    exact Sum.inl.inj h
  obtain ⟨l, ⟨hlp, hl⟩, _⟩ := exists_unique_liftCell hp k hbase
  refine ⟨g, l, Subtype.ext (Prod.ext ?_ ?_)⟩
  · have h := (translatedOldLift p i hiV hiE hiF hconn d₀ ht g).base_onF l
    exact h.trans ((congrArg _ hl).trans hd)
  · rw (config := { transparency := .default }) [translated_projection_F, hf']
    exact congrArg Sum.inl hlp

include hr he hf in
/-- Overlap is an actual deck identification of D, not an arbitrary
identification of chains. -/
theorem copies_identified_of_meet
    (hEconn : IsConnected (pushoutComplex p i hiV hiE))
    (g h : Pi1 (pushoutComplex p i hiV hiE) (Sum.inl (p.onV d₀)))
    (d e : D.V)
    (hmeet : (translatedOldLift p i hiV hiE hiF hconn d₀ ht g).onV d =
      (translatedOldLift p i hiV hiE hiF hconn d₀ ht h).onV e) :
    ∃ q : Q,
      (∀ v, (translatedOldLift p i hiV hiE hiF hconn d₀ ht g).onV v =
        (translatedOldLift p i hiV hiE hiF hconn d₀ ht h).onV (a.smulV q v)) ∧
      (∀ l, (translatedOldLift p i hiV hiE hiF hconn d₀ ht g).onE l =
        (translatedOldLift p i hiV hiE hiF hconn d₀ ht h).onE (a.smulE q l)) ∧
      (∀ f, (translatedOldLift p i hiV hiE hiF hconn d₀ ht g).onF f =
        (translatedOldLift p i hiV hiE hiF hconn d₀ ht h).onF (a.smulF q f)) := by
  have hpde : p.onV d = p.onV e := by
    have h' := congrArg endV hmeet
    rw (config := { transparency := .default }) [translated_projection_V, translated_projection_V] at h'
    exact Sum.inl.inj h'
  obtain ⟨q, hq, _⟩ := hr.simply_transitive d e hpde
  let F := translatedOldLift p i hiV hiE hiF hconn d₀ ht g
  let G := (translatedOldLift p i hiV hiE hiF hconn d₀ ht h).comp (a.cellHom q)
  have hE : ∀ l, (univProj (pushoutComplex p i hiV hiE) (Sum.inl (p.onV d₀))).onE (F.onE l) =
      (univProj (pushoutComplex p i hiV hiE) (Sum.inl (p.onV d₀))).onE (G.onE l) := by
    intro l
    change Sum.inl (p.onE l) = Sum.inl (p.onE (a.smulE q l))
    rw (config := { transparency := .default }) [he]
  have hF : ∀ l, (univProj (pushoutComplex p i hiV hiE) (Sum.inl (p.onV d₀))).onF (F.onF l) =
      (univProj (pushoutComplex p i hiV hiE) (Sum.inl (p.onV d₀))).onF (G.onF l) := by
    intro l
    change Sum.inl (p.onF l) = Sum.inl (p.onF (a.smulF q l))
    rw (config := { transparency := .default }) [hf]
  have hb : F.onV d = G.onV d := by
    change _ = (translatedOldLift p i hiV hiE hiF hconn d₀ ht h).onV (a.smulV q d)
    rw (config := { transparency := .default }) [hq]
    exact hmeet
  have hV := lift_onV_eq (isCovering_univProj (X := pushoutComplex p i hiV hiE)
    (x₀ := Sum.inl (p.onV d₀)) hEconn) hconn hE hb
  exact ⟨q, hV, lift_onE_eq (isCovering_univProj (X := pushoutComplex p i hiV hiE)
    (x₀ := Sum.inl (p.onV d₀)) hEconn) hE hV,
    lift_onF_eq (isCovering_univProj (X := pushoutComplex p i hiV hiE)
      (x₀ := Sum.inl (p.onV d₀)) hEconn) hF hV⟩

end FiniteChains.Comb.PushoutOldCover
