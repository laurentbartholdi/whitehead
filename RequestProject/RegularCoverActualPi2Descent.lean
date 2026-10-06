module

public import RequestProject.PushoutActualCycleGeneration
public import RequestProject.Pi2GenerationBaseChange
public import RequestProject.MapChainDescent

@[expose] public section

/-! The geometric generation input for regular-cover descent is now a
theorem. The explicit edge/face compatibility records actual deck maps,
which the older vertex-only `IsRegular` predicate does not encode.
Unverified source. -/

noncomputable section
namespace FiniteChains.Comb
universe u v
variable {D K : Complex2.{u}} {Q : Type v} [Group Q]
  (p : Hom D K) (hp : IsCovering p) (a : DeckAction D Q) (hr : IsRegular p a)
  (he : ∀ q e, p.onE (a.smulE q e) = p.onE e)
  (hf : ∀ q f, p.onF (a.smulF q f) = p.onF f)

include hp in
theorem isConnected_of_covering (hD : IsConnected D) : IsConnected K := by
  intro x y
  obtain ⟨d, rfl⟩ := hp.surjV x
  obtain ⟨e, rfl⟩ := hp.surjV y
  obtain ⟨l, hl⟩ := hD d e
  exact ⟨mapPath p l, isPath_mapPath p hl⟩

include hp hr he hf in
/-- Every genuine two-cycle of every universal cover of the pushout lies
in the span of actual lifted spherical classes from L. -/
theorem regularCover_cycle_mem_pi2FromSub_span
    (hDconn : IsConnected D) (hD : IsAcyclic D) (d₀ : D.V)
    {L : Complex2.{u}} (i : Hom D L)
    (hiV : Function.Injective i.onV) (hiE : Function.Injective i.onE)
    (hiF : Function.Injective i.onF) (hL : IsConnected L) (ht : Pi1Trivial i)
    (x : (pushoutComplex p i hiV hiE).V)
    (c : UF (pushoutComplex p i hiV hiE) x →₀ ℤ)
    (hc : bdry2 (uCover (pushoutComplex p i hiV hiE) x) c = 0) :
    c ∈ Submodule.span ℤ (Pi2FromSub (pushoutMap p i hiV hiE hiF) x) := by
  have hT := isConnected_pushoutComplex p i hiV hiE
    (isConnected_of_covering p hp hDconn) hL d₀
  obtain ⟨l, hl⟩ := hT x ((pushoutMap p i hiV hiE hiF).onV (i.onV d₀))
  apply pi2Generated_changeBase (pushoutMap p i hiV hiE hiF) hl _ c hc
  exact PushoutRelativeCopies.cycle_mem_span_at_core p hp a hr he hf i hiV hiE hiF
    hDconn hL d₀ ht hD hT

include hp hr he hf in
/-- A connected nonempty regular covering supplies the former global
generation hypothesis for this specific covering, with no cycle input. -/
theorem regularCover_pi2GeneratedByUpstairsFor (d₀ : D.V) : Pi2GeneratedByUpstairsFor p := by
  intro L i hiV hiE hiF _ hDconn hD hL ht x c hc
  exact regularCover_cycle_mem_pi2FromSub_span p hp a hr he hf hDconn hD d₀ i
    hiV hiE hiF hL ht x c hc

end FiniteChains.Comb
