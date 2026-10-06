module

public import RequestProject.IsoGeneration
public import RequestProject.IdentityCover

@[expose] public section

/-!
# Theorem A for a finite connected *acyclic* two-complex

The paper closes the proof of `(2) ⇒ (1)` with the remark that when `K` is finite and acyclic
one may take `D = K` with the identity covering.  In that case the descent of
Proposition 3.11 is an isomorphism, so the generation statement (3.5) — the one homotopical
input of Proposition 3.11 which is still unproved in general — is available
(`FiniteChains.Comb.pi2GeneratedByUpstairsFor_of_bijective`).

Consequently, **for a finite connected acyclic two-complex the reverse implication of
Theorem A follows from the extension step of Lemmas 3.1, 3.9, 3.10 alone**:

* `FiniteChains.Comb.pi2GeneratedByUpstairsFor_id` — the generation statement (3.5) for the
  identity covering;
* `FiniteChains.Comb.hasMapChains_of_mapStep_of_isAcyclic` — from the extension step, a finite
  connected acyclic complex carries strictly increasing chains of every length whose
  inclusions are zero on `π₂`;
* `FiniteChains.Comb.theoremA_maps_of_isAcyclic` — Theorem A for such a complex, with
  condition (1) in its faithful, map-carrying form.
-/

namespace FiniteChains
namespace Comb

universe u

/-- **The generation statement (3.5) for the identity covering.** -/
theorem pi2GeneratedByUpstairsFor_id (K : Complex2.{u}) :
    Pi2GeneratedByUpstairsFor (Hom.id K) :=
  pi2GeneratedByUpstairsFor_of_bijective (Hom.id K) Function.bijective_id Function.bijective_id
    Function.bijective_id

/-- **Condition (1) of Theorem A for a finite connected acyclic complex, from the extension
step alone.**  Taking `D = K` with the identity covering, the descended chain of
Proposition 3.11 is the chain upstairs, and the generation statement (3.5) is a theorem. -/
theorem hasMapChains_of_mapStep_of_isAcyclic (hstep : MapStep.{u}) {K : Complex2.{u}}
    [Finite K.E] [Finite K.F] (hconn : IsConnected K) (hacyc : IsAcyclic K) (x₀ : K.V) :
    HasMapChains K := by
  intro n
  obtain ⟨c, ⟨R⟩⟩ := hstep K hacyc hconn (n + 1)
  exact ⟨strictTopChain_of_relChainW R (Hom.id K) (isCovering_id K) hacyc hconn inferInstance
    inferInstance x₀ (pi2GeneratedByUpstairsFor_id K)⟩

/-- **Theorem A for a finite connected acyclic two-complex**, with condition (1) in its
faithful, map-carrying form: both sides hold, the reverse implication needing only the
extension step of Lemmas 3.1, 3.9, 3.10. -/
theorem theoremA_maps_of_isAcyclic (hstep : MapStep.{u}) {K : Complex2.{u}} [Finite K.E]
    [Finite K.F] (hconn : IsConnected K) (hacyc : IsAcyclic K) (x₀ : K.V) :
    HasMapChains K ↔ HasAcyclicRegularCover K :=
  ⟨fun _ => hasAcyclicRegularCover_of_isAcyclic hconn hacyc,
    fun _ => hasMapChains_of_mapStep_of_isAcyclic hstep hconn hacyc x₀⟩

end Comb
end FiniteChains
