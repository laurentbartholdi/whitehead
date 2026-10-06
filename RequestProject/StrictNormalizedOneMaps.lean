module

public import RequestProject.NormalizedStrictBoundary

@[expose] public section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb.StrictNormalized
universe u
variable {P Q R : Type u} [PartialOrder P] [PartialOrder Q] [PartialOrder R]

/-- The normalized strict edge-chain map of an arbitrary monotone map. -/
noncomputable def mapOne (f : P → Q) (hf : Monotone f) :
    (StrictOrdEdge P →₀ ℤ) →ₗ[ℤ] (StrictOrdEdge Q →₀ ℤ) :=
  normalizeOrdChain1.comp ((chain1 (orderCxMap f hf)).comp (chain1 (strictOrderIncl P)))

theorem mapOne_single (f : P → Q) (hf : Monotone f) (e : StrictOrdEdge P) (n : ℤ) :
    mapOne f hf (Finsupp.single e n) =
      n • normalizeOrdEdge ⟨(f e.1.1, f e.1.2), hf e.2.le⟩ := by
  change normalizeOrdChain1 (Finsupp.mapDomain (orderCxMap f hf).onE
    (Finsupp.mapDomain (strictOrderIncl P).onE (Finsupp.single e n))) = _
  rw [Finsupp.mapDomain_single, Finsupp.mapDomain_single, normalizeOrdChain1_single]
  rfl

theorem mapOne_strict (f : P → Q) (hf : StrictMono f) (c : StrictOrdEdge P →₀ ℤ) :
    mapOne f hf.monotone c = chain1 (strictOrderCxMap f hf) c := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, hc, hd]
  | single e n =>
    rw [mapOne_single]
    simp [normalizeOrdEdge, (hf e.2).ne, chain1, strictOrderCxMap]

theorem mapOne_id (c : StrictOrdEdge P →₀ ℤ) : mapOne id monotone_id c = c :=
  normalizedStrictChain1_id c

theorem mapOne_comp (f : P → Q) (hf : Monotone f) (g : Q → R) (hg : Monotone g)
    (c : StrictOrdEdge P →₀ ℤ) :
    mapOne g hg (mapOne f hf c) = mapOne (g ∘ f) (hg.comp hf) c := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, hc, hd]
  | single e n =>
    rw [mapOne_single, map_smul]
    by_cases h : f e.1.1 = f e.1.2
    · simp [normalizeOrdEdge, h, mapOne_single, Function.comp_def]
    · rw [show normalizeOrdEdge (⟨(f e.1.1, f e.1.2), hf e.2.le⟩ : OrdEdge Q) =
        Finsupp.single ⟨(f e.1.1, f e.1.2), lt_of_le_of_ne (hf e.2.le) h⟩ 1 by
          simp [normalizeOrdEdge, h]]
      rw [mapOne_single, one_smul, mapOne_single]
      rfl

theorem mapOne_boundary (f : P → Q) (hf : Monotone f) (c : StrictOrdEdge P →₀ ℤ) :
    bdry1 (strictOrderCx Q) (mapOne f hf c) =
      Finsupp.mapDomain f (bdry1 (strictOrderCx P) c) := by
  change bdry1 (strictOrderCx Q)
    (normalizeOrdChain1 (chain1 (orderCxMap f hf) (chain1 (strictOrderIncl P) c))) = _
  rw [bdry1_normalizeOrdChain1, bdry1_chain1, bdry1_chain1]
  change Finsupp.mapDomain f (Finsupp.mapDomain id _) = _
  rw [Finsupp.mapDomain_id]

theorem mapTwo_boundary (f : P → Q) (hf : Monotone f) (c : StrictOrdTri P →₀ ℤ) :
    bdry2 (strictOrderCx Q) (normalizedStrictChain2 f hf c) =
      mapOne f hf (bdry2 (strictOrderCx P) c) := by
  change bdry2 (strictOrderCx Q)
    (normalizeOrdChain2 (chain2 (orderCxMap f hf) (chain2 (strictOrderIncl P) c))) = _
  rw [bdry2_normalizeOrdChain2, bdry2_chain2, bdry2_chain2]
  rfl

/-- Exact naturality of normalization under a strict change of coordinates. -/
theorem mapOne_semiconj (e : P → Q) (he : StrictMono e)
    (g : P → P) (hg : Monotone g) (h : Q → Q) (hh : Monotone h)
    (hs : ∀ x, e (g x) = h (e x)) (c : StrictOrdEdge P →₀ ℤ) :
    chain1 (strictOrderCxMap e he) (normalizedStrictChain1 g hg c) =
      normalizedStrictChain1 h hh (chain1 (strictOrderCxMap e he) c) := by
  change chain1 (strictOrderCxMap e he) (mapOne g hg c) =
    mapOne h hh (chain1 (strictOrderCxMap e he) c)
  rw [← mapOne_strict e he, ← mapOne_strict e he, mapOne_comp, mapOne_comp]
  have heq : e ∘ g = h ∘ e := funext hs
  have mapEq (f g : P → Q) (hf : Monotone f) (hg : Monotone g) (he : f = g) :
      mapOne f hf c = mapOne g hg c := by
    subst g
    rfl
  exact mapEq _ _ _ _ heq

end FiniteChains.Comb.StrictNormalized
