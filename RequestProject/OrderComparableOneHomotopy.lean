import RequestProject.OrderNerveOneDictionary

/-! Genuine finite triangle fillings for two-leg order contractions in degree one. -/
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb
universe u
variable {P : Type u} [PartialOrder P]

noncomputable def normalizedStrictChain1 (g : P → P) (hg : Monotone g) :
    (StrictOrdEdge P →₀ ℤ) →ₗ[ℤ] (StrictOrdEdge P →₀ ℤ) :=
  normalizeOrdChain1.comp ((chain1 (orderCxMap g hg)).comp (chain1 (strictOrderIncl P)))

theorem normalizedStrictChain1_single (g : P → P) (hg : Monotone g)
    (e : StrictOrdEdge P) (n : ℤ) :
    normalizedStrictChain1 g hg (Finsupp.single e n) =
      n • normalizeOrdEdge ⟨(g e.1.1, g e.1.2), hg e.2.le⟩ := by
  change normalizeOrdChain1 (Finsupp.mapDomain (orderCxMap g hg).onE
    (Finsupp.mapDomain (strictOrderIncl P).onE (Finsupp.single e n))) = _
  rw [Finsupp.mapDomain_single, Finsupp.mapDomain_single, normalizeOrdChain1_single]
  rfl

theorem normalizedStrictChain1_id (c : StrictOrdEdge P →₀ ℤ) :
    normalizedStrictChain1 id monotone_id c = c := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => exact map_zero _
  | add c d hc hd => rw [map_add, hc, hd]
  | single e n =>
    rw [normalizedStrictChain1_single]
    simp [normalizeOrdEdge, e.2.ne]

theorem normalizedStrictChain1_zero_of_comparable_equal
    (g : P → P) (hg : Monotone g) (he : ∀ {a b : P}, a ≤ b → g a = g b)
    (c : StrictOrdEdge P →₀ ℤ) : normalizedStrictChain1 g hg c = 0 := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => exact map_zero _
  | add c d hc hd => rw [map_add, hc, hd, add_zero]
  | single e n =>
    rw [normalizedStrictChain1_single]
    simp [normalizeOrdEdge, he e.2.le]

theorem strict_oneCycle_comparable_boundary (g h : P → P)
    (hg : Monotone g) (hh : Monotone h) (hgh : ∀ x, g x ≤ h x)
    (c : StrictOrdEdge P →₀ ℤ) (hc : bdry1 (strictOrderCx P) c = 0) :
    ∃ y : StrictOrdTri P →₀ ℤ,
      bdry2 (strictOrderCx P) y = normalizedStrictChain1 h hh c -
        normalizedStrictChain1 g hg c := by
  let w := chain1 (strictOrderIncl P) c
  have hw : bdry1 (orderCx P) w = 0 := by
    rw [bdry1_chain1, hc, map_zero]
  let p := Nerve.prism g h (ordNerveChain1 w)
  have hp : p ∈ Nerve.Inc P :=
    Nerve.prism_mem_inc hg hh hgh (ordNerveChain1_mem_inc w)
  have hd : Nerve.bdry (ordNerveChain1 w) = 0 := by
    rw [← ordNerveChain0_bdry1, hw, map_zero]
  have hb : Nerve.bdry p = Nerve.cmap h (ordNerveChain1 w) -
      Nerve.cmap g (ordNerveChain1 w) := by
    simpa [p, hd] using Nerve.bdry_prism_add_prism_bdry g h (ordNerveChain1 w)
  let b := Nerve.lengthProjection 3 p
  have hbi : b ∈ Nerve.Inc P := Nerve.lengthProjection_mem_inc _ hp
  have hdeg : Nerve.lengthProjection 3 b = b := Nerve.lengthProjection_idempotent _ _
  have hy : bdry2 (orderCx P) (decodeOrdNerve2 b) =
      chain1 (orderCxMap h hh) w - chain1 (orderCxMap g hg) w := by
    apply ordNerveChain1_injective
    rw [ordNerveChain1_bdry2, ordNerveChain2_decode hbi, hdeg, map_sub]
    dsimp only [b]
    rw [← Nerve.lengthProjection_bdry, hb, map_sub,
      ← ordNerveChain1_chain1 h hh, ← ordNerveChain1_chain1 g hg,
      ordNerveChain1_lengthProjection, ordNerveChain1_lengthProjection]
  refine ⟨normalizeOrdChain2 (decodeOrdNerve2 b), ?_⟩
  rw [bdry2_normalizeOrdChain2, hy, map_sub]
  rfl

theorem strict_oneCycle_boundary_of_roof_collapse (g h : P → P)
    (hg : Monotone g) (hh : Monotone h) (hgi : ∀ x, g x ≤ x)
    (hgh : ∀ x, g x ≤ h x) (he : ∀ {a b : P}, a ≤ b → h a = h b)
    (c : StrictOrdEdge P →₀ ℤ) (hc : bdry1 (strictOrderCx P) c = 0) :
    ∃ y : StrictOrdTri P →₀ ℤ, bdry2 (strictOrderCx P) y = c := by
  obtain ⟨y, hy⟩ := strict_oneCycle_comparable_boundary g id hg monotone_id hgi c hc
  obtain ⟨z, hz⟩ := strict_oneCycle_comparable_boundary g h hg hh hgh c hc
  refine ⟨y - z, ?_⟩
  rw [map_sub, hy, hz, normalizedStrictChain1_id,
    normalizedStrictChain1_zero_of_comparable_equal h hh he]
  abel

end FiniteChains.Comb
