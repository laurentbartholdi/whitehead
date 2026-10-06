module

public import RequestProject.GenusCollapse
public import RequestProject.CutSurfaceSpine
public import Mathlib.Order.Extension.Linear
public import RequestProject.GeometricChainCollapse
public import RequestProject.CutFacetCollapse

@[expose] public section

/-! Integral chain collapse of the actual genus block, chosen independently of a cycle. -/

namespace FiniteChains.Davis.Genus
open ASC
variable (q : ℕ) [NeZero q]

abbrev GenusVertex := SCell (gvc q) (gec q) (gc q)

noncomputable instance genusVertexLinearOrder : LinearOrder (GenusVertex q) := by
  classical
  exact LinearOrder.lift' (toLinearExtension : GenusVertex q → LinearExtension (GenusVertex q))
    (fun _ _ h => h)

/-- Coordinate ordering extends the surface face order, so increasing flags use the
same orientations as the cubical boundary. -/
theorem genus_coordinate_strictMono :
    @StrictMono (GenusVertex q) (GenusVertex q)
      (instPartialOrderSCell (gc q)).toPreorder
      (genusVertexLinearOrder q).toPartialOrder.toPreorder id := by
  intro a b hab
  change toLinearExtension a < toLinearExtension b
  exact lt_of_le_of_ne (toLinearExtension.monotone hab.le) hab.ne

/-- A single collapse of the concrete truncated genus block kills every cut-surface cycle.
The collapse is chosen from the geometry, before the cycle is supplied. -/
theorem exists_genus_chainCollapse :
    ∃ lp : List (Cube (GenusVertex q) ×
        (Cube (GenusVertex q) ⊕ Finset (GenusVertex q))),
      CollapseChain.IsChainCollapse (cubeBdry (V := GenusVertex q)) lp ∧
      ∀ o : Finset (GenusVertex q) → ℤ,
        simpBdry o = 0 →
        (∀ σ, σ.card ≠ 3 → o σ = 0) →
        (∀ σ, σ ∉ (orderComplex (GenusVertex q)).faces → o σ = 0) →
        CollapseChain.cmap (cubeBdry (V := GenusVertex q)) lp
          (Sum.elim 0 (fun τ => -o τ)) = 0 := by
  obtain ⟨l, hl⟩ := genus_spine_collapse q
  obtain ⟨lp, hmap, hchain⟩ := exists_chainCollapse (Finset.Subset.refl _) hl
  refine ⟨lp, hchain, ?_⟩
  intro o hcyc hsupp hfaces
  exact cutSurface_cmap_eq_zero hcyc hsupp hfaces hl hmap hchain

/-- The actual sequence of oriented cellular cancellation pairs. -/
theorem exists_genus_geometric_chainCollapse :
    ∃ lp : List (Cube (GenusVertex q) ×
        (Cube (GenusVertex q) ⊕ Finset (GenusVertex q))),
      Collapse.IsPairCollapse (spineInc (orderComplex (GenusVertex q))) lp
        (topCubes (orderComplex (GenusVertex q))) ∧
      CollapseChain.IsChainCollapse (cubeBdry (V := GenusVertex q)) lp ∧
      ∀ o : Finset (GenusVertex q) → ℤ,
        simpBdry o = 0 →
        (∀ σ, σ.card ≠ 3 → o σ = 0) →
        (∀ σ, σ ∉ (orderComplex (GenusVertex q)).faces → o σ = 0) →
        CollapseChain.cmap (cubeBdry (V := GenusVertex q)) lp
          (Sum.elim 0 (fun τ => -o τ)) = 0 := by
  obtain ⟨l, hl⟩ := genus_spine_collapse q
  obtain ⟨lp, hm, hp, hc⟩ := exists_geometric_chainCollapse (Finset.Subset.refl _) hl
  exact ⟨lp, hp, hc, fun o hcyc hsupp hfaces =>
    cutSurface_cmap_eq_zero hcyc hsupp hfaces hl hm hc⟩

/-- Choose cut facets for all positive corner cubes while retaining both certificates and
the proved vanishing of the cut-surface cycle. -/
theorem exists_genus_cut_geometric_chainCollapse :
    ∃ lp : List (Cube (GenusVertex q) ×
        (Cube (GenusVertex q) ⊕ Finset (GenusVertex q))),
      Collapse.IsPairCollapse (spineInc (orderComplex (GenusVertex q))) lp
        (topCubes (orderComplex (GenusVertex q))) ∧
      CollapseChain.IsChainCollapse (cubeBdry (V := GenusVertex q)) lp ∧
      (∀ o : Finset (GenusVertex q) → ℤ,
        simpBdry o = 0 →
        (∀ σ, σ.card ≠ 3 → o σ = 0) →
        (∀ σ, σ ∉ (orderComplex (GenusVertex q)).faces → o σ = 0) →
        CollapseChain.cmap (cubeBdry (V := GenusVertex q)) lp
          (Sum.elim 0 (fun τ => -o τ)) = 0) ∧
      ∀ p ∈ lp, p.1 = posCube (freeSet p.1) → p.2 = Sum.inr (freeSet p.1) := by
  obtain ⟨lp, hp, _⟩ := exists_genus_geometric_chainCollapse q
  have hn := preferCutFaces_isPairCollapse (Finset.Subset.refl _) hp
  have hc := preferCutFaces_isChainCollapse (Finset.Subset.refl _) hp
  refine ⟨preferCutFaces lp, hn, hc, ?_, ?_⟩
  · intro o hcyc hsupp hfaces
    exact cutSurface_cmap_eq_zero hcyc hsupp hfaces hn.map_fst rfl hc
  · intro p hp hpos
    exact preferCutFaces_positive_pair hp hpos

/-- The actual sequence retains geometric and oriented certificates and uses the cut facet
of every positive corner cube. -/
noncomputable def genusChainCollapse := Classical.choose (exists_genus_cut_geometric_chainCollapse q)

theorem genusChainCollapse_isPairCollapse :
    Collapse.IsPairCollapse (spineInc (orderComplex (GenusVertex q))) (genusChainCollapse q)
      (topCubes (orderComplex (GenusVertex q))) :=
  (Classical.choose_spec (exists_genus_cut_geometric_chainCollapse q)).1

theorem genusChainCollapse_isChainCollapse :
    CollapseChain.IsChainCollapse (cubeBdry (V := GenusVertex q)) (genusChainCollapse q) :=
  (Classical.choose_spec (exists_genus_cut_geometric_chainCollapse q)).2.1

theorem genusChainCollapse_cutSurface_eq_zero
    (o : Finset (GenusVertex q) → ℤ) (hcyc : simpBdry o = 0)
    (hsupp : ∀ σ, σ.card ≠ 3 → o σ = 0)
    (hfaces : ∀ σ, σ ∉ (orderComplex (GenusVertex q)).faces → o σ = 0) :
    CollapseChain.cmap (cubeBdry (V := GenusVertex q)) (genusChainCollapse q)
      (Sum.elim 0 (fun τ => -o τ)) = 0 :=
  (Classical.choose_spec (exists_genus_cut_geometric_chainCollapse q)).2.2.1 o hcyc hsupp hfaces

theorem genusChainCollapse_positive_pair
    (p : Cube (GenusVertex q) × (Cube (GenusVertex q) ⊕ Finset (GenusVertex q)))
    (hp : p ∈ genusChainCollapse q) (hpos : p.1 = posCube (freeSet p.1)) :
    p.2 = Sum.inr (freeSet p.1) :=
  (Classical.choose_spec (exists_genus_cut_geometric_chainCollapse q)).2.2.2 p hp hpos

theorem genusChainCollapse_old_face_nonpositive
    (t g : Cube (GenusVertex q))
    (hp : (t, Sum.inl g) ∈ genusChainCollapse q) : t ≠ posCube (freeSet t) := by
  intro ht
  have hh := genusChainCollapse_positive_pair q (t, Sum.inl g) hp ht
  cases hh

/-- Every cut triangle is removed by its own positive corner cube. -/
theorem genusChainCollapse_removes_cut_triangle (σ : Finset (GenusVertex q))
    (hσ : IsTri (orderComplex (GenusVertex q)) σ) :
    Sum.inr σ ∈ (genusChainCollapse q).map Prod.snd := by
  have ht : posCube σ ∈ topCubes (orderComplex (GenusVertex q)) := by
    apply mem_topCubes.mpr
    simpa using hσ
  obtain ⟨f, hf⟩ := (genusChainCollapse_isPairCollapse q).covers ht
  have he : f = Sum.inr σ := by
    simpa using genusChainCollapse_positive_pair q (posCube σ, f) hf (by simp)
  subst f
  exact List.mem_map.mpr ⟨(posCube σ, Sum.inr σ), hf, rfl⟩

end FiniteChains.Davis.Genus
