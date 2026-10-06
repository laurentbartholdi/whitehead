module

public import RequestProject.GenusCappedSpineChains

@[expose] public section

/-! The actual capped-spine Cockcroft property in its presentation-cover coordinates. -/
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb
open scoped Classical
variable (q : ℕ) [NeZero q]

theorem cappedSpine_hurewicz (a : (cappedSpineCx q).V)
    (c : (uCover (cappedSpineCx q) a).F →₀ ℤ) :
    hurewicz (cappedSpineCx q) a c =
      Finsupp.mapDomain Prod.snd
        (chain2 (SpanningTree.treeUnivHom (cappedSpineTree q) a) c) := by
  change Finsupp.mapDomain (univProj (cappedSpineCx q) a).onF c =
    Finsupp.mapDomain Prod.snd
      (Finsupp.mapDomain (SpanningTree.uvFace (cappedSpineTree q)) c)
  rw (config := { transparency := .default }) [← Finsupp.mapDomain_comp]
  rfl

/-- Cockcroftness is exactly vanishing of the deck-forgetting image of every presentation
cover cycle. Both implications use the constructed cover comparison. -/
theorem cappedSpine_cockcroft_iff :
    Comb.IsCockcroft (cappedSpineCx q) ↔
      ∀ c : (univCover (SpanningTree.treeRel (cappedSpineTree q))).F →₀ ℤ,
        Comb.bdry2 (univCover (SpanningTree.treeRel (cappedSpineTree q))) c = 0 →
          Finsupp.mapDomain Prod.snd c = 0 := by
  constructor
  · intro h c hc
    let a : (cappedSpineCx q).V := markedSpineBase q
    obtain ⟨d, hd⟩ := cappedSpine_cover_chain2_surjective q a c
    have hmem : d ∈ Pi2 (cappedSpineCx q) a :=
      (cappedSpine_mem_pi2_iff q d).mpr (by rw (config := { transparency := .default }) [hd]; exact hc)
    have hh := h a d hmem
    rw (config := { transparency := .default }) [cappedSpine_hurewicz, hd] at hh
    exact hh
  · intro h a c hc
    rw (config := { transparency := .default }) [cappedSpine_hurewicz]
    exact h _ ((cappedSpine_mem_pi2_iff q c).mp hc)

end FiniteChains.Davis.Genus
