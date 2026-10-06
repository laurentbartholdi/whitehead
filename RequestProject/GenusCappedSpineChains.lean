module

public import RequestProject.GenusCappedSpine
public import RequestProject.TreeUnivCoverIso

@[expose] public section

/-! Chain comparison for the actual capped spine and its cell presentation. -/
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb
open scoped Classical
variable (q : ℕ) [NeZero q]

theorem cappedSpineDisk_boundary (x : Fin q × Bool) :
    Comb.bdry2 (cappedSpineCx q) (Finsupp.single (Sum.inr x) (1 : ℤ)) =
      pathChain (markedSpineLoop q x).1 := by
  rw (config := { transparency := .default }) [bdry2_single, one_smul]
  rfl

/-- Actual path-class-cover two-chains have exactly the presentation-cover cycle condition. -/
theorem cappedSpine_mem_pi2_iff {a : (cappedSpineCx q).V}
    (c : (uCover (cappedSpineCx q) a).F →₀ ℤ) :
    c ∈ Pi2 (cappedSpineCx q) a ↔
      Comb.bdry2 (univCover (SpanningTree.treeRel (cappedSpineTree q)))
        (chain2 (SpanningTree.treeUnivHom (cappedSpineTree q) a) c) = 0 := by
  classical
  exact SpanningTree.mem_pi2_iff_bdry2_univCover (cappedSpineTree q) c

/-- Every presentation-cover chain is the image of a genuine path-class-cover chain. -/
theorem cappedSpine_cover_chain2_surjective (a : (cappedSpineCx q).V) :
    Function.Surjective (chain2 (SpanningTree.treeUnivHom (cappedSpineTree q) a)) :=
  SpanningTree.chain2_treeUnivHom_surjective (cappedSpineTree q)

end FiniteChains.Davis.Genus
