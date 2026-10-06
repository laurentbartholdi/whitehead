module

public import RequestProject.TreeCoverAcyclic

@[expose] public section

/-! Prescribed nonzero boundaries survive the actual spanning-tree collapse. -/
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb.SpanningTree
universe u
variable {K : Complex2.{u}} (T : SpanningTree K)
  (N : Subgroup (FreeGroup (NonTree T))) [N.Normal]
  (hN : ∀ f, treeRel T f ∈ N)

/-- Two lifted edge chains with equal vertex boundaries are equal as soon as
their non-tree coordinates agree. The difference is a cycle supported on trees. -/
theorem piE_injective_of_same_boundary (c d : (CovQ T N × K.E) →₀ ℤ)
    (hb : bdry1 (treeCover T N hN) c = bdry1 (treeCover T N hN) d)
    (he : piE T N c = piE T N d) : c = d := by
  classical
  apply sub_eq_zero.mp
  apply treeChain_eq_zero (T := T) (N := N) (hN := hN)
  · apply support_isTree_of_piE_eq_zero (T := T) (N := N)
    rw [map_sub, he, sub_self]
  · rw [map_sub, hb, sub_self]

variable [DecidableEq (NonTree T)]

/-- Equality to a prescribed lifted one-cycle can be checked after collapsing
the spanning tree; the one-cycle need not be the zero chain. -/
theorem treeCover_bdry2_eq_iff (z : (CovQ T N × K.F) →₀ ℤ)
    (b : (CovQ T N × K.E) →₀ ℤ) (hb : bdry1 (treeCover T N hN) b = 0) :
    bdry2 (treeCover T N hN) z = b ↔
      bdry2 (coverComplex N (treeRel T) hN) z = piE T N b := by
  constructor
  · intro h
    rw [← piE_bdry2 (T := T) (N := N) (hN := hN), h]
  · intro h
    apply piE_injective_of_same_boundary T N hN
    · rw [bdry1_bdry2, hb]
    · rw [piE_bdry2 (T := T) (N := N) (hN := hN), h]

/-- Exact comparison with the finitely supported Fox complex, without a
finiteness assumption on cells or on the deck group. -/
theorem treeCover_bdry2_eq_iff_fox (z : (CovQ T N × K.F) →₀ ℤ)
    (b : (CovQ T N × K.E) →₀ ℤ) (hb : bdry1 (treeCover T N hN) b = 0) :
    bdry2 (treeCover T N hN) z = b ↔
      coverSecondBoundary N (treeRel T) (fsCoords N K.F z) =
        fsCoords N (NonTree T) (piE T N b) := by
  rw [treeCover_bdry2_eq_iff T N hN z b hb, fs_coverComplex_bdry2 N (treeRel T) hN]
  exact (fsCoords N (NonTree T)).injective.eq_iff.symm

/-- The prescribed boundary of a lifted marked path has exactly its translated
Fox word coordinates, retaining the actual starting sheet. -/
theorem treeCover_path_fox_coordinates (L : List (K.E × Bool))
    (g : CovQ T N) (i : NonTree T) :
    fsCoords N (NonTree T) (piE T N (pathChain (liftK T N L g))) i =
      (MonoidAlgebra.single g (1 : ℤ) : CoverRing N) * proj N (fox i (pathWord T L)) := by
  rw [piE_pathChain_liftK, fsCoords_pathChain_liftPath_apply, mk_letters]

end FiniteChains.Comb.SpanningTree
