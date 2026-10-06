import RequestProject.OrderNerveRealizationStarIntersections

namespace FiniteChains.Comb
open CategoryTheory Simplicial
open scoped Classical

/-- A nonempty finite chain of vertices is the vertex set of a simplex. -/
theorem orderNerveSimplex_of_finset {P : Type} [PartialOrder P]
    (A : Finset P) (hA : A.Nonempty) (hchain : IsChain (· ≤ ·) (A : Set P)) :
    ∃ (n : SimplexCategory) (s : (nerve P).obj (Opposite.op n)),
      Set.range s.obj = (A : Set P) := by
  classical
  letI : LinearOrder (A : Set P) :=
    { Subtype.partialOrder _ with
      le_total := fun x y => hchain.total x.property y.property
      toDecidableLE := Subtype.decidableLE
      toDecidableLT := Subtype.decidableLT
      toDecidableEq := Subtype.instDecidableEq }
  obtain ⟨a, ha⟩ := hA
  letI : Nonempty (A : Set P) := ⟨⟨a, ha⟩⟩
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero
    (ne_of_gt (Fintype.card_pos (α := (A : Set P))))
  let e : (A : Set P) ≃o Fin (n + 1) := (Fintype.orderIsoFinOfCardEq (A : Set P) hn).symm
  let s : (nerve P).obj (Opposite.op ⦋n⦌) :=
    (show Monotone (fun i : Fin (n + 1) => (e.symm i).val) from
      fun _ _ h => e.symm.monotone h).functor
  refine ⟨⦋n⦌, s, ?_⟩
  ext p
  constructor
  · rintro ⟨i, rfl⟩
    exact (e.symm i).property
  · intro hp
    exact ⟨e ⟨p, hp⟩, congrArg Subtype.val (e.symm_apply_apply ⟨p, hp⟩)⟩

def orderNerveRealizationStarIntersection {P : Type} [PartialOrder P] (A : Finset P) :
    Set (orderNerveRealization P) :=
  {x | ∀ p ∈ A, x ∈ orderNerveRealizationOpenStar P p}

/-- Positive barycentric coordinates in one point are supported on a chain. -/
theorem orderNerveRealizationStarIntersection_chain {P : Type} [PartialOrder P]
    (A : Finset P) (h : (orderNerveRealizationStarIntersection A).Nonempty) :
    IsChain (· ≤ ·) (A : Set P) := by
  obtain ⟨x, hx⟩ := h
  obtain ⟨n, s, z, hz, he⟩ := orderNerveRealization_interior_cover P x
  intro p hp q hq _
  have hxp := hx p hp
  have hxq := hx q hq
  rw [← he] at hxp hxq
  obtain ⟨i, rfl⟩ := (orderNerveRealizationSimplex_mem_openStar_iff s.val z hz p).mp hxp
  obtain ⟨j, rfl⟩ := (orderNerveRealizationSimplex_mem_openStar_iff s.val z hz q).mp hxq
  rcases le_total i j with hij | hij
  · exact Or.inl (leOfHom (s.val.map (homOfLE hij)))
  · exact Or.inr (leOfHom (s.val.map (homOfLE hij)))

theorem orderNerveRealizationStarIntersection_eq_simplexStar {P : Type} [PartialOrder P]
    (A : Finset P) {n : SimplexCategory} (s : (nerve P).obj (Opposite.op n))
    (hs : Set.range s.obj = (A : Set P)) :
    orderNerveRealizationStarIntersection A = orderNerveRealizationSimplexOpenStar s := by
  ext x
  constructor
  · intro hx i
    exact hx (s.obj i) (by
      change s.obj i ∈ (A : Set P)
      rw [← hs]
      exact Set.mem_range_self i)
  · intro hx p hp
    have hp' : p ∈ Set.range s.obj := by rw [hs]; exact hp
    obtain ⟨i, rfl⟩ := hp'
    exact hx i

/-- The nerve of the open vertex-star cover has exactly the finite chains of
the original poset as its nonempty simplices. -/
theorem orderNerveRealizationStarIntersection_nonempty_iff {P : Type} [PartialOrder P]
    (A : Finset P) (hA : A.Nonempty) :
    (orderNerveRealizationStarIntersection A).Nonempty ↔ IsChain (· ≤ ·) (A : Set P) := by
  constructor
  · exact orderNerveRealizationStarIntersection_chain A
  · intro h
    obtain ⟨n, s, hs⟩ := orderNerveSimplex_of_finset A hA h
    rw [orderNerveRealizationStarIntersection_eq_simplexStar A s hs]
    exact orderNerveRealizationSimplexOpenStar_nonempty s

/-- Every nonempty finite intersection in the vertex-star cover is contractible. -/
theorem orderNerveRealizationStarIntersection_contractible {P : Type} [PartialOrder P]
    (A : Finset P) (hA : A.Nonempty)
    (h : (orderNerveRealizationStarIntersection A).Nonempty) :
    ContractibleSpace (orderNerveRealizationStarIntersection A) := by
  obtain ⟨n, s, hs⟩ := orderNerveSimplex_of_finset A hA
    (orderNerveRealizationStarIntersection_chain A h)
  letI := orderNerveRealizationSimplexOpenStar_contractible s
  exact (Homeomorph.setCongr
    (orderNerveRealizationStarIntersection_eq_simplexStar A s hs)).contractibleSpace

theorem orderNerveRealizationStarIntersection_acyclic {P : Type} [PartialOrder P]
    (A : Finset P) (hA : A.Nonempty)
    (h : (orderNerveRealizationStarIntersection A).Nonempty) :
    Whitehead.Acyclic (orderNerveRealizationStarIntersection A) := by
  letI := orderNerveRealizationStarIntersection_contractible A hA h
  exact Whitehead.acyclic_of_contractible _

end FiniteChains.Comb
