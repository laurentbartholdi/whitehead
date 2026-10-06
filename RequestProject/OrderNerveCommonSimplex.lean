module

public import RequestProject.OrderNerveRealizationContraction

@[expose] public section

namespace FiniteChains.Comb
open CategoryTheory Simplicial
open scoped Classical
variable {P : Type} [PartialOrder P]

/-- Two simplices whose vertices are pairwise cross-comparable lie in an actual
common simplex, with explicit simplex operators for both inclusions. -/
theorem orderNerveSimplex_common {n k : SimplexCategory}
    (s : (nerve P).obj (Opposite.op n)) (t : (nerve P).obj (Opposite.op k))
    (hc : ∀ i j, s.obj i ≤ t.obj j ∨ t.obj j ≤ s.obj i) :
    ∃ (m : SimplexCategory) (u : (nerve P).obj (Opposite.op m))
      (a : n ⟶ m) (b : k ⟶ m),
      (nerve P).map a.op u = s ∧ (nerve P).map b.op u = t := by
  classical
  let A : Set P := Set.range s.obj ∪ Set.range t.obj
  have hA : IsChain (· ≤ ·) A := by
    intro x hx y hy _
    rcases hx with ⟨i, rfl⟩ | ⟨i, rfl⟩
    · rcases hy with ⟨j, rfl⟩ | ⟨j, rfl⟩
      · rcases le_total i j with h | h
        · exact Or.inl (leOfHom (s.map (homOfLE h)))
        · exact Or.inr (leOfHom (s.map (homOfLE h)))
      · exact hc i j
    · rcases hy with ⟨j, rfl⟩ | ⟨j, rfl⟩
      · exact (hc j i).symm
      · rcases le_total i j with h | h
        · exact Or.inl (leOfHom (t.map (homOfLE h)))
        · exact Or.inr (leOfHom (t.map (homOfLE h)))
  letI : Fintype A := ((Set.finite_range s.obj).union (Set.finite_range t.obj)).fintype
  letI : LinearOrder A :=
    { Subtype.partialOrder _ with
      le_total := fun x y => hA.total x.property y.property
      toDecidableLE := Subtype.decidableLE
      toDecidableLT := Subtype.decidableLT
      toDecidableEq := Subtype.instDecidableEq }
  letI : Nonempty A := ⟨⟨s.obj 0, Or.inl ⟨0, rfl⟩⟩⟩
  obtain ⟨r, hr⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt (Fintype.card_pos (α := A)))
  let e : A ≃o Fin (r + 1) := (Fintype.orderIsoFinOfCardEq A hr).symm
  let u : (nerve P).obj (Opposite.op ⦋r⦌) :=
    (show Monotone (fun i : Fin (r + 1) => (e.symm i).val) from
      fun _ _ h => e.symm.monotone h).functor
  let a : n ⟶ ⦋r⦌ := SimplexCategory.mkHom
    ⟨fun i => e ⟨s.obj i, Or.inl ⟨i, rfl⟩⟩,
      fun _ _ h => e.monotone (leOfHom (s.map (homOfLE h)))⟩
  let b : k ⟶ ⦋r⦌ := SimplexCategory.mkHom
    ⟨fun i => e ⟨t.obj i, Or.inr ⟨i, rfl⟩⟩,
      fun _ _ h => e.monotone (leOfHom (t.map (homOfLE h)))⟩
  refine ⟨⦋r⦌, u, a, b, ?_, ?_⟩
  · exact CategoryTheory.Functor.ext (fun i =>
      congrArg Subtype.val (e.symm_apply_apply ⟨s.obj i, Or.inl ⟨i, rfl⟩⟩))
  · exact CategoryTheory.Functor.ext (fun i =>
      congrArg Subtype.val (e.symm_apply_apply ⟨t.obj i, Or.inr ⟨i, rfl⟩⟩))

end FiniteChains.Comb
