module

public import RequestProject.TreePresentation
public import RequestProject.UnivCoverIncl

@[expose] public section

/-! Actual cellular cocycles associated with characters of the fundamental group. -/
namespace FiniteChains.Comb.SpanningTree
universe u v
variable {K : Complex2.{u}} (T : SpanningTree K)
  {M : Type v} [AddCommGroup M]
  (χ : Pi1 K T.root →* Multiplicative M)

noncomputable def characterChain1 : (K.E →₀ ℤ) →ₗ[ℤ] M :=
  Finsupp.linearCombination ℤ (fun e => Multiplicative.toAdd
    (χ (freeToPi1 T (germWord T (e, true)))))

theorem characterChain1_pathChain (p : List (K.E × Bool)) :
    characterChain1 T χ (pathChain p) =
      Multiplicative.toAdd (χ (freeToPi1 T (pathWord T p))) := by
  induction p with
  | nil => simp [characterChain1]
  | cons eb p ih =>
      rw [pathChain_cons, map_add, ih, pathWord_cons, map_mul, map_mul]
      change _ = Multiplicative.toAdd (χ (freeToPi1 T (germWord T eb))) + _
      apply congrArg₂ (· + ·) _ rfl
      obtain ⟨e, b⟩ := eb
      cases b with
      | true => simp [characterChain1]
      | false =>
          have he : germWord T (e, false) = (germWord T (e, true))⁻¹ :=
            germWord_revGerm T (e, true)
          simp only [Bool.false_eq_true, ↓reduceIte, map_neg, he, map_inv]
          simp [characterChain1]

/-- Every fundamental-group character annihilates the actual cellular two-boundaries. -/
theorem characterChain1_bdry2 (c : K.F →₀ ℤ) :
    characterChain1 T χ (bdry2 K c) = 0 := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => rw [map_add, map_add, hc, hd, add_zero]
  | single f n =>
      rw [bdry2_single, LinearMap.map_smul, characterChain1_pathChain]
      change n • Multiplicative.toAdd (χ (freeToPi1 T (treeRel T f))) = 0
      rw [freeToPi1_treeRel, map_one]
      simp

end FiniteChains.Comb.SpanningTree
