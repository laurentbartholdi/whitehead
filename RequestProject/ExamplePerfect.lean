module

public import RequestProject.ExampleSL25Group
public import RequestProject.ExampleSL25

@[expose] public section

/-!
# `G(A)` is perfect: the example of Remark 2 satisfies condition (2) through the identity
cover

Remark 2 of the paper notes that every acyclic two-complex satisfies condition (2) of
Theorem A through its identity cover, the example being the presentation

  `A = ⟨x, y | x²yx⁻¹y, xy⁴xy⁻¹⟩`.

The identity cover of `K(A)` corresponds to the normal subgroup `N = G(A)`, and condition
(2) of Theorem A for it requires `N` to be perfect and the Fox boundary over
`ℤ[G/N] = ℤ` — that is, the exponent-sum matrix, see `RequestProject/ExampleSL25.lean` —
to be injective.

The second half is `FiniteChains.injective_expMatrixA`.  The first half is proved here:
the abelianization of `G(A)` is trivial, because the exponent-sum relations `x + 2y = 0`
and `2x + 3y = 0` force `x = y = 0`.  Transporting along the surjection of
`RequestProject/ExampleSL25Group.lean` gives the perfectness of `SL(2, 5)` as well.
-/

namespace FiniteChains
namespace ExampleA

open Subgroup

/-- In the abelianization of `G(A)` the generators die: the exponent-sum relations
`a + 2b = 0`, `2a + 3b = 0` have only the trivial solution. -/
theorem abelianization_gens_eq_one :
    Abelianization.of xA = 1 ∧ Abelianization.of yA = 1 := by
  set a := Abelianization.of xA with ha0
  set b := Abelianization.of yA with hb0
  have h1 : a * a * b * a⁻¹ * b = 1 := by
    have := congrArg Abelianization.of hrA.1
    simpa [ha0, hb0, map_mul, map_inv] using this
  have h2 : a * b * b * b * b * a * b⁻¹ = 1 := by
    have := congrArg Abelianization.of hrA.2
    simpa [ha0, hb0, map_mul, map_inv] using this
  set A := Additive.ofMul a with hA
  set B := Additive.ofMul b with hB
  have h1' : A + A + B + -A + B = 0 := by simpa using congrArg Additive.ofMul h1
  have h2' : A + B + B + B + B + A + -B = 0 := by simpa using congrArg Additive.ofMul h2
  have key : B = ((A + A + B + -A + B) + (A + A + B + -A + B))
      - (A + B + B + B + B + A + -B) := by abel
  rw [h1', h2'] at key
  have hB0 : B = 0 := by simpa using key
  have key2 : A = (A + A + B + -A + B) - B - B := by abel
  rw [h1', hB0] at key2
  have hA0 : A = 0 := by simpa using key2
  exact ⟨by simpa [hA] using hA0, by simpa [hB] using hB0⟩

/-- The abelianization of `G(A)` is trivial. -/
theorem abelianization_GA_trivial (z : Abelianization GA) : z = 1 := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective z
  have hg : g ∈ Subgroup.closure ({xA, yA} : Set GA) := by rw [hgenA]; trivial
  show Abelianization.of g = 1
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
      rcases hx with rfl | rfl
      · exact abelianization_gens_eq_one.1
      · exact abelianization_gens_eq_one.2
  | one => exact map_one _
  | mul x y _ _ hx hy => rw [map_mul, hx, hy, one_mul]
  | inv x _ hx => rw [map_inv, hx, inv_one]

/-- **`G(A)` is perfect**: its commutator subgroup is the whole group.  Together with the
injectivity of the exponent-sum matrix this is condition (2) of Theorem A for `K(A)`,
realized by the identity cover. -/
theorem commutator_GA : ⁅(⊤ : Subgroup GA), (⊤ : Subgroup GA)⁆ = ⊤ := by
  have hker : (Abelianization.of : GA →* Abelianization GA).ker = ⊤ :=
    (Subgroup.eq_top_iff' _).2 fun g => abelianization_GA_trivial _
  rw [← _root_.commutator_def GA, ← Abelianization.ker_of, hker]

/-- Perfectness passes to surjective images. -/
theorem commutator_top_of_surjective {G H : Type*} [Group G] [Group H] (f : G →* H)
    (hf : Function.Surjective f) (h : ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ = ⊤) :
    ⁅(⊤ : Subgroup H), (⊤ : Subgroup H)⁆ = ⊤ := by
  have htop : Subgroup.map f (⊤ : Subgroup G) = ⊤ := Subgroup.map_top_of_surjective f hf
  calc ⁅(⊤ : Subgroup H), (⊤ : Subgroup H)⁆
      = ⁅Subgroup.map f (⊤ : Subgroup G), Subgroup.map f (⊤ : Subgroup G)⁆ := by rw [htop]
    _ = Subgroup.map f ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ :=
        (Subgroup.map_commutator (⊤ : Subgroup G) (⊤ : Subgroup G) f).symm
    _ = Subgroup.map f (⊤ : Subgroup G) := by rw [h]
    _ = ⊤ := htop

/-- Consequently `SL(2, 5)` is perfect. -/
theorem commutator_SL25 : ⁅(⊤ : Subgroup SL25), (⊤ : Subgroup SL25)⁆ = ⊤ :=
  commutator_top_of_surjective phi phi_surjective commutator_GA

/-- **Remark 2 through the identity cover.**  For `N = G(A)` the algebraic condition of
Remark 1 holds: `N` is perfect and the Fox boundary over `ℤ[G/N] = ℤ` — the exponent-sum
matrix of the presentation `A` — is injective.  So `K(A)` satisfies condition (2) of
Theorem A. -/
theorem remark2_identity_cover :
    ⁅(⊤ : Subgroup GA), (⊤ : Subgroup GA)⁆ = ⊤ ∧
      Function.Injective (expMatrixA.mulVecLin) :=
  ⟨commutator_GA, injective_expMatrixA⟩

end ExampleA
end FiniteChains
