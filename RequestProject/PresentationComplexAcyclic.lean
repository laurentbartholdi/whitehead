module

public import RequestProject.IdentityCover

@[expose] public section

/-!
# The standard two-complex of a presentation, and the acyclic example of the paper

Remark 2 of the paper says that an acyclic two-complex satisfies condition (2) of Theorem A
through its identity cover, and offers the concrete nonaspherical example
`A = ⟨x, y | x²yx⁻¹y, xy⁴xy⁻¹⟩` with `G(A) ≅ SL(2,5)`.  This file builds the standard
two-complex of a presentation inside the combinatorial model, characterises its acyclicity,
and checks the example.

* `FiniteChains.Comb.presentationComplex` — one vertex, one edge per generator, one two-cell
  per relator word;
* `FiniteChains.Comb.isAcyclic_presentationComplex_iff` — such a complex is acyclic exactly
  when its second boundary (the exponent-sum matrix) is bijective;
* `FiniteChains.Comb.sl25Complex` — the complex of the presentation `A` of the paper, whose
  exponent-sum matrix is `!![1, 2; 2, 3]`;
* `FiniteChains.Comb.sl25Complex_isAcyclic` and
  `FiniteChains.Comb.sl25Complex_hasAcyclicRegularCover` — it is acyclic, hence satisfies
  condition (2) of Theorem A.
-/

namespace FiniteChains
namespace Comb

universe u

/-! ### The standard two-complex of a presentation -/

theorem isPath_of_punit {E : Type u} (src tgt : E → PUnit.{u + 1}) :
    ∀ (l : List (E × Bool)) (a b : PUnit.{u + 1}), IsPath src tgt l a b
  | [], a, b => Subsingleton.elim a b
  | _ :: l, _, b => ⟨Subsingleton.elim _ _, isPath_of_punit src tgt l _ b⟩

/-- **The standard two-complex of a presentation**: one vertex, one edge per generator, one
two-cell per relator, attached along the relator word. -/
abbrev presentationComplex {α J : Type u} (w : J → List (α × Bool)) : Complex2.{u} where
  V := PUnit.{u + 1}
  E := α
  F := J
  src _ := PUnit.unit
  tgt _ := PUnit.unit
  base _ := PUnit.unit
  att := w
  att_isLoop f := isPath_of_punit _ _ (w f) _ _

variable {α J : Type u} (w : J → List (α × Bool))

theorem presentationComplex_isConnected : IsConnected (presentationComplex w) :=
  fun a b => ⟨[], Subsingleton.elim a b⟩

/-- All edges are loops, so the first boundary vanishes. -/
theorem bdry1_presentationComplex (c : (presentationComplex w).E →₀ ℤ) :
    bdry1 (presentationComplex w) c = 0 := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c₁ c₂ h₁ h₂ => rw [map_add, h₁, h₂, add_zero]
  | single e n =>
      rw [bdry1_single]
      simp

/-- **A presentation complex is acyclic exactly when its second boundary is bijective.**
The second boundary is the exponent-sum matrix of the presentation. -/
theorem isAcyclic_presentationComplex_iff :
    IsAcyclic (presentationComplex w) ↔ Function.Bijective (bdry2 (presentationComplex w)) := by
  classical
  constructor
  · intro h
    exact ⟨h.h2, fun c => h.h1 c (bdry1_presentationComplex w c)⟩
  · rintro ⟨hinj, hsurj⟩
    refine ⟨hinj, fun c _ => hsurj c, fun c hc => ?_⟩
    refine ⟨0, ?_⟩
    rw [map_zero]
    have hsum : ∑ v ∈ c.support, c v = 0 := by
      simpa [augC, Finsupp.linearCombination_apply, Finsupp.sum] using hc
    refine (Finsupp.ext fun a => ?_).symm
    have hval : c PUnit.unit = 0 := by
      by_cases hmem : PUnit.unit ∈ c.support
      · rw [show c.support = {PUnit.unit} from Finset.eq_singleton_iff_unique_mem.2
          ⟨hmem, fun x _ => Subsingleton.elim _ _⟩] at hsum
        simpa using hsum
      · simpa using hmem
    rw [show a = PUnit.unit from Subsingleton.elim _ _, hval]
    rfl

/-! ### The example `A = ⟨x, y | x²yx⁻¹y, xy⁴xy⁻¹⟩` of the paper -/

/-- The two relator words of the presentation `A`, written as lists of oriented letters
(`0` is `x`, `1` is `y`). -/
def sl25Words : Fin 2 → List (Fin 2 × Bool)
  | 0 => [(0, true), (0, true), (1, true), (0, false), (1, true)]
  | 1 => [(0, true), (1, true), (1, true), (1, true), (1, true), (0, true), (1, false)]

/-- The two-complex of the presentation `A`. -/
abbrev sl25Complex : Complex2.{0} := presentationComplex sl25Words

theorem pathChain_sl25Words_zero :
    pathChain (sl25Words 0) = Finsupp.single 0 (1 : ℤ) + Finsupp.single 1 (2 : ℤ) := by
  refine Finsupp.ext fun i => ?_
  fin_cases i <;> simp [sl25Words, pathChain]

theorem pathChain_sl25Words_one :
    pathChain (sl25Words 1) = Finsupp.single 0 (2 : ℤ) + Finsupp.single 1 (3 : ℤ) := by
  refine Finsupp.ext fun i => ?_
  fin_cases i <;> simp [sl25Words, pathChain]

/-- The first column of the inverse of the exponent-sum matrix `!![1, 2; 2, 3]`. -/
noncomputable def sl25InvCol : Fin 2 → (Fin 2 →₀ ℤ)
  | 0 => Finsupp.single 0 (-3 : ℤ) + Finsupp.single 1 (2 : ℤ)
  | 1 => Finsupp.single 0 (2 : ℤ) + Finsupp.single 1 (-1 : ℤ)

/-- The inverse of the exponent-sum matrix `!![1, 2; 2, 3]`, whose determinant is `-1`. -/
noncomputable def sl25Inv : (Fin 2 →₀ ℤ) →ₗ[ℤ] (Fin 2 →₀ ℤ) :=
  Finsupp.linearCombination ℤ sl25InvCol

theorem sl25Inv_single (i : Fin 2) (n : ℤ) :
    sl25Inv (Finsupp.single i n) = n • sl25InvCol i := by
  simp [sl25Inv]

theorem bdry2_sl25Complex_single (j : Fin 2) (n : ℤ) :
    bdry2 sl25Complex (Finsupp.single j n) = n • pathChain (sl25Words j) :=
  bdry2_single (X := sl25Complex) j n

theorem sl25Inv_bdry2 (c : Fin 2 →₀ ℤ) : sl25Inv (bdry2 sl25Complex c) = c := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c₁ c₂ h₁ h₂ => rw [map_add, map_add, h₁, h₂]
  | single j n =>
      rcases (by revert j; decide : j = 0 ∨ j = 1) with rfl | rfl
      · rw [bdry2_sl25Complex_single, pathChain_sl25Words_zero,
          show (n • (Finsupp.single (0 : Fin 2) (1 : ℤ) + Finsupp.single 1 (2 : ℤ)))
            = Finsupp.single (0 : Fin 2) n + Finsupp.single 1 (2 * n) from by
              refine Finsupp.ext fun i => ?_
              fin_cases i <;> simp [mul_comm],
          map_add, sl25Inv_single, sl25Inv_single]
        refine Finsupp.ext fun i => ?_
        fin_cases i <;> simp [sl25InvCol] <;> ring
      · rw [bdry2_sl25Complex_single, pathChain_sl25Words_one,
          show (n • (Finsupp.single (0 : Fin 2) (2 : ℤ) + Finsupp.single 1 (3 : ℤ)))
            = Finsupp.single (0 : Fin 2) (2 * n) + Finsupp.single 1 (3 * n) from by
              refine Finsupp.ext fun i => ?_
              fin_cases i <;> simp <;> ring,
          map_add, sl25Inv_single, sl25Inv_single]
        refine Finsupp.ext fun i => ?_
        fin_cases i <;> simp [sl25InvCol] <;> ring

theorem bdry2_sl25Inv (c : Fin 2 →₀ ℤ) : bdry2 sl25Complex (sl25Inv c) = c := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c₁ c₂ h₁ h₂ => rw [map_add, map_add, h₁, h₂]
  | single i n =>
      rcases (by revert i; decide : i = 0 ∨ i = 1) with rfl | rfl
      · rw [sl25Inv_single]
        show bdry2 sl25Complex (n • sl25InvCol 0) = _
        rw [show (n • sl25InvCol 0)
            = Finsupp.single (0 : Fin 2) (-3 * n) + Finsupp.single 1 (2 * n) from by
              refine Finsupp.ext fun i => ?_
              fin_cases i <;> simp [sl25InvCol] <;> ring,
          map_add, bdry2_sl25Complex_single, bdry2_sl25Complex_single,
          pathChain_sl25Words_zero, pathChain_sl25Words_one]
        refine Finsupp.ext fun i => ?_
        fin_cases i <;> simp <;> ring
      · rw [sl25Inv_single]
        show bdry2 sl25Complex (n • sl25InvCol 1) = _
        rw [show (n • sl25InvCol 1)
            = Finsupp.single (0 : Fin 2) (2 * n) + Finsupp.single 1 (-n) from by
              refine Finsupp.ext fun i => ?_
              fin_cases i <;> simp [sl25InvCol, mul_comm],
          map_add, bdry2_sl25Complex_single, bdry2_sl25Complex_single,
          pathChain_sl25Words_zero, pathChain_sl25Words_one]
        refine Finsupp.ext fun i => ?_
        fin_cases i <;> simp <;> ring

theorem sl25Complex_bdry2_bijective : Function.Bijective (bdry2 sl25Complex) :=
  ⟨Function.LeftInverse.injective sl25Inv_bdry2,
    Function.RightInverse.surjective bdry2_sl25Inv⟩

/-- **The complex of the presentation `A` is acyclic.** -/
theorem sl25Complex_isAcyclic : IsAcyclic sl25Complex :=
  (isAcyclic_presentationComplex_iff sl25Words).2 sl25Complex_bdry2_bijective

/-- **The example of Remark 2 satisfies condition (2) of Theorem A**: the two-complex of
`A = ⟨x, y | x²yx⁻¹y, xy⁴xy⁻¹⟩` is acyclic and connected, so its identity cover is a
connected acyclic regular cover. -/
theorem sl25Complex_hasAcyclicRegularCover : HasAcyclicRegularCover sl25Complex :=
  hasAcyclicRegularCover_of_isAcyclic (presentationComplex_isConnected sl25Words)
    sl25Complex_isAcyclic

end Comb
end FiniteChains
