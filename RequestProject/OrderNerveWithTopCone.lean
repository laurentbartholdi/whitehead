module

public import RequestProject.OrderNerveFiniteCoordinates
public import RequestProject.OrderNerveRealizationContraction
public import Mathlib.Data.Fintype.Option

@[expose] public section

/-! The actual realization of `WithTop P` is the radial cone on the actual
realization of `P`. The equal-fiber statement records the collapsed radius-zero
face exactly; no abstract cone-realization comparison is assumed. -/

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb
open scoped Classical unitInterval

variable (P : Type) [PartialOrder P]

def orderNerveConeBase : C(orderNerveRealization P, orderNerveRealization (WithTop P)) :=
  (orderNerveRealizationMap (fun p : P => (p : WithTop P)) WithTop.coe_mono).hom

def orderNerveRadialCone : C(I × orderNerveRealization P,
    orderNerveRealization (WithTop P)) where
  toFun rx := orderNerveRealizationCone (⊤ : WithTop P)
    (fun _ => Or.inl le_top) (unitInterval.symm rx.1) (orderNerveConeBase P rx.2)
  continuous_toFun := (orderNerveRealizationCone_continuous
    (⊤ : WithTop P) (fun _ => Or.inl le_top)).comp
      ((unitInterval.continuous_symm.comp continuous_fst).prodMk
        ((orderNerveConeBase P).continuous.comp continuous_snd))

@[simp] theorem orderNerveConeBase_coordinate (x : orderNerveRealization P) (p : P) :
    orderNerveRealizationCoordinates (WithTop P) (orderNerveConeBase P x) p =
      orderNerveRealizationCoordinates P x p :=
  orderNerveRealizationCoordinates_map_injective _ WithTop.coe_mono
    WithTop.coe_injective x p

@[simp] theorem orderNerveConeBase_top (x : orderNerveRealization P) :
    orderNerveRealizationCoordinates (WithTop P) (orderNerveConeBase P x) ⊤ = 0 :=
  orderNerveRealizationCoordinates_map_outside _ WithTop.coe_mono x ⊤
    (by rintro ⟨p, hp⟩; exact WithTop.coe_ne_top hp)

@[simp] theorem orderNerveRadialCone_top (r : I) (x : orderNerveRealization P) :
    orderNerveRealizationCoordinates (WithTop P) (orderNerveRadialCone P (r, x)) ⊤ =
      1 - (r : ℝ) := by
  simp [orderNerveRadialCone, orderNerveRealizationCone_coordinates]

@[simp] theorem orderNerveRadialCone_coordinate (r : I) (x : orderNerveRealization P)
    (p : P) :
    orderNerveRealizationCoordinates (WithTop P) (orderNerveRadialCone P (r, x)) p =
      (r : ℝ) * orderNerveRealizationCoordinates P x p := by
  simp [orderNerveRadialCone, orderNerveRealizationCone_coordinates]

@[simp] theorem orderNerveRadialCone_zero (x : orderNerveRealization P) :
    orderNerveRadialCone P (0, x) = orderNerveRealizationVertex (⊤ : WithTop P) := by
  simp [orderNerveRadialCone]

@[simp] theorem orderNerveRadialCone_one (x : orderNerveRealization P) :
    orderNerveRadialCone P (1, x) = orderNerveConeBase P x := by
  simp [orderNerveRadialCone]

theorem orderNerveRadialCone_eq_iff (a b : I × orderNerveRealization P) :
    orderNerveRadialCone P a = orderNerveRadialCone P b ↔
      a.1 = b.1 ∧ (a.1 = 0 ∨ a.2 = b.2) := by
  constructor
  · intro h
    have ht := (orderNerveRadialCone_top P a.1 a.2).symm.trans
      ((congrArg (fun z => orderNerveRealizationCoordinates (WithTop P) z ⊤) h).trans
        (orderNerveRadialCone_top P b.1 b.2))
    have hr : a.1 = b.1 := Subtype.ext (by linarith)
    refine ⟨hr, ?_⟩
    by_cases hz : a.1 = 0
    · exact Or.inl hz
    · right
      apply orderNerveRealizationCoordinates_injective P
      funext p
      have hp := (orderNerveRadialCone_coordinate P a.1 a.2 p).symm.trans
        ((congrArg (fun z => orderNerveRealizationCoordinates (WithTop P) z (p : WithTop P)) h).trans
          (orderNerveRadialCone_coordinate P b.1 b.2 p))
      rw (config := { transparency := .default }) [← hr] at hp
      have hn : (a.1 : ℝ) ≠ 0 := fun ha => hz (Subtype.ext ha)
      exact (mul_left_cancel₀ hn) hp
  · rintro ⟨hr, hz | hx⟩
    · obtain ⟨r, x⟩ := a
      obtain ⟨s, y⟩ := b
      dsimp at hr hz
      subst r
      subst s
      simp
    · exact congrArg (orderNerveRadialCone P) (Prod.ext hr hx)

theorem orderNerveRadialCone_surjective [Fintype P] [Nonempty P] :
    Function.Surjective (orderNerveRadialCone P) := by
  intro x
  let c := orderNerveRealizationCoordinates (WithTop P) x
  have hc (p : WithTop P) : 0 ≤ c p := orderNerveRealizationCoordinates_nonneg x p
  have hsum : c ⊤ + ∑ p : P, c p = 1 := by
    have hs := orderNerveRealizationCoordinates_sum x
    change (∑ p : Option P, c p) = 1 at hs
    rw (config := { transparency := .default }) [Fintype.sum_option] at hs
    exact hs
  have hsnonneg : 0 ≤ ∑ p : P, c p := Finset.sum_nonneg (fun p _ => hc p)
  let r : I := ⟨1 - c ⊤, by constructor <;> linarith [hc ⊤]⟩
  have hsumr : ∑ p : P, c p = (r : ℝ) := by dsimp [r]; linarith
  by_cases hr : r = 0
  · let p₀ : P := Classical.choice inferInstance
    refine ⟨(0, orderNerveRealizationVertex p₀), ?_⟩
    rw (config := { transparency := .default }) [orderNerveRadialCone_zero]
    apply orderNerveRealizationCoordinates_injective (WithTop P)
    funext p
    induction p using WithTop.recTopCoe with
    | top =>
        have hz := congrArg (fun t : I => (t : ℝ)) hr
        dsimp [r] at hz
        simp only [orderNerveRealizationCoordinates_vertex, ite_true]
        change 1 = c ⊤
        linarith
    | coe p =>
        have hp : c p ≤ ∑ q : P, c q :=
          Finset.single_le_sum (f := fun q : P => c (q : WithTop P))
            (fun q _ => hc q) (Finset.mem_univ p)
        rw (config := { transparency := .default }) [hsumr, hr] at hp
        simp only [Set.Icc.coe_zero] at hp
        simp only [orderNerveRealizationCoordinates_vertex, WithTop.top_ne_coe, ite_false]
        exact (le_antisymm hp (hc p)).symm
  · have hrpos : 0 < (r : ℝ) := lt_of_le_of_ne r.property.1
      (fun hz => hr (Subtype.ext hz.symm))
    let d : P → ℝ := fun p => c p / (r : ℝ)
    have hd : ∀ p, 0 ≤ d p := fun p => div_nonneg (hc p) r.property.1
    have hdsum : ∑ p, d p = 1 := by
      dsimp [d]
      rw (config := { transparency := .default }) [← Finset.sum_div, hsumr, div_self (ne_of_gt hrpos)]
    have hdchain : IsChain (· ≤ ·) {p | 0 < d p} := by
      intro p hp q hq hpq
      have hp' : 0 < c p := (div_pos_iff_of_pos_right hrpos).mp hp
      have hq' : 0 < c q := (div_pos_iff_of_pos_right hrpos).mp hq
      have h := orderNerveRealizationCoordinates_support_chain x hp' hq'
        (fun he => hpq (WithTop.coe_injective he))
      exact h.elim (fun h => Or.inl (WithTop.coe_le_coe.mp h))
        (fun h => Or.inr (WithTop.coe_le_coe.mp h))
    obtain ⟨y, hy⟩ := orderNerveRealizationCoordinates_exists d hd hdsum hdchain
    refine ⟨(r, y), ?_⟩
    apply orderNerveRealizationCoordinates_injective (WithTop P)
    funext p
    induction p using WithTop.recTopCoe with
    | top =>
        rw (config := { transparency := .default }) [orderNerveRadialCone_top]
        change 1 - (1 - c ⊤) = c ⊤
        ring
    | coe p =>
        rw (config := { transparency := .default }) [orderNerveRadialCone_coordinate, hy p]
        change (r : ℝ) * (c p / (r : ℝ)) = c p
        field_simp [ne_of_gt hrpos]

end FiniteChains.Comb
