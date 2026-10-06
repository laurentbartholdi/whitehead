import RequestProject.RACGCovering
import RequestProject.SquareComplexUniversalCover
import RequestProject.SquareComplexTreeCase
import RequestProject.MedianTransport

/-!
# `C(L)` and its universal cover: the square complexes

`RequestProject/RACGCovering.lean` shows that the parity homomorphism `phi : W_L → (ℤ/2)^{L⁰}`
is a covering of *graphs* from the Cayley graph of the right-angled Coxeter group `W_L` onto the
one-skeleton of the complex `C(L)`.  This file upgrades that statement to square complexes and
uses the covering theory of `RequestProject/SquareComplexUniversalCover.lean` to identify the
universal cover.

* `FiniteChains.RACG.ceq_two`, `FiniteChains.RACG.gen_two_eq` — the trace computation behind the
  right-angled relations: two two-letter reduced words give the same group element exactly when
  they are equal or are obtained from one another by swapping two commuting letters;
* `FiniteChains.RACG.four_cycle_commuting` — **every four-cycle of the Cayley graph is a
  commutation square** `x, x s, x s t, x t` with `s t = t s`; hence the two-cells of the square
  complex of the Cayley graph (the four-cycles) are exactly the two-cells of the cube complex;
* `FiniteChains.RACG.cubeCx` — the square complex `C(L)`: sign vectors, one edge for each change
  of coordinate and one square for each edge `{s,t}` of `L`;
* `FiniteChains.RACG.isCovering_phi` — **`phi` is a covering of square complexes**;
* `FiniteChains.RACG.universal_cover_iso` — **the universal cover of `C(L)` is the Cayley
  complex**: every connected, simply connected covering of `C(L)` is isomorphic, over `C(L)`, to
  the square complex of the Cayley graph of `W_L`;
* `FiniteChains.RACG.universal_cover_median` — consequently its one-skeleton is a median graph:
  Gromov's criterion for the complexes `C(L)` of the paper, with the covering no longer assumed
  to be the Cayley graph but only assumed connected and simply connected.
-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains
namespace RACG

universe u

variable {V : Type u} [DecidableEq V] (A : CommRel V)

/-! ### Two-letter words -/

omit [DecidableEq V] in
/-- Two-letter reduced words with the same trace: either they are equal, or they differ by the
swap of two commuting letters. -/
theorem ceq_two {a b c d : V} (h : CEq A.rel [a, b] [c, d]) :
    (a = c ∧ b = d) ∨ (A.rel a b ∧ a = d ∧ b = c) := by
  have key : ∀ l : List V, CEq A.rel [a, b] l → l = [a, b] ∨ (A.rel a b ∧ l = [b, a]) := by
    intro l hl
    induction hl with
    | refl => exact Or.inl rfl
    | tail _ hstep ih =>
        rcases ih with rfl | ⟨hab, rfl⟩
        · cases hstep with
          | head hcm q => exact Or.inr ⟨hcm, rfl⟩
          | cons x hs => cases hs with | cons y hs2 => cases hs2
        · cases hstep with
          | head hcm q => exact Or.inl rfl
          | cons x hs => cases hs with | cons y hs2 => cases hs2
  rcases key _ h with h1 | ⟨hab, h2⟩
  · have h1' : c = a ∧ d = b := by simpa using h1
    exact Or.inl ⟨h1'.1.symm, h1'.2.symm⟩
  · have h2' : c = b ∧ d = a := by simpa using h2
    exact Or.inr ⟨hab, h2'.2.symm, h2'.1.symm⟩

omit [DecidableEq V] in
/-- A two-letter word with distinct letters is reduced. -/
theorem isRed_two {a b : V} (hab : a ≠ b) : IsRed A.rel [a, b] := by
  refine ⟨⟨trivial, by simp [canStart]⟩, ?_⟩
  simp only [canStart_cons, canStart_nil, and_false, or_false]
  exact fun h => hab h.symm

/-- **The right-angled two-letter relation**: if two products of two distinct generators agree,
either the factors agree, or the two generators commute and the products are the two orders. -/
theorem gen_two_eq {a b c d : V} (hab : a ≠ b) (hcd : c ≠ d)
    (h : gen A a * gen A b = gen A c * gen A d) :
    (a = c ∧ b = d) ∨ (A.rel a b ∧ a = d ∧ b = c) := by
  have hred1 : IsRed A.rel [a, b] := isRed_two A hab
  have hred2 : IsRed A.rel [c, d] := isRed_two A hcd
  have hw1 : cword A [a, b] = gen A a * gen A b := by simp
  have hw2 : cword A [c, d] = gen A c * gen A d := by simp
  have hcw : cword A [a, b] = cword A [c, d] := by rw [hw1, hw2, h]
  have htr : mkTr A [a, b] hred1 = mkTr A [c, d] hred2 := by
    rw [← cword_apply_one A hred1, ← cword_apply_one A hred2, hcw]
  exact ceq_two A ((mkTr_eq_iff A hred1 hred2).1 htr)

/-! ### Four-cycles of the Cayley graph -/

/-- **Every four-cycle of the Cayley graph is a commutation square.** -/
theorem four_cycle_commuting {x y z w : CayGroup A}
    (hxy : (cayleyGraph A).Adj x y) (hyz : (cayleyGraph A).Adj y z)
    (hzw : (cayleyGraph A).Adj z w) (hwx : (cayleyGraph A).Adj w x)
    (hxz : x ≠ z) (hyw : y ≠ w) :
    ∃ s t : V, A.rel s t ∧ y = x * gen A s ∧ z = x * gen A s * gen A t ∧ w = x * gen A t := by
  obtain ⟨s₁, rfl⟩ := hxy
  obtain ⟨s₂, rfl⟩ := hyz
  obtain ⟨s₃, rfl⟩ := hzw
  obtain ⟨s₄, hx⟩ := hwx
  -- the four generators multiply to one
  have hprod : gen A s₁ * gen A s₂ = gen A s₄ * gen A s₃ := by
    have h1 : x * gen A s₁ * gen A s₂ * gen A s₃ * gen A s₄ = x := hx.symm
    have h2 : gen A s₁ * gen A s₂ * gen A s₃ * gen A s₄ = 1 := by
      refine mul_left_cancel (a := x) ?_
      rw [mul_one]
      calc x * (gen A s₁ * gen A s₂ * gen A s₃ * gen A s₄)
          = x * gen A s₁ * gen A s₂ * gen A s₃ * gen A s₄ := by group
        _ = x := h1
    have h3 : gen A s₁ * gen A s₂ = (gen A s₃ * gen A s₄)⁻¹ := by
      rw [eq_inv_iff_mul_eq_one]
      calc gen A s₁ * gen A s₂ * (gen A s₃ * gen A s₄)
          = gen A s₁ * gen A s₂ * gen A s₃ * gen A s₄ := by group
        _ = 1 := h2
    rw [h3, mul_inv_rev]
    have e3 : (gen A s₃)⁻¹ = gen A s₃ := by
      rw [inv_eq_iff_mul_eq_one]; exact gen_mul_gen A s₃
    have e4 : (gen A s₄)⁻¹ = gen A s₄ := by
      rw [inv_eq_iff_mul_eq_one]; exact gen_mul_gen A s₄
    rw [e3, e4]
  have h12 : s₁ ≠ s₂ := by
    rintro rfl
    exact hxz (by rw [mul_assoc, gen_mul_gen, mul_one])
  have h23 : s₂ ≠ s₃ := by
    rintro rfl
    exact hyw (by rw [mul_assoc, mul_assoc, gen_mul_gen, mul_one])
  have h43 : s₄ ≠ s₃ := by
    rintro rfl
    refine hxz ?_
    have hcancel : x * gen A s₁ * gen A s₂ * gen A s₄ * gen A s₄ = x * gen A s₁ * gen A s₂ := by
      rw [mul_assoc, gen_mul_gen, mul_one]
    exact hx.trans hcancel
  rcases gen_two_eq A h12 h43 hprod with ⟨h1, h2⟩ | ⟨hrel, h1, h2⟩
  · exact absurd h2 h23
  · refine ⟨s₁, s₂, hrel, rfl, rfl, ?_⟩
    have hcomm : gen A s₁ * gen A s₂ = gen A s₂ * gen A s₁ := by
      rw [hprod, ← h1, ← h2]
    have h3 : gen A s₃ = gen A s₁ := by rw [h1]
    calc x * gen A s₁ * gen A s₂ * gen A s₃
        = x * (gen A s₁ * gen A s₂) * gen A s₁ := by rw [h3]; group
      _ = x * (gen A s₂ * gen A s₁) * gen A s₁ := by rw [hcomm]
      _ = x * gen A s₂ * (gen A s₁ * gen A s₁) := by group
      _ = x * gen A s₂ := by rw [gen_mul_gen, mul_one]

/-! ### The square complex of `C(L)` and the covering -/

omit [DecidableEq V] A in
theorem vec_cancel (v w : V → ZMod 2) : v + w + w = v := by
  funext u
  have h : ∀ p q : ZMod 2, p + q + q = p := by decide
  exact h (v u) (w u)

omit [DecidableEq V] A in
theorem vec_swap (v w z : V → ZMod 2) : v + w + z + w = v + z := by
  funext u
  have h : ∀ p q r : ZMod 2, p + q + r + q = p + r := by decide
  exact h (v u) (w u) (z u)

/-- **The square complex `C(L)`**: the one-skeleton is `cubeGraph` (sign vectors, one edge for
each change of coordinate) and there is one square for each edge `{s,t}` of the commutation
graph. -/
def cubeCx (A : CommRel V) : SquareComplex (V → ZMod 2) where
  adj := (cubeGraph (V := V)).Adj
  adj_symm h := (cubeGraph (V := V)).symm.symm _ _ h
  adj_irrefl a h := (cubeGraph (V := V)).irrefl h
  sq a b c d := ∃ s t : V, A.rel s t ∧ b = a + eVec s ∧ c = a + eVec s + eVec t ∧ d = a + eVec t
  sq_adj := by
    rintro a b c d ⟨s, t, -, rfl, rfl, rfl⟩
    refine ⟨⟨s, rfl⟩, ⟨t, rfl⟩, ⟨s, ?_⟩, ⟨t, ?_⟩⟩ <;>
      first | rfl | simp [vec_cancel, vec_swap]
  sq_rotate := by
    rintro a b c d ⟨s, t, hrel, rfl, rfl, rfl⟩
    refine ⟨t, s, A.rel_symm hrel, ?_, ?_, ?_⟩ <;>
      first | rfl | simp [vec_cancel, vec_swap]
  sq_reverse := by
    rintro a b c d ⟨s, t, hrel, rfl, rfl, rfl⟩
    refine ⟨s, t, hrel, ?_, ?_, ?_⟩ <;>
      first | rfl | simp [vec_cancel, vec_swap] | rw [add_right_comm]

/-- Two commuting generators commute in the group. -/
theorem gen_mul_comm {s t : V} (h : A.rel s t) : gen A s * gen A t = gen A t * gen A s :=
  Subtype.ext (by simpa [gen] using actPerm_mul_comm A h)

/-- Distinct generators have a product of length two; in particular it is not the identity. -/
theorem gen_mul_gen_ne_one {s t : V} (hst : s ≠ t) : gen A s * gen A t ≠ 1 := by
  intro h
  have hw : cword A [s, t] = gen A s * gen A t := by simp
  have hlen : clen A (cword A [s, t]) = 2 := by
    rw [clen_cword A (isRed_two A hst)]
    simp
  rw [hw, h, clen_one] at hlen
  exact absurd hlen (by omega)

theorem gen_ne_gen {s t : V} (hst : s ≠ t) : gen A s ≠ gen A t := by
  intro h
  refine gen_mul_gen_ne_one A hst ?_
  rw [h, gen_mul_gen]

/-- **The parity map is a covering of square complexes** from the square complex of the Cayley
graph of `W_L` onto `C(L)`. -/
theorem isCovering_phi
    (hdim : ∀ t : Finset V, (∀ s ∈ t, ∀ r ∈ t, s ≠ r → A.rel s r) → t.card ≤ 3) :
    SquareComplex.IsCovering ((cayleyMedianSimpleGraph A hdim).toSquareComplex) (cubeCx A)
      (phi A) where
  map_adj h := phi_map_adj A h
  map_sq := by
    rintro a b c d ⟨hab, hbc, hcd, hda, hac, hbd⟩
    obtain ⟨s, t, hrel, rfl, rfl, rfl⟩ := four_cycle_commuting A hab hbc hcd hda hac hbd
    refine ⟨s, t, hrel, ?_, ?_, ?_⟩
    · rw [phi_mul, phi_gen]
    · rw [phi_mul, phi_mul, phi_gen, phi_gen]
    · rw [phi_mul, phi_gen]
  lift_adj := fun x {_} h => phi_unique_lift A x h
  lift_sq := by
    rintro a b c d ⟨s, t, hrel, rfl, rfl, rfl⟩
    have hst : s ≠ t := fun hst => A.rel_irrefl s (hst ▸ hrel)
    have hcomm : gen A s * gen A t = gen A t * gen A s := gen_mul_comm A hrel
    refine ⟨a * gen A s, a * gen A s * gen A t, a * gen A t, ⟨⟨s, rfl⟩, ⟨t, rfl⟩, ⟨s, ?_⟩, ⟨t, ?_⟩,
      ?_, ?_⟩, ?_, ?_, ?_⟩
    · rw [mul_assoc, mul_assoc, ← hcomm, ← mul_assoc, ← mul_assoc, mul_assoc a,
        gen_mul_gen, mul_one]
    · rw [mul_assoc, gen_mul_gen, mul_one]
    · intro hcon
      refine gen_mul_gen_ne_one A hst ?_
      have := congrArg (fun g => a⁻¹ * g) hcon
      simpa [mul_assoc] using this.symm
    · intro hcon
      refine gen_ne_gen A hst ?_
      have := congrArg (fun g => a⁻¹ * g) hcon
      simpa [mul_assoc] using this
    · rw [phi_mul, phi_gen]
    · rw [phi_mul, phi_mul, phi_gen, phi_gen]
    · rw [phi_mul, phi_gen]

/-! ### The universal cover of `C(L)` -/

/-- The square complex of the Cayley graph is connected. -/
theorem cayleyCx_walkConnected
    (hdim : ∀ t : Finset V, (∀ s ∈ t, ∀ r ∈ t, s ≠ r → A.rel s r) → t.card ≤ 3) :
    ((cayleyMedianSimpleGraph A hdim).toSquareComplex).WalkConnected :=
  SquareComplex.walkConnected_of_connected (G := cayleyGraph A) (fun _ _ h => h)
    (cayleyGraph_connected A)

/-- **The universal cover of `C(L)` is the Cayley complex of `W_L`.**  Any connected, simply
connected covering of `C(L)` is isomorphic over `C(L)` to the square complex of the Cayley graph
of the right-angled Coxeter group. -/
theorem universal_cover_iso
    (hdim : ∀ t : Finset V, (∀ s ∈ t, ∀ r ∈ t, s ≠ r → A.rel s r) → t.card ≤ 3)
    {Vu : Type u} {U : SquareComplex Vu} {qm : Vu → (V → ZMod 2)}
    (hq : SquareComplex.IsCovering U (cubeCx A) qm) (hUC : U.WalkConnected)
    (hUSC : U.SimplyConnectedW) {u₀ : Vu} {x₀ : CayGroup A} (h0 : qm u₀ = phi A x₀) :
    ∃ f : Vu → CayGroup A, Function.Bijective f ∧ f u₀ = x₀ ∧ (∀ u, phi A (f u) = qm u) ∧
      (∀ u w, U.adj u w ↔ (cayleyGraph A).Adj (f u) (f w)) ∧
      (∀ a b c d, U.sq a b c d ↔
        ((cayleyMedianSimpleGraph A hdim).toSquareComplex).sq (f a) (f b) (f c) (f d)) :=
  SquareComplex.exists_iso_of_universal (isCovering_phi A hdim) hq
    (cayleyCx_walkConnected A hdim)
    ((cayleyMedianSimpleGraph A hdim).toSquareComplex_simplyConnectedW) hUC hUSC h0

/-- **Gromov's criterion for the complexes `C(L)` of the paper.**  The one-skeleton of any
connected, simply connected covering of `C(L)` is a median graph — the covering is no longer
assumed to be the Cayley graph, only to be a covering which is connected and simply connected. -/
theorem universal_cover_median
    (hdim : ∀ t : Finset V, (∀ s ∈ t, ∀ r ∈ t, s ≠ r → A.rel s r) → t.card ≤ 3)
    {Vu : Type u} {U : SquareComplex Vu} {qm : Vu → (V → ZMod 2)}
    (hq : SquareComplex.IsCovering U (cubeCx A) qm) (hUC : U.WalkConnected)
    (hUSC : U.SimplyConnectedW) {u₀ : Vu} {x₀ : CayGroup A} (h0 : qm u₀ = phi A x₀) :
    ∃ M : MedianSimpleGraph Vu, ∀ a b : Vu, M.G.Adj a b ↔ U.adj a b := by
  classical
  obtain ⟨f, hbij, -, -, hadj, -⟩ := universal_cover_iso A hdim hq hUC hUSC h0
  refine ⟨MedianSimpleGraph.ofIso (cayleyMedianSimpleGraph A hdim)
    (SquareComplex.toSimpleGraph U) ⟨Equiv.ofBijective f hbij, ?_⟩, fun a b => Iff.rfl⟩
  intro a b
  exact (hadj a b).symm

/-- **Non-vacuity**: the Cayley complex itself is such a covering, so the hypotheses of
`FiniteChains.RACG.universal_cover_median` are satisfiable. -/
theorem universal_cover_median_nonvacuous
    (hdim : ∀ t : Finset V, (∀ s ∈ t, ∀ r ∈ t, s ≠ r → A.rel s r) → t.card ≤ 3) :
    ∃ M : MedianSimpleGraph (CayGroup A), ∀ a b : CayGroup A,
      M.G.Adj a b ↔ ((cayleyMedianSimpleGraph A hdim).toSquareComplex).adj a b :=
  universal_cover_median A hdim (isCovering_phi A hdim) (cayleyCx_walkConnected A hdim)
    ((cayleyMedianSimpleGraph A hdim).toSquareComplex_simplyConnectedW)
    (x₀ := (1 : CayGroup A)) rfl

end RACG
end FiniteChains
