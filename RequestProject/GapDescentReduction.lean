module

public import RequestProject.MinimalGap
public import RequestProject.PushoutChain

@[expose] public section

/-!
# Sharpening the descent gap of Theorem A

`RequestProject/MinimalGap.lean` reduced the converse implication of Theorem A to the two
statements of `FiniteChains.Comb.Gap`, one of which, `descent`, is Proposition 3.11: a
relative chain over an acyclic regular cover `D → K` descends to a chain over `K` with finite
stages whose inclusions are zero on `π₂`.  As stated, that field asks for the *existence* of a
whole chain downstairs — construction, finiteness and homotopy theory together.

With the cellular pushout of `RequestProject/CombPushout.lean` and the descended chain of
`RequestProject/PushoutChain.lean` the construction and the finiteness bookkeeping are no
longer part of the gap: the chain downstairs is the explicit sequence
`E₀ = K`, `Eᵢ = K ∪_p Lᵢ`, whose terms are subcomplexes of one another by
`FiniteChains.Comb.descentChain_sub`.  What is left is the properties of *that* sequence:

* `FiniteChains.Comb.PushoutDescent` — the sharpened hypothesis: for the explicit pushout
  chain, the inclusions are zero on `π₂`, consecutive terms are distinct, and the terms of the
  chain upstairs have only finitely many cells off the cover;
* `FiniteChains.Comb.gap_descent_of_pushoutDescent` — it implies the field `descent` of
  `FiniteChains.Comb.Gap`;
* `FiniteChains.Comb.gap_of_pushoutDescent`, `FiniteChains.Comb.theoremA_of_pushoutDescent` —
  Theorem A for finite connected combinatorial two-complexes now follows from Lemmas 3.1,
  3.9, 3.10 (the field `step`) together with this sharpened form of Proposition 3.11.
-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains
namespace Comb

universe u

/-- **The sharpened form of Proposition 3.11.**  For a relative chain `c` over a connected
acyclic regular cover `D` of a finite complex `K`, the explicit chain of cellular pushouts
`Eᵢ = K ∪_p cᵢ` downstairs is strictly increasing, its inclusions are zero on `π₂`, and the
terms of the chain upstairs carry only finitely many cells off `D`.  Everything else in
Proposition 3.11 — that the `Eᵢ` are complexes, that each is a subcomplex of the next, that
`E₀ = K`, and the finiteness of the stages — is proved in
`RequestProject/PushoutChain.lean`. -/
def PushoutDescent : Prop :=
  ∀ (K D : Complex2.{u}) (c : ℕ → Complex2.{u}) (n : ℕ) (Q : Type u) (_ : Group Q)
    (p : Hom D K) (A : DeckAction D Q), IsCovering p → IsRegular p A → IsConnected D →
    IsAcyclic D → IsRelativeChain combData D c n → Finite K.E → Finite K.F →
    ∀ (hsub : ∀ i, Sub (c i) (c (i + 1))) (h0 : c 0 = D),
      (∀ i < n, combData.ZeroPi2 (descentChain K (h0 ▸ p) hsub i)
          (descentChain K (h0 ▸ p) hsub (i + 1))) ∧
        (∀ i < n, descentChain K (h0 ▸ p) hsub i ≠ descentChain K (h0 ▸ p) hsub (i + 1)) ∧
        (∀ i, Finite (OffE (chainIncl c hsub i))) ∧ (∀ i, Finite (OffF (chainIncl c hsub i)))

/-- Truncating a chain at its last term keeps it a relative chain. -/
theorem isRelativeChain_truncate {D : Complex2.{u}} {c : ℕ → Complex2.{u}} {n : ℕ}
    (hc : IsRelativeChain combData D c n) :
    IsRelativeChain combData D (fun i => c (min i n)) n where
  sub i hi := by
    rw [min_eq_left hi.le, min_eq_left hi]
    exact hc.sub i hi
  strict i hi := by
    rw [min_eq_left hi.le, min_eq_left hi]
    exact hc.strict i hi
  zero i hi := by
    rw [min_eq_left hi.le, min_eq_left hi]
    exact hc.zero i hi
  base := by simpa using hc.base
  cockcroft i hi := by
    rw [min_eq_left hi]
    exact hc.cockcroft i hi
  pi1 i h1 h2 := by
    rw [min_eq_left h2]
    exact hc.pi1 i h1 h2

/-- **The sharpened statement implies the field `descent` of `FiniteChains.Comb.Gap`.** -/
theorem gap_descent_of_pushoutDescent (h : PushoutDescent.{u}) :
    ∀ (K D : Complex2.{u}) (c : ℕ → Complex2.{u}) (n : ℕ), IsAcyclicCover D K →
      IsRelativeChain combData D c n → Finite K.E → Finite K.F →
      ∃ e : ℕ → Complex2.{u}, e 0 = K ∧ IsZeroChain combData e n ∧
        (∀ i, i ≤ n → Finite (e i).E) ∧ (∀ i, i ≤ n → Finite (e i).F) := by
  intro K D c n hcov hc hKE hKF
  obtain ⟨Q, hQ, p, A, hp, hreg, hconnD, hacycD⟩ := id hcov
  set c' : ℕ → Complex2.{u} := fun i => c (min i n) with hc'
  have hsub' : ∀ i, Sub (c' i) (c' (i + 1)) := sub_truncate hc.sub
  have hc0 : c' 0 = D := by simpa [hc'] using hc.base
  have hchain : IsRelativeChain combData D c' n := isRelativeChain_truncate hc
  obtain ⟨hzero, hstrict, hoffE, hoffF⟩ :=
    h K D c' n Q hQ p A hp hreg hconnD hacycD hchain hKE hKF hsub' hc0
  refine ⟨descentChain K (hc0 ▸ p) hsub', rfl,
    ⟨fun i _ => descentChain_sub _ hsub' i, hstrict, hzero⟩, ?_, ?_⟩
  · exact fun i _ => descentChain_finite_E _ hsub' hKE hoffE i
  · exact fun i _ => descentChain_finite_F _ hsub' hKF hoffF i

/-- **Theorem A for finite connected combinatorial two-complexes**, from Lemmas 3.1, 3.9,
3.10 and the sharpened Proposition 3.11. -/
theorem gap_of_pushoutDescent
    (step : ∀ D : Complex2.{u}, IsAcyclic D → ∀ (c : ℕ → Complex2.{u}) (n : ℕ),
      IsRelativeChain combData D c n →
      ∃ c' : ℕ → Complex2.{u}, IsRelativeChain combData D c' (n + 1))
    (h : PushoutDescent.{u}) : Gap.{u} where
  step := step
  descent := gap_descent_of_pushoutDescent h

theorem theoremA_of_pushoutDescent
    (step : ∀ D : Complex2.{u}, IsAcyclic D → ∀ (c : ℕ → Complex2.{u}) (n : ℕ),
      IsRelativeChain combData D c n →
      ∃ c' : ℕ → Complex2.{u}, IsRelativeChain combData D c' (n + 1))
    (h : PushoutDescent.{u}) {K : Complex2.{u}} [Finite K.E] [Finite K.F]
    (hconn : IsConnected K) (x₀ : K.V) :
    HasFiniteZeroChains K ↔ HasAcyclicRegularCover K :=
  theoremA_of_gap (gap_of_pushoutDescent step h) hconn x₀

end Comb
end FiniteChains
