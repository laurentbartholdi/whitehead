import RequestProject.GapDescentReduction

/-!
# Relative chains with finitely many added cells, and the corrected descent gap

`RequestProject/GapDescentReduction.lean` reduced the converse implication of Theorem A to
the field `step` of `FiniteChains.Comb.Gap` together with the statement
`FiniteChains.Comb.PushoutDescent`.  The latter asks, *for an arbitrary relative chain over
`D`*, that the terms of the chain carry only finitely many cells off `D`.  That is not a
consequence of being a relative chain: `FiniteChains.IsRelativeChain` says nothing about the
number of cells, and a chain may well add infinitely many of them.  The finiteness has to
travel **with the chain**, i.e. it belongs to the construction of Lemmas 3.1, 3.9, 3.10 (in
the paper, each pass adds finitely many generators and relators), not to the descent.

This file carries out that correction.

* `FiniteChains.Comb.IsFiniteRelativeChain` — a relative chain together with the bookkeeping
  the descent actually needs: each of its terms has only finitely many cells off `D`, and
  each step adds a two-cell;
* `FiniteChains.Comb.descent_of_finiteRelativeChain` — **Proposition 3.11 for such a chain,
  modulo the homotopy statement only**: if the arrows of the explicit chain of cellular
  pushouts `Eᵢ = K ∪_p Lᵢ` are zero on `π₂`, then that chain witnesses condition (1) of
  Theorem A for `K` with finite stages.  Construction, strictness and finiteness are proved
  here;
* `FiniteChains.Comb.FiniteStep`, `FiniteChains.Comb.PushoutArrowsZeroPi2` — the two
  statements that remain: the extension step of Lemmas 3.1, 3.9, 3.10 *with finitely many
  added cells*, and the vanishing on `π₂` of the arrows of the descended chain;
* `FiniteChains.Comb.hasFiniteZeroChains_of_finiteStep`,
  `FiniteChains.Comb.theoremA_of_finiteStep` — **Theorem A for finite connected combinatorial
  two-complexes from exactly those two statements.**
-/

namespace FiniteChains
namespace Comb

universe u

variable {K D : Complex2.{u}} {c : ℕ → Complex2.{u}}

/-! ### Chains adding finitely many cells -/

/-- **A relative chain with finite relative cell data.**  On top of
`FiniteChains.IsRelativeChain` it records that every term carries only finitely many cells
off `D` and that every step adds at least one two-cell.  Both are properties of the
construction of Lemmas 3.1, 3.9 and 3.10, and both are what the descent of Proposition 3.11
needs in order to produce a strictly increasing chain with finite stages. -/
structure IsFiniteRelativeChain (D : Complex2.{u}) (c : ℕ → Complex2.{u}) (n : ℕ)
    (hsub : ∀ i, Sub (c i) (c (i + 1))) : Prop where
  /-- The underlying relative chain of Proposition 3.7. -/
  chain : IsRelativeChain combData D c n
  /-- Each term has only finitely many edges off `D`. -/
  finiteOffE : ∀ i ≤ n, Finite (OffE (chainIncl c hsub i))
  /-- Each term has only finitely many two-cells off `D`. -/
  finiteOffF : ∀ i ≤ n, Finite (OffF (chainIncl c hsub i))
  /-- Each step adds a two-cell. -/
  adds : ∀ i < n, Nonempty (OffF (chainStep c hsub i))

/-- The identity map has no cells off its image. -/
theorem isEmpty_offE_id (X : Complex2.{u}) : IsEmpty (OffE (Hom.id X)) :=
  ⟨fun w => w.2 w.1 rfl⟩

/-- The identity map has no two-cells off its image. -/
theorem isEmpty_offF_id (X : Complex2.{u}) : IsEmpty (OffF (Hom.id X)) :=
  ⟨fun w => w.2 w.1 rfl⟩

/-- **The constant chain is a finite relative chain of length zero.** -/
theorem isFiniteRelativeChain_const (hD : IsAcyclic D) :
    IsFiniteRelativeChain D (fun _ => D) 0 (fun _ => Sub.refl D) where
  chain := isRelativeChain_const (isCockcroft_of_isAcyclic hD)
  finiteOffE i hi := by
    obtain rfl : i = 0 := Nat.le_zero.1 hi
    haveI : IsEmpty (OffE (chainIncl (fun _ : ℕ => D) (fun _ => Sub.refl D) 0)) :=
      isEmpty_offE_id D
    exact Finite.of_subsingleton
  finiteOffF i hi := by
    obtain rfl : i = 0 := Nat.le_zero.1 hi
    haveI : IsEmpty (OffF (chainIncl (fun _ : ℕ => D) (fun _ => Sub.refl D) 0)) :=
      isEmpty_offF_id D
    exact Finite.of_subsingleton
  adds i hi := absurd hi (Nat.not_lt_zero i)

/-! ### Finiteness and strictness of the descended chain -/

/-- Finiteness of the stages of the descended chain, up to the length of the chain. -/
theorem descentChain_finite_E_le (p : Hom (c 0) K) (hsub : ∀ i, Sub (c i) (c (i + 1))) {n : ℕ}
    (hK : Finite K.E) (hoff : ∀ i ≤ n, Finite (OffE (chainIncl c hsub i))) :
    ∀ i ≤ n, Finite (descentChain K p hsub i).E := by
  intro i hi
  match i with
  | 0 => exact hK
  | j + 1 =>
      have := hoff (j + 1) hi
      exact inferInstanceAs (Finite (K.E ⊕ OffE (chainIncl c hsub (j + 1))))

/-- Finiteness of the two-cells of the stages of the descended chain. -/
theorem descentChain_finite_F_le (p : Hom (c 0) K) (hsub : ∀ i, Sub (c i) (c (i + 1))) {n : ℕ}
    (hK : Finite K.F) (hoff : ∀ i ≤ n, Finite (OffF (chainIncl c hsub i))) :
    ∀ i ≤ n, Finite (descentChain K p hsub i).F := by
  intro i hi
  match i with
  | 0 => exact hK
  | j + 1 =>
      have := hoff (j + 1) hi
      exact inferInstanceAs (Finite (K.F ⊕ OffF (chainIncl c hsub (j + 1))))

/-- A two-cell added by the first step is a two-cell off `D` in the first term. -/
def offF_chainIncl_one_of_step (hsub : ∀ i, Sub (c i) (c (i + 1)))
    (w : OffF (chainStep c hsub 0)) : OffF (chainIncl c hsub 1) :=
  ⟨w.1, w.2⟩

/-- **The descended chain of a finite relative chain is strictly increasing.** -/
theorem descentChain_strict (p : Hom (c 0) K) (hsub : ∀ i, Sub (c i) (c (i + 1))) {n : ℕ}
    (hKF : Finite K.F) (hfin : IsFiniteRelativeChain (c 0) c n hsub) :
    ∀ i < n, descentChain K p hsub i ≠ descentChain K p hsub (i + 1) := by
  intro i hi
  match i with
  | 0 =>
      obtain ⟨w⟩ := hfin.adds 0 hi
      exact descentChain_zero_ne_one p hsub hKF (hfin.finiteOffF 1 hi)
        (offF_chainIncl_one_of_step hsub w)
  | j + 1 =>
      obtain ⟨w⟩ := hfin.adds (j + 1) hi
      exact descentChain_succ_ne_succ p hsub j hKF (hfin.finiteOffF (j + 1) (by omega))
        (hfin.finiteOffF (j + 2) (by omega)) w

/-! ### Proposition 3.11 for a finite relative chain -/

/-- **Proposition 3.11 for a chain with finitely many added cells, modulo the homotopy
statement.**  The explicit chain of cellular pushouts `E₀ = K`, `Eᵢ = K ∪_p Lᵢ` of
`RequestProject/PushoutChain.lean` is a chain of two-complexes starting at `K`, strictly
increasing, with finite stages; if moreover its arrows are zero on `π₂` it witnesses
condition (1) of Theorem A for `K`. -/
theorem descent_of_finiteRelativeChain {n : ℕ} (p : Hom D K)
    (hsub : ∀ i, Sub (c i) (c (i + 1))) (h0 : c 0 = D)
    (hfin : IsFiniteRelativeChain D c n hsub) (hKE : Finite K.E) (hKF : Finite K.F)
    (hzero : ∀ i < n, combData.ZeroPi2 (descentChain K (h0 ▸ p) hsub i)
      (descentChain K (h0 ▸ p) hsub (i + 1))) :
    ∃ e : ℕ → Complex2.{u}, e 0 = K ∧ IsZeroChain combData e n ∧
      (∀ i, i ≤ n → Finite (e i).E) ∧ (∀ i, i ≤ n → Finite (e i).F) := by
  subst h0
  refine ⟨descentChain K p hsub, rfl,
    ⟨fun i _ => descentChain_sub p hsub i, descentChain_strict p hsub hKF hfin, hzero⟩,
    descentChain_finite_E_le p hsub hKE hfin.finiteOffE,
    descentChain_finite_F_le p hsub hKF hfin.finiteOffF⟩

/-! ### The two remaining statements -/

/-- **Lemmas 3.1, 3.9, 3.10 with the finiteness bookkeeping.**  Over an acyclic complex a
finite relative chain can be prolonged by one term, again adding only finitely many cells. -/
def FiniteStep : Prop :=
  ∀ D : Complex2.{u}, IsAcyclic D → ∀ (c : ℕ → Complex2.{u}) (n : ℕ)
    (hsub : ∀ i, Sub (c i) (c (i + 1))), IsFiniteRelativeChain D c n hsub →
    ∃ (c' : ℕ → Complex2.{u}) (hsub' : ∀ i, Sub (c' i) (c' (i + 1))),
      IsFiniteRelativeChain D c' (n + 1) hsub'

/-- **The homotopy statement of Proposition 3.11**: the arrows of the descended chain
`E₀ = K`, `Eᵢ = K ∪_p Lᵢ` are zero on `π₂`.  For the first arrow this is proved in
`RequestProject/ZeroPi2Descent.lean`; for the later ones
`RequestProject/Pi2GenerationDescent.lean` reduces it to the generation statement (3.5) of
the paper. -/
def PushoutArrowsZeroPi2 : Prop :=
  ∀ (K D : Complex2.{u}) (c : ℕ → Complex2.{u}) (n : ℕ) (p : Hom D K)
    (hsub : ∀ i, Sub (c i) (c (i + 1))) (h0 : c 0 = D),
    IsCovering p → IsConnected D → IsAcyclic D → IsFiniteRelativeChain D c n hsub →
    Finite K.E → Finite K.F →
    ∀ i < n, combData.ZeroPi2 (descentChain K (h0 ▸ p) hsub i)
      (descentChain K (h0 ▸ p) hsub (i + 1))

/-- Relative chains of every length, with finite relative cell data, from `FiniteStep`. -/
theorem exists_finiteRelativeChain (hstep : FiniteStep.{u}) (hD : IsAcyclic D) (n : ℕ) :
    ∃ (c : ℕ → Complex2.{u}) (hsub : ∀ i, Sub (c i) (c (i + 1))),
      IsFiniteRelativeChain D c n hsub := by
  induction n with
  | zero => exact ⟨fun _ => D, fun _ => Sub.refl D, isFiniteRelativeChain_const hD⟩
  | succ n ih =>
      obtain ⟨c, hsub, hc⟩ := ih
      exact hstep D hD c n hsub hc

/-- **`(2) ⇒ (1)` for finite combinatorial two-complexes, from the two remaining
statements.** -/
theorem hasFiniteZeroChains_of_finiteStep (hstep : FiniteStep.{u})
    (harrows : PushoutArrowsZeroPi2.{u}) {K : Complex2.{u}} [Finite K.E] [Finite K.F]
    (hK : HasAcyclicRegularCover K) : HasFiniteZeroChains K := by
  obtain ⟨D, Q, hQ, p, A, hcov, hreg, hconnD, hacycD⟩ := hK
  intro n
  obtain ⟨c, hsub, hc⟩ := exists_finiteRelativeChain hstep hacycD n
  exact descent_of_finiteRelativeChain p hsub hc.chain.base hc inferInstance inferInstance
    (harrows K D c n p hsub hc.chain.base hcov hconnD hacycD hc inferInstance inferInstance)

/-- **Theorem A for finite connected combinatorial two-complexes**, from the extension step
with finitely many added cells and the vanishing on `π₂` of the arrows of the descended
chain.  The implication `(1) ⇒ (2)` is a theorem of this project. -/
theorem theoremA_of_finiteStep (hstep : FiniteStep.{u}) (harrows : PushoutArrowsZeroPi2.{u})
    {K : Complex2.{u}} [Finite K.E] [Finite K.F] (hconn : IsConnected K) (x₀ : K.V) :
    HasFiniteZeroChains K ↔ HasAcyclicRegularCover K :=
  ⟨fun h => hasAcyclicRegularCover_of_hasZeroChains_comb_disc hconn x₀ h,
    fun h => hasFiniteZeroChains_of_finiteStep hstep harrows h⟩

end Comb
end FiniteChains
