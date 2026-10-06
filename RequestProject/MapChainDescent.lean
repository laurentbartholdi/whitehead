module

public import RequestProject.MinimalGap
public import RequestProject.Pi2GenerationDescent

@[expose] public section

/-!
# Proposition 3.11 for chains given by explicit inclusions

Condition (1) of Theorem A speaks about a chain of **inclusions** `K = E₀ ⊊ E₁ ⊊ ⋯ ⊊ Eₙ`
each of which is zero on `π₂`.  The interface `FiniteChains.combData` renders "the inclusion
is zero on `π₂`" by the stronger condition *every* injective cellular map `Eᵢ → Eᵢ₊₁` is zero
on `π₂`; this is convenient for the implication `(1) ⇒ (2)`, but the descent of
Proposition 3.11 produces one specific inclusion per step and says nothing about the others.
This file works with the faithful, map-carrying form throughout.

* `FiniteChains.Comb.inclFrom` — the inclusion `L₀ ⊆ Lᵢ` of a chain given by explicit maps;
* `FiniteChains.Comb.RelChainW` — a relative chain of Proposition 3.7 **with its
  inclusions**, together with the finiteness bookkeeping needed downstairs;
* `FiniteChains.Comb.RelChainW.desc`, `FiniteChains.Comb.RelChainW.descInc` — the descended
  chain `E₀ = K`, `Eᵢ₊₁ = K ∪_p Lᵢ₊₁` of Proposition 3.11 together with its inclusions, and
  the proofs that these are injective, that the stages are finite and connected;
* `FiniteChains.Comb.RelChainW.zeroPi2_descInc_zero` — **the first arrow is zero on `π₂`**
  (unconditionally);
* `FiniteChains.Comb.Pi2GeneratedByUpstairs` — the generation statement (3.5) of the paper,
  the one remaining input of step 2 of the proof of Proposition 3.11;
* `FiniteChains.Comb.RelChainW.zeroPi2_descInc` — granted (3.5), **all** arrows of the
  descended chain are zero on `π₂`;
* `FiniteChains.Comb.RelChainW.toTopChainDisc` — the descended chain as a chain in the sense
  of `RequestProject/ComponentChain.lean`, whence
* `FiniteChains.Comb.hasAcyclicRegularCover_of_hasMapChains`,
  `FiniteChains.Comb.theoremA_maps` — **Theorem A for finite connected combinatorial
  two-complexes with condition (1) in its faithful form**, from two inputs: the extension
  step of Lemmas 3.1, 3.9, 3.10 (`FiniteChains.Comb.MapStep`) and the generation statement
  (3.5).
-/

namespace FiniteChains
namespace Comb

universe u

/-! ### Chains with explicit inclusions -/

/-- The inclusion of the first term of a chain into its `i`-th term. -/
def inclFrom (c : ℕ → Complex2.{u}) (inc : ∀ i, Hom (c i) (c (i + 1))) :
    ∀ i, Hom (c 0) (c i)
  | 0 => Hom.id (c 0)
  | i + 1 => (inc i).comp (inclFrom c inc i)

@[simp] theorem inclFrom_succ (c : ℕ → Complex2.{u}) (inc : ∀ i, Hom (c i) (c (i + 1)))
    (i : ℕ) : inclFrom c inc (i + 1) = (inc i).comp (inclFrom c inc i) := rfl

/-- **A relative chain of Proposition 3.7 carrying its inclusions.**  The chain is indexed by
all of `ℕ` (a chain of length `n` is extended by repeating its last term); the conditions of
Proposition 3.7 are imposed up to the index `n`.  On top of them the structure records what
the descent of Proposition 3.11 needs: the stages are connected, each term has only finitely
many cells off `D`, and each step adds a two-cell. -/
structure RelChainW (D : Complex2.{u}) (c : ℕ → Complex2.{u}) (n : ℕ) where
  /-- The inclusion of one term into the next. -/
  inc : ∀ i, Hom (c i) (c (i + 1))
  incV : ∀ i, Function.Injective (inc i).onV
  incE : ∀ i, Function.Injective (inc i).onE
  incF : ∀ i, Function.Injective (inc i).onF
  /-- The chain starts at the acyclic core `D`. -/
  base : c 0 = D
  /-- Every stage is connected. -/
  conn : ∀ i, IsConnected (c i)
  /-- Every stage is Cockcroft. -/
  cockcroft : ∀ i ≤ n, IsCockcroft (c i)
  /-- Every inclusion is zero on `π₂`. -/
  zero : ∀ i < n, ZeroPi2 (inc i)
  /-- `π₁(D)` dies from the first stage on. -/
  pi1 : ∀ i, 1 ≤ i → i ≤ n → Pi1Trivial (inclFrom c inc i)
  /-- Every stage has only finitely many edges off `D`. -/
  finE : ∀ i, Finite (OffE (inclFrom c inc i))
  /-- Every stage has only finitely many two-cells off `D`. -/
  finF : ∀ i, Finite (OffF (inclFrom c inc i))
  /-- Every step adds a two-cell. -/
  adds : ∀ i < n, Nonempty (OffF (inc i))

namespace RelChainW

variable {D : Complex2.{u}} {c : ℕ → Complex2.{u}} {n : ℕ} (R : RelChainW D c n)

theorem inclV (i : ℕ) : Function.Injective (inclFrom c R.inc i).onV := by
  induction i with
  | zero => exact fun _ _ h => h
  | succ i ih => exact (R.incV i).comp ih

theorem inclE (i : ℕ) : Function.Injective (inclFrom c R.inc i).onE := by
  induction i with
  | zero => exact fun _ _ h => h
  | succ i ih => exact (R.incE i).comp ih

theorem inclF (i : ℕ) : Function.Injective (inclFrom c R.inc i).onF := by
  induction i with
  | zero => exact fun _ _ h => h
  | succ i ih => exact (R.incF i).comp ih

/-! ### The descended chain -/

variable (K : Complex2.{u}) (p : Hom (c 0) K)

/-- **The descended chain of Proposition 3.11**: `E₀ = K` and `Eᵢ₊₁ = K ∪_p Lᵢ₊₁`. -/
noncomputable def desc : ℕ → Complex2.{u}
  | 0 => K
  | i + 1 => pushoutComplex p (inclFrom c R.inc (i + 1)) (R.inclV (i + 1)) (R.inclE (i + 1))

@[simp] theorem desc_zero : R.desc K p 0 = K := rfl

@[simp] theorem desc_succ (i : ℕ) : R.desc K p (i + 1) =
    pushoutComplex p (inclFrom c R.inc (i + 1)) (R.inclV (i + 1)) (R.inclE (i + 1)) := rfl

/-- The inclusions of the descended chain. -/
noncomputable def descInc : ∀ i, Hom (R.desc K p i) (R.desc K p (i + 1))
  | 0 => pushoutInl p (inclFrom c R.inc 1) (R.inclV 1) (R.inclE 1)
  | i + 1 =>
      pushoutFunctor p (inclFrom c R.inc (i + 1)) (inclFrom c R.inc (i + 2)) (R.inc (i + 1))
        (R.inclV (i + 1)) (R.inclE (i + 1)) (R.inclV (i + 2)) (R.inclE (i + 2))
        (R.inclF (i + 2)) rfl

theorem descInc_zero : R.descInc K p 0 = pushoutInl p (inclFrom c R.inc 1) (R.inclV 1)
    (R.inclE 1) := rfl

theorem descInc_succ (i : ℕ) : R.descInc K p (i + 1) =
    pushoutFunctor p (inclFrom c R.inc (i + 1)) (inclFrom c R.inc (i + 2)) (R.inc (i + 1))
      (R.inclV (i + 1)) (R.inclE (i + 1)) (R.inclV (i + 2)) (R.inclE (i + 2))
      (R.inclF (i + 2)) rfl := rfl

/-! ### The induced maps of pushouts are inclusions -/

section Functor

variable {L L' : Complex2.{u}} {D' : Complex2.{u}} (q : Hom D' K) (j : Hom D' L) (j' : Hom D' L')
  (k : Hom L L') (hjV : Function.Injective j.onV) (hjE : Function.Injective j.onE)
  (hj'V : Function.Injective j'.onV) (hj'E : Function.Injective j'.onE)
  (hj'F : Function.Injective j'.onF) (hkj : k.comp j = j')

include hkj in
theorem pushoutFunctor_injV (hkV : Function.Injective k.onV) :
    Function.Injective (pushoutFunctor q j j' k hjV hjE hj'V hj'E hj'F hkj).onV := by
  set F := pushoutFunctor q j j' k hjV hjE hj'V hj'E hj'F hkj
  have hinl : ∀ a : K.V, F.onV (Sum.inl a) = Sum.inl a := fun _ => rfl
  have hinr : ∀ w : OffV j, F.onV (Sum.inr w) = Sum.inr ⟨k.onV w.1, off_map_V hkV hkj w⟩ :=
    fun w => pushV_of_off q j' ⟨k.onV w.1, off_map_V hkV hkj w⟩
  rintro (a | w) (b | w') h
  · rw [hinl, hinl] at h
    exact congrArg Sum.inl (Sum.inl_injective h)
  · rw [hinl, hinr] at h
    simp at h
  · rw [hinr, hinl] at h
    simp at h
  · rw [hinr, hinr] at h
    exact congrArg Sum.inr (Subtype.ext (hkV (congrArg Subtype.val (Sum.inr_injective h))))

include hkj in
theorem pushoutFunctor_injE (hkE : Function.Injective k.onE) :
    Function.Injective (pushoutFunctor q j j' k hjV hjE hj'V hj'E hj'F hkj).onE := by
  set F := pushoutFunctor q j j' k hjV hjE hj'V hj'E hj'F hkj
  have hinl : ∀ a : K.E, F.onE (Sum.inl a) = Sum.inl a := fun _ => rfl
  have hinr : ∀ w : OffE j, F.onE (Sum.inr w) = Sum.inr ⟨k.onE w.1, off_map_E hkE hkj w⟩ :=
    fun w => pushE_of_off q j' ⟨k.onE w.1, off_map_E hkE hkj w⟩
  rintro (a | w) (b | w') h
  · rw [hinl, hinl] at h
    exact congrArg Sum.inl (Sum.inl_injective h)
  · rw [hinl, hinr] at h
    simp at h
  · rw [hinr, hinl] at h
    simp at h
  · rw [hinr, hinr] at h
    exact congrArg Sum.inr (Subtype.ext (hkE (congrArg Subtype.val (Sum.inr_injective h))))

include hkj in
theorem pushoutFunctor_injF (hkF : Function.Injective k.onF) :
    Function.Injective (pushoutFunctor q j j' k hjV hjE hj'V hj'E hj'F hkj).onF := by
  set F := pushoutFunctor q j j' k hjV hjE hj'V hj'E hj'F hkj
  have hinl : ∀ a : K.F, F.onF (Sum.inl a) = Sum.inl a := fun _ => rfl
  have hinr : ∀ w : OffF j, F.onF (Sum.inr w) = Sum.inr ⟨k.onF w.1, off_map_F hkF hkj w⟩ :=
    fun w => pushF_of_off q j' ⟨k.onF w.1, off_map_F hkF hkj w⟩
  rintro (a | w) (b | w') h
  · rw [hinl, hinl] at h
    exact congrArg Sum.inl (Sum.inl_injective h)
  · rw [hinl, hinr] at h
    simp at h
  · rw [hinr, hinl] at h
    simp at h
  · rw [hinr, hinr] at h
    exact congrArg Sum.inr (Subtype.ext (hkF (congrArg Subtype.val (Sum.inr_injective h))))

end Functor

theorem descInc_injV : ∀ i, Function.Injective (R.descInc K p i).onV
  | 0 => fun _ _ h => Sum.inl_injective h
  | i + 1 => pushoutFunctor_injV K p _ _ _ _ _ _ _ _ rfl (R.incV (i + 1))

theorem descInc_injE : ∀ i, Function.Injective (R.descInc K p i).onE
  | 0 => fun _ _ h => Sum.inl_injective h
  | i + 1 => pushoutFunctor_injE K p _ _ _ _ _ _ _ _ rfl (R.incE (i + 1))

theorem descInc_injF : ∀ i, Function.Injective (R.descInc K p i).onF
  | 0 => fun _ _ h => Sum.inl_injective h
  | i + 1 => pushoutFunctor_injF K p _ _ _ _ _ _ _ _ rfl (R.incF (i + 1))

/-! ### Finiteness and connectivity of the stages -/

theorem desc_finE (hK : Finite K.E) : ∀ i, Finite (R.desc K p i).E
  | 0 => hK
  | i + 1 => by
      have := R.finE (i + 1)
      exact inferInstanceAs (Finite (K.E ⊕ OffE (inclFrom c R.inc (i + 1))))

theorem desc_finF (hK : Finite K.F) : ∀ i, Finite (R.desc K p i).F
  | 0 => hK
  | i + 1 => by
      have := R.finF (i + 1)
      exact inferInstanceAs (Finite (K.F ⊕ OffF (inclFrom c R.inc (i + 1))))

theorem desc_conn (hK : IsConnected K) (v₀ : (c 0).V) : ∀ i, IsConnected (R.desc K p i)
  | 0 => hK
  | i + 1 =>
      isConnected_pushoutComplex p (inclFrom c R.inc (i + 1)) (R.inclV (i + 1))
        (R.inclE (i + 1)) hK (R.conn (i + 1)) v₀

/-! ### The arrows are zero on `π₂` -/

/-- **The first arrow of the descended chain is zero on `π₂`** (step 3 of the proof of
Proposition 3.11): a sphere in `K` lifts to the acyclic cover `D`. -/
theorem zeroPi2_descInc_zero (hcov : IsCovering p) (hD : IsAcyclic (c 0))
    (hconnD : IsConnected (c 0)) (hconnK : IsConnected K) (hn : 1 ≤ n) :
    ZeroPi2 (R.descInc K p 0) :=
  zeroPi2_pushoutInl (inclFrom c R.inc 1) (R.inclV 1) (R.inclE 1) (R.inclF 1) hcov hD hconnD
    hconnK (R.conn 1) (R.pi1 1 le_rfl hn)

end RelChainW

/-- **The generation statement (3.5) of the paper.**  For the cellular pushout
`E = K ∪_p L` of Proposition 3.11 along a connected acyclic covering `p : D → K` and a
subcomplex `D ⊆ L` in which `π₁(D)` dies, the second homotopy module of `E` is generated by
the spherical classes coming from `L`.  In the paper this is the isomorphism
`ℤ[H * J] ⊗_{ℤ[J]} π₂(L) ≅ π₂(E)` obtained from the Mayer–Vietoris sequence of the universal
cover; the surjectivity in degree two of the map used there is proved in
`RequestProject/UnivCoverCopies.lean`. -/
def Pi2GeneratedByUpstairsFor {D K : Complex2.{u}} (p : Hom D K) : Prop :=
  ∀ (L : Complex2.{u}) (ι : Hom D L)
    (hV : Function.Injective ι.onV) (hE : Function.Injective ι.onE)
    (hF : Function.Injective ι.onF),
    IsCovering p → IsConnected D → IsAcyclic D → IsConnected L → Pi1Trivial ι →
    ∀ (x₀ : (pushoutComplex p ι hV hE).V) (z : (uCover (pushoutComplex p ι hV hE) x₀).F →₀ ℤ),
      z ∈ Pi2 (pushoutComplex p ι hV hE) x₀ →
        z ∈ Submodule.span ℤ (Pi2FromSub (pushoutMap p ι hV hE hF) x₀)

/-- The generation statement (3.5) for every covering. -/
def Pi2GeneratedByUpstairs : Prop :=
  ∀ (D K : Complex2.{u}) (p : Hom D K), Pi2GeneratedByUpstairsFor p

namespace RelChainW

variable {D : Complex2.{u}} {c : ℕ → Complex2.{u}} {n : ℕ} (R : RelChainW D c n)
variable (K : Complex2.{u}) (p : Hom (c 0) K)

/-- **The later arrows of the descended chain are zero on `π₂`**, granted the generation
statement (3.5): the square of Proposition 3.11 commutes, its upper arrow is zero on `π₂`,
and its images generate `π₂` of the lower source. -/
theorem zeroPi2_descInc_succ (hgen : Pi2GeneratedByUpstairsFor p) (hcov : IsCovering p)
    (hD : IsAcyclic (c 0)) (hconnD : IsConnected (c 0)) (hconnK : IsConnected K)
    (v₀ : (c 0).V) (i : ℕ) (hi : i + 1 < n) : ZeroPi2 (R.descInc K p (i + 1)) := by
  have hconnE' : IsConnected (pushoutComplex p (inclFrom c R.inc (i + 2)) (R.inclV (i + 2))
      (R.inclE (i + 2))) :=
    isConnected_pushoutComplex p (inclFrom c R.inc (i + 2)) (R.inclV (i + 2))
      (R.inclE (i + 2)) hconnK (R.conn (i + 2)) v₀
  refine zeroPi2_pushoutFunctor p (inclFrom c R.inc (i + 1)) (inclFrom c R.inc (i + 2))
    (R.inc (i + 1)) (R.inclV (i + 1)) (R.inclE (i + 1)) (R.inclF (i + 1)) (R.inclV (i + 2))
    (R.inclE (i + 2)) (R.inclF (i + 2)) rfl hconnE' (R.zero (i + 1) hi) ?_
  intro x₀ z hz
  exact hgen (c (i + 1)) (inclFrom c R.inc (i + 1)) (R.inclV (i + 1))
    (R.inclE (i + 1)) (R.inclF (i + 1)) hcov hconnD hD (R.conn (i + 1))
    (R.pi1 (i + 1) (by omega) (by omega)) x₀ z hz

/-- **All arrows of the descended chain are zero on `π₂`**, granted (3.5). -/
theorem zeroPi2_descInc (hgen : Pi2GeneratedByUpstairsFor p) (hcov : IsCovering p)
    (hD : IsAcyclic (c 0)) (hconnD : IsConnected (c 0)) (hconnK : IsConnected K)
    (v₀ : (c 0).V) : ∀ i < n, ZeroPi2 (R.descInc K p i)
  | 0, hi => R.zeroPi2_descInc_zero K p hcov hD hconnD hconnK hi
  | i + 1, hi => R.zeroPi2_descInc_succ K p hgen hcov hD hconnD hconnK v₀ i hi

end RelChainW

/-! ### Strictness of the descended chain -/

section Strict

variable {D : Complex2.{u}} {c : ℕ → Complex2.{u}} {n : ℕ} (R : RelChainW D c n)
variable (K : Complex2.{u}) (p : Hom (c 0) K)

/-- The first step of the descended chain is strict: the pushout acquires the two-cell added
by the first step upstairs. -/
theorem desc_zero_ne_one (hKF : Finite K.F) (hn : 0 < n) :
    R.desc K p 0 ≠ R.desc K p 1 := by
  obtain ⟨w⟩ := R.adds 0 hn
  haveI := R.finF 1
  haveI := hKF
  have hw : OffF (inclFrom c R.inc 1) := ⟨w.1, w.2⟩
  refine ne_of_card_F_lt ?_
  have h1 : Nat.card (R.desc K p 1).F
      = Nat.card K.F + Nat.card (OffF (inclFrom c R.inc 1)) := Nat.card_sum
  have h2 : 0 < Nat.card (OffF (inclFrom c R.inc 1)) := Nat.card_pos_iff.2 ⟨⟨hw⟩, R.finF 1⟩
  show Nat.card K.F < Nat.card (R.desc K p 1).F
  omega

/-- The later steps of the descended chain are strict. -/
theorem desc_succ_ne_succ (hKF : Finite K.F) (i : ℕ) (hi : i + 1 < n) :
    R.desc K p (i + 1) ≠ R.desc K p (i + 2) := by
  obtain ⟨w⟩ := R.adds (i + 1) hi
  haveI := R.finF (i + 1)
  haveI := R.finF (i + 2)
  haveI := hKF
  have hw : ∀ d, (inclFrom c R.inc (i + 2)).onF d ≠ w.1 := fun d => w.2 _
  set g : OffF (inclFrom c R.inc (i + 1)) → OffF (inclFrom c R.inc (i + 2)) :=
    fun v => ⟨(R.inc (i + 1)).onF v.1, off_map_F (R.incF (i + 1)) rfl v⟩
  have hginj : Function.Injective g := fun v v' hvv =>
    Subtype.ext (R.incF (i + 1) (congrArg Subtype.val hvv))
  have hnotmem : ( ⟨w.1, hw⟩ : OffF (inclFrom c R.inc (i + 2))) ∉ Set.range g := by
    rintro ⟨v, hv⟩
    exact w.2 v.1 (congrArg Subtype.val hv)
  have hlt : Nat.card (OffF (inclFrom c R.inc (i + 1)))
      < Nat.card (OffF (inclFrom c R.inc (i + 2))) := by
    rcases lt_or_eq_of_le (Nat.card_le_card_of_injective g hginj) with h | h
    · exact h
    · exact absurd (((Nat.bijective_iff_injective_and_card g).2 ⟨hginj, h⟩).2 _) hnotmem
  refine ne_of_card_F_lt ?_
  have e1 : Nat.card (R.desc K p (i + 1)).F
      = Nat.card K.F + Nat.card (OffF (inclFrom c R.inc (i + 1))) := Nat.card_sum
  have e2 : Nat.card (R.desc K p (i + 2)).F
      = Nat.card K.F + Nat.card (OffF (inclFrom c R.inc (i + 2))) := Nat.card_sum
  omega

end Strict

/-! ### Non-vacuity: the constant chain -/

/-- The inclusion of the first term of the constant chain with identity steps is the
identity on edges. -/
theorem inclFrom_const_onE (D : Complex2.{u}) (i : ℕ) :
    (inclFrom (fun _ => D) (fun _ => Hom.id D) i).onE = id := by
  induction i with
  | zero => rfl
  | succ i ih => exact congrArg (fun g => id ∘ g) ih

/-- The inclusion of the first term of the constant chain with identity steps is the
identity on two-cells. -/
theorem inclFrom_const_onF (D : Complex2.{u}) (i : ℕ) :
    (inclFrom (fun _ => D) (fun _ => Hom.id D) i).onF = id := by
  induction i with
  | zero => rfl
  | succ i ih => exact congrArg (fun g => id ∘ g) ih

/-- **The constant chain is a relative chain of length zero with its inclusions**, so the
notion is not vacuous and the induction of Proposition 3.7 has a starting point. -/
noncomputable def relChainW_const {D : Complex2.{u}} (hD : IsAcyclic D) (hconn : IsConnected D) :
    RelChainW D (fun _ => D) 0 where
  inc _ := Hom.id D
  incV _ := fun _ _ h => h
  incE _ := fun _ _ h => h
  incF _ := fun _ _ h => h
  base := rfl
  conn _ := hconn
  cockcroft _ _ := isCockcroft_of_isAcyclic hD
  zero i hi := absurd hi (Nat.not_lt_zero i)
  pi1 i _ hi := absurd hi (by omega)
  finE i := by
    haveI : IsEmpty (OffE (inclFrom (fun _ => D) (fun _ => Hom.id D) i)) :=
      ⟨fun w => w.2 w.1 (congrFun (inclFrom_const_onE D i) w.1)⟩
    exact Finite.of_subsingleton
  finF i := by
    haveI : IsEmpty (OffF (inclFrom (fun _ => D) (fun _ => Hom.id D) i)) :=
      ⟨fun w => w.2 w.1 (congrFun (inclFrom_const_onF D i) w.1)⟩
    exact Finite.of_subsingleton
  adds i hi := absurd hi (Nat.not_lt_zero i)

/-! ### Assembling Theorem A -/

/-- A complex covered by a connected complex is connected. -/
theorem isConnected_of_isCovering {D K : Complex2.{u}} {p : Hom D K} (hp : IsCovering p)
    (hD : IsConnected D) : IsConnected K := by
  intro u v
  obtain ⟨a, rfl⟩ := hp.surjV u
  obtain ⟨b, rfl⟩ := hp.surjV v
  obtain ⟨m, hm⟩ := hD a b
  exact ⟨mapPath p m, isPath_mapPath p hm⟩

/-- **A chain of finite two-complexes over `K` in the sense of condition (1) of Theorem A**:
the inclusions are zero on `π₂` and the chain is strictly increasing. -/
structure StrictTopChain (K : Complex2.{u}) (n : ℕ) extends TopChainDisc K n where
  /-- The first inclusion `K ⊆ X₀` is strict. -/
  baseStrict : K ≠ X 0
  /-- The later inclusions are strict. -/
  strict : ∀ r < n, X r ≠ X (r + 1)

/-- **The descended chain of Proposition 3.11 as a chain of two-complexes over `K`.**  Its
inclusions are zero on `π₂` granted the generation statement (3.5); everything else —
injectivity of the inclusions, strictness, finiteness of the stages — is proved. -/
noncomputable def strictTopChain_of_relChainW {D K : Complex2.{u}} {c : ℕ → Complex2.{u}}
    {n : ℕ} (R : RelChainW D c (n + 1)) (p : Hom D K) (hcov : IsCovering p) (hD : IsAcyclic D)
    (hconnD : IsConnected D) (hKE : Finite K.E) (hKF : Finite K.F) (d₀ : D.V)
    (hgen : Pi2GeneratedByUpstairsFor p) : StrictTopChain K n := by
  have hb := R.base
  subst hb
  have hconnK : IsConnected K := isConnected_of_isCovering hcov hconnD
  exact
    { X := fun r => R.desc K p (r + 1)
      inc := fun r => R.descInc K p (r + 1)
      incV := fun r => R.descInc_injV K p (r + 1)
      incE := fun r => R.descInc_injE K p (r + 1)
      incF := fun r => R.descInc_injF K p (r + 1)
      finE := fun r => R.desc_finE K p hKE (r + 1)
      finF := fun r => R.desc_finF K p hKF (r + 1)
      base := R.descInc K p 0
      baseV := R.descInc_injV K p 0
      baseE := R.descInc_injE K p 0
      baseF := R.descInc_injF K p 0
      zero_pi2 := fun r hr =>
        R.zeroPi2_descInc_succ K p hgen hcov hD hconnD hconnK d₀ r (by omega)
      baseStrict := desc_zero_ne_one R K p hKF (by omega)
      strict := fun r hr => desc_succ_ne_succ R K p hKF r (by omega) }

/-- **Condition (1) of Theorem A in its faithful form**: for every `n` there is a strictly
increasing chain `K ⊊ X₀ ⊊ ⋯ ⊊ Xₙ` of finite two-complexes whose inclusions are zero on
`π₂`. -/
def HasMapChains (K : Complex2.{u}) : Prop := ∀ n : ℕ, Nonempty (StrictTopChain K n)

/-- **Lemmas 3.1, 3.9, 3.10 in the map-carrying form**: over a connected acyclic complex
there are relative chains of every length carrying their inclusions, with finitely many cells
added at each stage. -/
def MapStep : Prop :=
  ∀ D : Complex2.{u}, IsAcyclic D → IsConnected D → ∀ n : ℕ,
    ∃ c : ℕ → Complex2.{u}, Nonempty (RelChainW D c n)

/-- **`(2) ⇒ (1)` for finite combinatorial two-complexes, in the faithful form**, from the
extension step and the generation statement (3.5). -/
theorem hasMapChains_of_mapStep (hstep : MapStep.{u}) (hgen : Pi2GeneratedByUpstairs.{u})
    {K : Complex2.{u}} [Finite K.E] [Finite K.F] (x₀ : K.V)
    (hK : HasAcyclicRegularCover K) : HasMapChains K := by
  obtain ⟨D, Q, hQ, p, A, hcov, hreg, hconnD, hacycD⟩ := hK
  intro n
  obtain ⟨c, ⟨R⟩⟩ := hstep D hacycD hconnD (n + 1)
  obtain ⟨d₀, -⟩ := hcov.surjV x₀
  exact ⟨strictTopChain_of_relChainW R p hcov hacycD hconnD inferInstance inferInstance d₀
    (hgen D K p)⟩

/-- **Theorem A for finite connected combinatorial two-complexes, with condition (1) in its
faithful, map-carrying form.**  The implication `(1) ⇒ (2)` is a theorem of this project; the
converse follows from the extension step of Lemmas 3.1, 3.9, 3.10 and from the generation
statement (3.5) of Proposition 3.11. -/
theorem theoremA_maps (hstep : MapStep.{u}) (hgen : Pi2GeneratedByUpstairs.{u})
    {K : Complex2.{u}} [Finite K.E] [Finite K.F] (hconn : IsConnected K) (x₀ : K.V) :
    HasMapChains K ↔ HasAcyclicRegularCover K :=
  ⟨fun h => hasAcyclicRegularCover_of_topChainsDisc hconn x₀
      (fun n => (h n).map StrictTopChain.toTopChainDisc),
    fun h => hasMapChains_of_mapStep hstep hgen x₀ h⟩

end Comb
end FiniteChains
