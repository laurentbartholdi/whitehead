module

public import RequestProject.CombPushout

@[expose] public section

/-!
# Descending a chain along a covering: the combinatorial part of Proposition 3.11

Proposition 3.11 takes a chain `D = L₀ ⊆ L₁ ⊆ ⋯ ⊆ Lₙ` over an acyclic regular cover
`p : D → K` and descends it to a chain over `K` by forming the cellular pushouts
`Eᵢ = K ∪_p Lᵢ`.  Using the pushout of `RequestProject/CombPushout.lean` this file builds the
descended sequence and proves everything about it except the homotopy-theoretic statement
that its inclusions are zero on `π₂`:

* `FiniteChains.Comb.chainIncl` — the inclusion `L₀ ⊆ Lᵢ` obtained by composing the steps of
  the chain, and its injectivity;
* `FiniteChains.Comb.descentChain` — the descended sequence `E₀ = K`, `Eᵢ = K ∪_p Lᵢ`;
* `FiniteChains.Comb.descentChain_sub` — **every term is a subcomplex of the next**, so the
  descended sequence really is a chain of two-complexes starting at `K`;
* `FiniteChains.Comb.descentChain_finite_E`, `FiniteChains.Comb.descentChain_finite_F` — the
  stages are finite as soon as `K` is finite and each `Lᵢ` has only finitely many cells off
  `L₀`;
* `FiniteChains.Comb.descentChain_isConnected` — the stages are connected;
* `FiniteChains.Comb.exists_descentChain` — the packaged existence statement.

The chain upstairs is indexed by all of `ℕ`; a chain of finite length `n` is put in this form
by repeating its last term (`FiniteChains.Comb.sub_truncate`).
-/

namespace FiniteChains
namespace Comb

universe u

variable {K : Complex2.{u}} {c : ℕ → Complex2.{u}}

/-! ### The inclusions of a chain -/

/-- A chain of length `n`, extended to all of `ℕ` by repeating its last term, is a chain of
subcomplexes at every index. -/
theorem sub_truncate {n : ℕ} (hsub : ∀ i < n, Sub (c i) (c (i + 1))) (i : ℕ) :
    Sub (c (min i n)) (c (min (i + 1) n)) := by
  rcases lt_or_ge i n with h | h
  · rw [min_eq_left h.le, min_eq_left h]
    exact hsub i h
  · rw [min_eq_right h, min_eq_right (by omega)]
    exact Sub.refl _

variable (c) in
/-- The chosen inclusion of one term of the chain into the next. -/
noncomputable def chainStep (hsub : ∀ i, Sub (c i) (c (i + 1))) (i : ℕ) : Hom (c i) (c (i + 1)) :=
  (hsub i).choose

theorem chainStep_injV (hsub : ∀ i, Sub (c i) (c (i + 1))) (i : ℕ) :
    Function.Injective (chainStep c hsub i).onV := (hsub i).choose_spec.1

theorem chainStep_injE (hsub : ∀ i, Sub (c i) (c (i + 1))) (i : ℕ) :
    Function.Injective (chainStep c hsub i).onE := (hsub i).choose_spec.2.1

theorem chainStep_injF (hsub : ∀ i, Sub (c i) (c (i + 1))) (i : ℕ) :
    Function.Injective (chainStep c hsub i).onF := (hsub i).choose_spec.2.2

variable (c) in
/-- The inclusion of the first term of the chain into the `i`-th one. -/
noncomputable def chainIncl (hsub : ∀ i, Sub (c i) (c (i + 1))) : ∀ i : ℕ, Hom (c 0) (c i)
  | 0 => Hom.id (c 0)
  | i + 1 => (chainStep c hsub i).comp (chainIncl hsub i)

theorem chainIncl_succ (hsub : ∀ i, Sub (c i) (c (i + 1))) (i : ℕ) :
    chainIncl c hsub (i + 1) = (chainStep c hsub i).comp (chainIncl c hsub i) := rfl

theorem chainIncl_injV (hsub : ∀ i, Sub (c i) (c (i + 1))) :
    ∀ i, Function.Injective (chainIncl c hsub i).onV
  | 0 => fun _ _ h => h
  | i + 1 => (chainStep_injV hsub i).comp (chainIncl_injV hsub i)

theorem chainIncl_injE (hsub : ∀ i, Sub (c i) (c (i + 1))) :
    ∀ i, Function.Injective (chainIncl c hsub i).onE
  | 0 => fun _ _ h => h
  | i + 1 => (chainStep_injE hsub i).comp (chainIncl_injE hsub i)

theorem chainIncl_injF (hsub : ∀ i, Sub (c i) (c (i + 1))) :
    ∀ i, Function.Injective (chainIncl c hsub i).onF
  | 0 => fun _ _ h => h
  | i + 1 => (chainStep_injF hsub i).comp (chainIncl_injF hsub i)

/-! ### The descended chain -/

variable (K) in
/-- **The chain `Eᵢ = K ∪_p Lᵢ` downstairs.**  The zeroth term is `K` itself; the `(i+1)`-st
is the cellular pushout of `K ← L₀ ⊆ L_{i+1}` along the covering `p`. -/
noncomputable def descentChain (p : Hom (c 0) K) (hsub : ∀ i, Sub (c i) (c (i + 1))) :
    ℕ → Complex2.{u}
  | 0 => K
  | i + 1 =>
      pushoutComplex p (chainIncl c hsub (i + 1)) (chainIncl_injV hsub (i + 1))
        (chainIncl_injE hsub (i + 1))

@[simp] theorem descentChain_zero (p : Hom (c 0) K) (hsub : ∀ i, Sub (c i) (c (i + 1))) :
    descentChain K p hsub 0 = K := rfl

theorem descentChain_succ (p : Hom (c 0) K) (hsub : ∀ i, Sub (c i) (c (i + 1))) (i : ℕ) :
    descentChain K p hsub (i + 1) =
      pushoutComplex p (chainIncl c hsub (i + 1)) (chainIncl_injV hsub (i + 1))
        (chainIncl_injE hsub (i + 1)) := rfl

/-- **Each term of the descended chain is a subcomplex of the next.** -/
theorem descentChain_sub (p : Hom (c 0) K) (hsub : ∀ i, Sub (c i) (c (i + 1))) (i : ℕ) :
    Sub (descentChain K p hsub i) (descentChain K p hsub (i + 1)) := by
  cases i with
  | zero =>
      exact sub_pushoutComplex p (chainIncl c hsub 1) (chainIncl_injV hsub 1)
        (chainIncl_injE hsub 1)
  | succ i =>
      exact sub_pushout_of_sub p (chainIncl c hsub (i + 1)) (chainIncl c hsub (i + 2))
        (chainStep c hsub (i + 1)) (chainIncl_injV hsub (i + 1)) (chainIncl_injE hsub (i + 1))
        (chainIncl_injV hsub (i + 2)) (chainIncl_injE hsub (i + 2)) (chainIncl_injF hsub (i + 2))
        (chainStep_injV hsub (i + 1)) (chainStep_injE hsub (i + 1)) (chainStep_injF hsub (i + 1))
        rfl

/-- `K` is a subcomplex of every term of the descended chain. -/
theorem sub_descentChain (p : Hom (c 0) K) (hsub : ∀ i, Sub (c i) (c (i + 1))) :
    ∀ i, Sub K (descentChain K p hsub i)
  | 0 => Sub.refl K
  | i + 1 => (sub_descentChain p hsub i).trans (descentChain_sub p hsub i)

/-! ### Finiteness of the stages -/

theorem descentChain_finite_V (p : Hom (c 0) K) (hsub : ∀ i, Sub (c i) (c (i + 1)))
    (hK : Finite K.V) (hoff : ∀ i, Finite (OffV (chainIncl c hsub i))) :
    ∀ i, Finite (descentChain K p hsub i).V
  | 0 => hK
  | i + 1 => by
      have := hoff (i + 1)
      exact inferInstanceAs (Finite (K.V ⊕ OffV (chainIncl c hsub (i + 1))))

theorem descentChain_finite_E (p : Hom (c 0) K) (hsub : ∀ i, Sub (c i) (c (i + 1)))
    (hK : Finite K.E) (hoff : ∀ i, Finite (OffE (chainIncl c hsub i))) :
    ∀ i, Finite (descentChain K p hsub i).E
  | 0 => hK
  | i + 1 => by
      have := hoff (i + 1)
      exact inferInstanceAs (Finite (K.E ⊕ OffE (chainIncl c hsub (i + 1))))

theorem descentChain_finite_F (p : Hom (c 0) K) (hsub : ∀ i, Sub (c i) (c (i + 1)))
    (hK : Finite K.F) (hoff : ∀ i, Finite (OffF (chainIncl c hsub i))) :
    ∀ i, Finite (descentChain K p hsub i).F
  | 0 => hK
  | i + 1 => by
      have := hoff (i + 1)
      exact inferInstanceAs (Finite (K.F ⊕ OffF (chainIncl c hsub (i + 1))))

/-- Every stage of the descended chain is connected. -/
theorem descentChain_isConnected (p : Hom (c 0) K) (hsub : ∀ i, Sub (c i) (c (i + 1)))
    (hK : IsConnected K) (hconn : ∀ i, IsConnected (c i)) (v₀ : (c 0).V) :
    ∀ i, IsConnected (descentChain K p hsub i)
  | 0 => hK
  | i + 1 =>
      isConnected_pushoutComplex p (chainIncl c hsub (i + 1)) (chainIncl_injV hsub (i + 1))
        (chainIncl_injE hsub (i + 1)) hK (hconn (i + 1)) v₀

/-! ### Strictness of the descended chain -/

/-- Two complexes with different numbers of two-cells are different. -/
theorem ne_of_card_F_lt {X Y : Complex2.{u}} (h : Nat.card X.F < Nat.card Y.F) : X ≠ Y :=
  fun hxy => absurd (congrArg (fun Z : Complex2.{u} => Nat.card Z.F) hxy) (Nat.ne_of_lt h)

/-- **The first step of the descended chain is strict** as soon as the chain upstairs has a
two-cell off its first term (and the relevant cell sets are finite). -/
theorem descentChain_zero_ne_one (p : Hom (c 0) K) (hsub : ∀ i, Sub (c i) (c (i + 1)))
    (hK : Finite K.F) (hoff : Finite (OffF (chainIncl c hsub 1)))
    (f : OffF (chainIncl c hsub 1)) :
    descentChain K p hsub 0 ≠ descentChain K p hsub 1 := by
  refine ne_of_card_F_lt ?_
  have h1 : Nat.card (descentChain K p hsub 1).F =
      Nat.card K.F + Nat.card (OffF (chainIncl c hsub 1)) :=
    Nat.card_sum
  have h2 : 0 < Nat.card (OffF (chainIncl c hsub 1)) := Nat.card_pos_iff.2 ⟨⟨f⟩, hoff⟩
  show Nat.card K.F < Nat.card (descentChain K p hsub 1).F
  omega

/-- **The later steps of the descended chain are strict** as soon as the corresponding step of
the chain upstairs adds a two-cell (and the relevant cell sets are finite). -/
theorem descentChain_succ_ne_succ (p : Hom (c 0) K) (hsub : ∀ i, Sub (c i) (c (i + 1))) (i : ℕ)
    (hK : Finite K.F) (h1 : Finite (OffF (chainIncl c hsub (i + 1))))
    (h2 : Finite (OffF (chainIncl c hsub (i + 2)))) (f : OffF (chainStep c hsub (i + 1))) :
    descentChain K p hsub (i + 1) ≠ descentChain K p hsub (i + 2) := by
  have hfoff : ∀ d, (chainIncl c hsub (i + 2)).onF d ≠ f.1 := fun d => f.2 _
  set g : OffF (chainIncl c hsub (i + 1)) → OffF (chainIncl c hsub (i + 2)) :=
    fun w => ⟨(chainStep c hsub (i + 1)).onF w.1,
      off_map_F (chainStep_injF hsub (i + 1)) rfl w⟩
  have hginj : Function.Injective g := by
    intro w w' hww
    exact Subtype.ext (chainStep_injF hsub (i + 1) (congrArg Subtype.val hww))
  have hnotmem : (⟨f.1, hfoff⟩ : OffF (chainIncl c hsub (i + 2))) ∉ Set.range g := by
    rintro ⟨w, hw⟩
    exact f.2 w.1 (congrArg Subtype.val hw)
  have hlt : Nat.card (OffF (chainIncl c hsub (i + 1))) <
      Nat.card (OffF (chainIncl c hsub (i + 2))) := by
    have hle := Nat.card_le_card_of_injective g hginj
    rcases lt_or_eq_of_le hle with h | h
    · exact h
    · exact absurd (((Nat.bijective_iff_injective_and_card g).2 ⟨hginj, h⟩).2 _) hnotmem
  refine ne_of_card_F_lt ?_
  have e1 : Nat.card (descentChain K p hsub (i + 1)).F =
      Nat.card K.F + Nat.card (OffF (chainIncl c hsub (i + 1))) := Nat.card_sum
  have e2 : Nat.card (descentChain K p hsub (i + 2)).F =
      Nat.card K.F + Nat.card (OffF (chainIncl c hsub (i + 2))) := Nat.card_sum
  omega

/-- Two complexes with different numbers of vertices are different. -/
theorem ne_of_card_V_lt {X Y : Complex2.{u}} (h : Nat.card X.V < Nat.card Y.V) : X ≠ Y :=
  fun hxy => absurd (congrArg (fun Z : Complex2.{u} => Nat.card Z.V) hxy) (Nat.ne_of_lt h)

/-- Two complexes with different numbers of edges are different. -/
theorem ne_of_card_E_lt {X Y : Complex2.{u}} (h : Nat.card X.E < Nat.card Y.E) : X ≠ Y :=
  fun hxy => absurd (congrArg (fun Z : Complex2.{u} => Nat.card Z.E) hxy) (Nat.ne_of_lt h)

/-- The vertex analogue of `FiniteChains.Comb.descentChain_succ_ne_succ`: a step of the chain
upstairs which adds a vertex makes the corresponding step downstairs strict. -/
theorem descentChain_succ_ne_succ_of_offV (p : Hom (c 0) K) (hsub : ∀ i, Sub (c i) (c (i + 1)))
    (i : ℕ) (hK : Finite K.V) (h1 : Finite (OffV (chainIncl c hsub (i + 1))))
    (h2 : Finite (OffV (chainIncl c hsub (i + 2)))) (v : OffV (chainStep c hsub (i + 1))) :
    descentChain K p hsub (i + 1) ≠ descentChain K p hsub (i + 2) := by
  have hvoff : ∀ d, (chainIncl c hsub (i + 2)).onV d ≠ v.1 := fun d => v.2 _
  set g : OffV (chainIncl c hsub (i + 1)) → OffV (chainIncl c hsub (i + 2)) :=
    fun w => ⟨(chainStep c hsub (i + 1)).onV w.1,
      off_map_V (chainStep_injV hsub (i + 1)) rfl w⟩
  have hginj : Function.Injective g := fun w w' hww =>
    Subtype.ext (chainStep_injV hsub (i + 1) (congrArg Subtype.val hww))
  have hnotmem : (⟨v.1, hvoff⟩ : OffV (chainIncl c hsub (i + 2))) ∉ Set.range g := by
    rintro ⟨w, hw⟩
    exact v.2 w.1 (congrArg Subtype.val hw)
  have hlt : Nat.card (OffV (chainIncl c hsub (i + 1))) <
      Nat.card (OffV (chainIncl c hsub (i + 2))) := by
    rcases lt_or_eq_of_le (Nat.card_le_card_of_injective g hginj) with h | h
    · exact h
    · exact absurd (((Nat.bijective_iff_injective_and_card g).2 ⟨hginj, h⟩).2 _) hnotmem
  refine ne_of_card_V_lt ?_
  have e1 : Nat.card (descentChain K p hsub (i + 1)).V =
      Nat.card K.V + Nat.card (OffV (chainIncl c hsub (i + 1))) := Nat.card_sum
  have e2 : Nat.card (descentChain K p hsub (i + 2)).V =
      Nat.card K.V + Nat.card (OffV (chainIncl c hsub (i + 2))) := Nat.card_sum
  omega

/-- The edge analogue of `FiniteChains.Comb.descentChain_succ_ne_succ`. -/
theorem descentChain_succ_ne_succ_of_offE (p : Hom (c 0) K) (hsub : ∀ i, Sub (c i) (c (i + 1)))
    (i : ℕ) (hK : Finite K.E) (h1 : Finite (OffE (chainIncl c hsub (i + 1))))
    (h2 : Finite (OffE (chainIncl c hsub (i + 2)))) (e : OffE (chainStep c hsub (i + 1))) :
    descentChain K p hsub (i + 1) ≠ descentChain K p hsub (i + 2) := by
  have heoff : ∀ d, (chainIncl c hsub (i + 2)).onE d ≠ e.1 := fun d => e.2 _
  set g : OffE (chainIncl c hsub (i + 1)) → OffE (chainIncl c hsub (i + 2)) :=
    fun w => ⟨(chainStep c hsub (i + 1)).onE w.1,
      off_map_E (chainStep_injE hsub (i + 1)) rfl w⟩
  have hginj : Function.Injective g := fun w w' hww =>
    Subtype.ext (chainStep_injE hsub (i + 1) (congrArg Subtype.val hww))
  have hnotmem : (⟨e.1, heoff⟩ : OffE (chainIncl c hsub (i + 2))) ∉ Set.range g := by
    rintro ⟨w, hw⟩
    exact e.2 w.1 (congrArg Subtype.val hw)
  have hlt : Nat.card (OffE (chainIncl c hsub (i + 1))) <
      Nat.card (OffE (chainIncl c hsub (i + 2))) := by
    rcases lt_or_eq_of_le (Nat.card_le_card_of_injective g hginj) with h | h
    · exact h
    · exact absurd (((Nat.bijective_iff_injective_and_card g).2 ⟨hginj, h⟩).2 _) hnotmem
  refine ne_of_card_E_lt ?_
  have e1 : Nat.card (descentChain K p hsub (i + 1)).E =
      Nat.card K.E + Nat.card (OffE (chainIncl c hsub (i + 1))) := Nat.card_sum
  have e2 : Nat.card (descentChain K p hsub (i + 2)).E =
      Nat.card K.E + Nat.card (OffE (chainIncl c hsub (i + 2))) := Nat.card_sum
  omega

/-! ### The packaged statement -/

/-- **The combinatorial half of Proposition 3.11.**  A chain over `L₀` together with a
cellular map `p : L₀ → K` yields a chain of two-complexes starting at `K`, with finite stages
as soon as `K` is finite and each term of the chain upstairs has only finitely many cells off
`L₀`.  Only the vanishing of the induced maps on `π₂` is left open. -/
theorem exists_descentChain (p : Hom (c 0) K) (hsub : ∀ i, Sub (c i) (c (i + 1)))
    (hKE : Finite K.E) (hKF : Finite K.F)
    (hoffE : ∀ (i : ℕ) (h : Hom (c 0) (c i)), Finite (OffE h))
    (hoffF : ∀ (i : ℕ) (h : Hom (c 0) (c i)), Finite (OffF h)) :
    ∃ e : ℕ → Complex2.{u}, e 0 = K ∧ (∀ i, Sub (e i) (e (i + 1))) ∧
      (∀ i, Finite (e i).E) ∧ (∀ i, Finite (e i).F) :=
  ⟨descentChain K p hsub, rfl, descentChain_sub p hsub,
    descentChain_finite_E p hsub hKE fun i => hoffE i (chainIncl c hsub i),
    descentChain_finite_F p hsub hKF fun i => hoffF i (chainIncl c hsub i)⟩

end Comb
end FiniteChains
