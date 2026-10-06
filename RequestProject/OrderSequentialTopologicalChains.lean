module

public import RequestProject.OrderEmbeddedTopologicalChains

@[expose] public section

namespace FiniteChains.Comb
open CategoryTheory
universe u

section Iteration
variable {P : ℕ → Type u} [∀ i, PartialOrder (P i)]
  (f : ∀ i, P i ↪o P (i + 1))

/-- Compose the actual successive order embeddings to put all stages into
one later stage. No separately chosen ambient embeddings are required. -/
def orderEmbeddingChain (i j : ℕ) (hij : i ≤ j) : P i ↪o P j where
  toFun := Nat.leRecOn (C := P) hij (fun {k} p => f k p)
  inj' := Nat.leRecOn_injective (C := P) hij (fun {k} p => f k p) (fun k => (f k).injective)
  map_rel_iff' := by
    intro x y
    change Nat.leRecOn (C := P) hij (fun {k} p => f k p) x ≤
      Nat.leRecOn (C := P) hij (fun {k} p => f k p) y ↔ x ≤ y
    induction hij with
    | refl => simp only [Nat.leRecOn_self]
    | @step j hij ih =>
      rw [Nat.leRecOn_succ hij, Nat.leRecOn_succ hij]
      exact (f j).le_iff_le.trans ih

theorem orderEmbeddingChain_self (i : ℕ) (p : P i) :
    orderEmbeddingChain f i i le_rfl p = p := Nat.leRecOn_self p

theorem orderEmbeddingChain_step (i j : ℕ) (hij : i + 1 ≤ j) (p : P i) :
    orderEmbeddingChain f i j (Nat.le_trans (Nat.le_succ i) hij) p =
      orderEmbeddingChain f (i + 1) j hij (f i p) :=
  (Nat.leRecOn_succ_left p (Nat.le_trans (Nat.le_succ i) hij) hij).symm

end Iteration

variable {P : ℕ → Type} [∀ i, PartialOrder (P i)] [∀ i, Nonempty (P i)]
  [∀ i, (nerve (P i)).HasDimensionLE 2]

/-- Successive proper order embeddings with actual pi2 vanishing construct
the exact length-n chain of CW subcomplexes inside the last stage. The
initial homeomorphism preserves its given open cells, and finiteness of
the last order supplies actual finite ambient CW cells. -/
theorem orderNerve_hasChain_of_successive_embeddings
    (f : ∀ i, P i ↪o P (i + 1)) (hc : ∀ i, IsConnected (orderCx (P i)))
    (n : ℕ)
    (hp : ∀ i, i < n → ∃ p : P (i + 1), p ∉ Set.range (f i))
    (hk : ∀ i, i < n → Whitehead.KillsPi2
      ⟨orderNerveRealizationMap (f i) (f i).monotone,
        (orderNerveRealizationMap (f i) (f i).monotone).hom.continuous⟩)
    (finite : Bool) (hfin : finite = true → Finite (P n)) :
    Whitehead.HasChain (orderNerveTwoComplex (P 0) (hc 0)) n finite := by
  let e (i : Fin (n + 1)) : P i.val ↪o P n :=
    orderEmbeddingChain f i.val n (Nat.le_of_lt_succ i.isLt)
  let s (i : Fin n) : P i.castSucc.val →o P i.succ.val := (f i.val).toOrderHom
  have he (i : Fin n) (p : P i.castSucc.val) : e i.castSucc p = e i.succ (s i p) :=
    orderEmbeddingChain_step f i.val n i.isLt p
  apply orderNerve_hasChain_of_embeddings (P := fun i : Fin (n + 1) => P i.val)
    e s he ?_ (hc n) (fun i => hc i.val) (fun i => hk i.val i.isLt) finite hfin
  intro i
  obtain ⟨p, hpn⟩ := hp i.val i.isLt
  refine ⟨p, ?_⟩
  rintro ⟨q, hq⟩
  apply hpn
  refine ⟨q, (e i.succ).injective ?_⟩
  exact (he i q).symm.trans hq

end FiniteChains.Comb
