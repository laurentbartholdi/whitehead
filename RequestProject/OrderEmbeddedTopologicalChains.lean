module

public import RequestProject.OrderNerveEmbeddingCells
public import RequestProject.OrderTopologicalChains

@[expose] public section

namespace FiniteChains.Comb
open CategoryTheory Topology

variable {n : ℕ} {P : Fin (n + 1) → Type} [∀ i, PartialOrder (P i)]
variable {Q : Type} [PartialOrder Q]

/-- A compatible family of embedded order models gives the exact chain of
actual CW subcomplexes, preserving the original cells of its first member.
The common ambient model must really be two-dimensional. -/
theorem orderNerve_hasChain_of_embeddings
    [∀ i, Nonempty (P i)] [Nonempty Q] [(nerve Q).HasDimensionLE 2]
    (e : ∀ i, P i ↪o Q)
    (f : ∀ i : Fin n, P i.castSucc →o P i.succ)
    (he : ∀ i : Fin n, ∀ p, e i.castSucc p = e i.succ (f i p))
    (hp : ∀ i : Fin n, ∃ p : P i.succ, e i.succ p ∉ Set.range (e i.castSucc))
    (hQ : IsConnected (orderCx Q)) (hP : ∀ i, IsConnected (orderCx (P i)))
    (hk : ∀ i : Fin n, Whitehead.KillsPi2
      ⟨orderNerveRealizationMap (f i) (f i).monotone,
        (orderNerveRealizationMap (f i) (f i).monotone).hom.continuous⟩)
    (finite : Bool) (hfin : finite = true → Finite Q) :
    letI := orderNerveEmbedding_hasDimensionLE (e 0) 2
    Whitehead.HasChain (orderNerveTwoComplex (P 0) (hP 0)) n finite := by
  letI := orderNerveEmbedding_hasDimensionLE (e 0) 2
  refine ⟨orderNerveTwoComplex Q hQ,
    fun i => orderNerveRealizationSubcomplex Q (Set.range (e i)),
    orderNerveRealizationEmbeddingHomeomorph (e 0),
    orderNerveRealizationEmbedding_initialIdentification (e 0) (hP 0) hQ, ?_, ?_, ?_⟩
  · intro hf
    letI := hfin hf
    exact orderNerveTwoComplex_finiteCells Q hQ
  · intro i
    letI := orderNerveRealization_pathConnectedSpace (P i) (hP i)
    exact (orderNerveRealizationEmbeddingHomeomorph (e i)).surjective.connectedSpace
      (orderNerveRealizationEmbeddingHomeomorph (e i)).continuous
  · intro i
    have hs : Set.range (e i.castSucc) ⊆ Set.range (e i.succ) := by
      rintro q ⟨p, rfl⟩
      exact ⟨f i p, (he i p).symm⟩
    obtain ⟨p, hpn⟩ := hp i
    refine ⟨orderNerveRealizationSubcomplex_mono hs,
      orderNerveRealizationSubcomplex_ne (e i.succ p) ⟨p, rfl⟩ hpn, ?_⟩
    apply (Whitehead.killsPi2_homeomorph_square_iff
      (orderNerveRealizationEmbeddingHomeomorph (e i.castSucc))
      (orderNerveRealizationEmbeddingHomeomorph (e i.succ))
      ⟨orderNerveRealizationMap (f i) (f i).monotone,
        (orderNerveRealizationMap (f i) (f i).monotone).hom.continuous⟩ _ ?_).mpr (hk i)
    apply ContinuousMap.ext
    intro x
    apply Subtype.ext
    change (orderNerveRealizationEmbeddingHomeomorph (e i.castSucc) x).val =
      (orderNerveRealizationEmbeddingHomeomorph (e i.succ)
        (orderNerveRealizationMap (f i) (f i).monotone x)).val
    rw [orderNerveRealizationEmbeddingHomeomorph_coe,
      orderNerveRealizationEmbeddingHomeomorph_coe, orderNerveRealizationMap_comp]
    have hcomp : (e i.succ ∘ f i : P i.castSucc → Q) = e i.castSucc :=
      funext (fun p => (he i p).symm)
    simp only [hcomp]

end FiniteChains.Comb
