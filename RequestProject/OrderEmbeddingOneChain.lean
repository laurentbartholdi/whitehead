import RequestProject.OrderEmbeddedTopologicalChains

namespace FiniteChains.Comb
open CategoryTheory Topology
variable {P Q : Type} [PartialOrder P] [PartialOrder Q]
  [Nonempty P] [Nonempty Q] [(nerve P).HasDimensionLE 2] [(nerve Q).HasDimensionLE 2]

/-- A proper embedding with a proved zero pi2 map gives the exact one-step chain,
including the original open-cell identification. -/
theorem orderNerve_hasChain_one_of_embedding (f : P ↪o Q)
    (hP : IsConnected (orderCx P)) (hQ : IsConnected (orderCx Q))
    (hp : ∃ q : Q, q ∉ Set.range f)
    (hk : Whitehead.KillsPi2
      ⟨orderNerveRealizationMap f f.monotone, (orderNerveRealizationMap f f.monotone).hom.continuous⟩)
    (finite : Bool) (hfin : finite = true → Finite Q) :
    Whitehead.HasChain (orderNerveTwoComplex P hP) 1 finite := by
  let g : Q ↪o Q := (OrderIso.refl Q).toOrderEmbedding
  let C : Fin 2 → CWComplex.Subcomplex (Set.univ : Set (orderNerveRealization Q)) :=
    Fin.cases (orderNerveRealizationSubcomplex Q (Set.range f))
      (fun _ => orderNerveRealizationSubcomplex Q (Set.range g))
  refine ⟨orderNerveTwoComplex Q hQ, C, orderNerveRealizationEmbeddingHomeomorph f,
    orderNerveRealizationEmbedding_initialIdentification f hP hQ, ?_, ?_, ?_⟩
  · intro hf
    letI := hfin hf
    exact orderNerveTwoComplex_finiteCells Q hQ
  · intro i
    fin_cases i
    · letI := orderNerveRealization_pathConnectedSpace P hP
      exact (orderNerveRealizationEmbeddingHomeomorph f).surjective.connectedSpace
        (orderNerveRealizationEmbeddingHomeomorph f).continuous
    · letI := orderNerveRealization_pathConnectedSpace Q hQ
      exact (orderNerveRealizationEmbeddingHomeomorph g).surjective.connectedSpace
        (orderNerveRealizationEmbeddingHomeomorph g).continuous
  · intro i
    fin_cases i
    have hs : Set.range f ⊆ Set.range g := by
      rintro q ⟨p, rfl⟩
      exact ⟨f p, rfl⟩
    obtain ⟨q, hq⟩ := hp
    refine ⟨orderNerveRealizationSubcomplex_mono hs,
      orderNerveRealizationSubcomplex_ne q ⟨q, rfl⟩ hq, ?_⟩
    apply (Whitehead.killsPi2_homeomorph_square_iff
      (orderNerveRealizationEmbeddingHomeomorph f)
      (orderNerveRealizationEmbeddingHomeomorph g)
      ⟨orderNerveRealizationMap f f.monotone,
        (orderNerveRealizationMap f f.monotone).hom.continuous⟩ _ ?_).mpr hk
    apply ContinuousMap.ext
    intro x
    apply Subtype.ext
    change (orderNerveRealizationEmbeddingHomeomorph f x).val =
      (orderNerveRealizationEmbeddingHomeomorph g (orderNerveRealizationMap f f.monotone x)).val
    rw [orderNerveRealizationEmbeddingHomeomorph_coe,
      orderNerveRealizationEmbeddingHomeomorph_coe]
    change _ = orderNerveRealizationMap id monotone_id _
    rw [orderNerveRealizationMap_id]

end FiniteChains.Comb
