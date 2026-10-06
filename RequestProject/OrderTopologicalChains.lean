import RequestProject.SolutionLemmas
import RequestProject.OrderPi1TrivialLift

namespace FiniteChains.Comb
open CategoryTheory Topology

variable {P : Type} [PartialOrder P] [Nonempty P] [(nerve P).HasDimensionLE 2]
variable {n : ℕ} (A : Fin (n + 1) → Set P) [∀ i, Nonempty (A i)]

/-- A chain of induced subposets with proved topological pi2 conditions gives
exactly the CW chain required by Challenge, including the original open-cell
identification and the finite ambient-cell condition. -/
theorem orderNerve_hasChain
    (hP : IsConnected (orderCx P)) (hA : ∀ i, IsConnected (orderCx (A i)))
    (hs : ∀ i : Fin n, A i.castSucc ⊆ A i.succ)
    (hp : ∀ i : Fin n, ∃ p, p ∈ A i.succ ∧ p ∉ A i.castSucc)
    (hk : ∀ i : Fin n, Whitehead.KillsPi2
      ⟨orderNerveRealizationMap (Set.inclusion (hs i)) (fun _ _ h => h),
        (orderNerveRealizationMap (Set.inclusion (hs i)) (fun _ _ h => h)).hom.continuous⟩)
    (finite : Bool) (hfin : finite = true → Finite P) :
    letI := orderNerveSubtype_hasDimensionLE (A 0) 2
    Whitehead.HasChain (orderNerveTwoComplex (A 0) (hA 0)) n finite := by
  letI := orderNerveSubtype_hasDimensionLE (A 0) 2
  refine ⟨orderNerveTwoComplex P hP, fun i => orderNerveRealizationSubcomplex P (A i),
    orderNerveRealizationSubtypeHomeomorph (A 0),
    orderNerveRealizationSubtype_initialIdentification (A 0) hP (hA 0), ?_, ?_, ?_⟩
  · intro hf
    letI := hfin hf
    exact orderNerveTwoComplex_finiteCells P hP
  · intro i
    exact orderNerveRealizationSubcomplex_connectedSpace (A i) (hA i)
  · intro i
    obtain ⟨p, hpb, hpa⟩ := hp i
    exact ⟨orderNerveRealizationSubcomplex_mono (hs i),
      orderNerveRealizationSubcomplex_ne p hpb hpa,
      (Whitehead.killsPi2_orderNerve_subcomplex_inclusion_iff (hs i)).mpr (hk i)⟩

/-- The pi2 obligations of the actual CW chain are discharged by the genuine
Cockcroft property and the proved combinatorial pi1-triviality calculations. -/
theorem orderNerve_hasChain_of_cockcroft_pi1Trivial
    (hP : IsConnected (orderCx P)) (hA : ∀ i, IsConnected (orderCx (A i)))
    (hs : ∀ i : Fin n, A i.castSucc ⊆ A i.succ)
    (hp : ∀ i : Fin n, ∃ p, p ∈ A i.succ ∧ p ∉ A i.castSucc)
    (hc : ∀ i : Fin n, Whitehead.IsCockcroft (orderNerveRealization (A i.castSucc)))
    (ht : ∀ i : Fin n, Pi1Trivial
      (orderCxMap (Set.inclusion (hs i)) (fun _ _ h => h)))
    (finite : Bool) (hfin : finite = true → Finite P) :
    letI := orderNerveSubtype_hasDimensionLE (A 0) 2
    Whitehead.HasChain (orderNerveTwoComplex (A 0) (hA 0)) n finite := by
  apply orderNerve_hasChain A hP hA hs hp _ finite hfin
  intro i
  exact killsPi2_orderRealization_of_isCockcroft_of_pi1Trivial
    (Set.inclusion (hs i)) (fun _ _ h => h) (hA i.castSucc)
    (Classical.arbitrary (A i.castSucc)) (ht i) (hc i)

end FiniteChains.Comb
