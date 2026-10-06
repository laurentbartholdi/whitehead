module

public import RequestProject.AcyclicPresentationActualChains
public import RequestProject.RegularCoverChainDescent

@[expose] public section

/-! Retain the actual maps and the triviality on fundamental groups in
the acyclic presentation construction. These data are needed by regular
cover descent and are lost if one retains only the existence of HasChain.
 -/

noncomputable section
open scoped Classical

namespace FiniteChains.RelativeNormalForm.AmbientChain
open Comb

variable {A C : Type} {core : C → FreeGroup A} {n : ℕ}
  (c : AmbientChain core n)

def cellComplex (i : ℕ) : Complex2 := presComplex (c.chainRel i)

def cellInclusion (i : ℕ) : Hom (c.cellComplex i) (c.cellComplex (i + 1)) :=
  presInclHom (c.chainGenIncl i) (c.chainGenIncl_injective i)
    (c.chainRel i) (c.chainRel (i + 1)) (c.chainCellIncl i) (c.chainRel_incl i)

theorem cellInclusion_zero (hinj : Function.Injective (expMatrix core))
    (i : ℕ) (hi : i < n + 1) : ZeroPi2 (c.cellInclusion i) := by
  apply (zeroPi2_presInclHom_iff (ρ := c.chainRel i) (σ := c.chainRel (i + 1))
    (c.chainGenIncl i) (c.chainGenIncl_injective i)
    (c.chainCellIncl i) (c.chainRel_incl i)).mpr
  exact (c.toPresChainFS hinj).zero_pi2 i hi

theorem first_cellInclusion_pi1Trivial : Pi1Trivial (c.cellInclusion 0) := by
  apply (pi1Trivial_presInclHom_iff (ρ := c.chainRel 0) (σ := c.chainRel 1)
    (c.chainGenIncl 0) (c.chainGenIncl_injective 0)
    (c.chainCellIncl 0) (c.chainRel_incl 0)).mpr
  intro w
  induction w using QuotientGroup.induction_on with
  | H w =>
      let f : FreeGroup A →* PresGroup (c.chainRel 1) :=
        (QuotientGroup.mk' (relSub (c.chainRel 1))).comp (FreeGroup.map Sum.inl)
      have hf : f = 1 := by
        apply FreeGroup.ext_hom
        intro a
        change (QuotientGroup.mk (FreeGroup.map Sum.inl (FreeGroup.of a)) :
          PresGroup (c.chainRel 1)) = 1
        exact c.core_trivial 0 a
      change (QuotientGroup.mk (FreeGroup.map Sum.inl w) : PresGroup (c.chainRel 1)) = 1
      exact DFunLike.congr_fun hf w

theorem cellInclFrom_pi1Trivial : ∀ i, 1 ≤ i →
    Pi1Trivial (inclFrom c.cellComplex c.cellInclusion i)
  | 0, hi => by omega
  | 1, _ => fun a p hp => c.first_cellInclusion_pi1Trivial a p hp
  | i + 2, _ => Pi1Trivial.comp_left (c.cellInclusion (i + 1))
      (cellInclFrom_pi1Trivial (i + 1) (by omega))

/-- The same fixed-core construction with all the data required for
regular-cover descent, for arbitrary generator and relator sets. -/
def toRelativeCellChain (hinj : Function.Injective (expMatrix core)) :
    RelativeCellChain c.cellComplex (n + 1) where
  inc := c.cellInclusion
  incV := by
    intro i a b _
    exact @Subsingleton.elim PUnit inferInstance a b
  incE := c.chainGenIncl_injective
  incF := c.chainCellIncl_injective
  conn := by
    intro i a b
    exact ⟨[], @Subsingleton.elim PUnit inferInstance a b⟩
  zero := c.cellInclusion_zero hinj
  pi1 := fun i hi _ => c.cellInclFrom_pi1Trivial i hi
  proper := by
    intro i hi
    rcases c.chain_proper i hi with ⟨a, ha⟩ | ⟨j, hj⟩
    · left
      intro hs
      exact ha (hs a)
    · right
      intro hs
      exact hj (hs j)

end FiniteChains.RelativeNormalForm.AmbientChain

namespace FiniteChains.RelativeNormalForm
open Comb
variable {A C : Type} (core : C → FreeGroup A)
  (hcore : Function.Bijective (expMatrix core))

def actualRelativeCellChain (n : ℕ) :
    RelativeCellChain (actualAmbientChain core hcore n).cellComplex (n + 1) :=
  (actualAmbientChain core hcore n).toRelativeCellChain hcore.1

end FiniteChains.RelativeNormalForm
