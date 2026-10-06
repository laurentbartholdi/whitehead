module

public import RequestProject.PresWordDiskExtension
public import RequestProject.PresWordDiskComparisonNaturality
public import RequestProject.PresWordEmbeddingCombPi2
public import RequestProject.ClassicalCWModelSequenceTransfer
public import RequestProject.CanonicalPresentationTopologicalChains
public import RequestProject.PresentationChainFinsupp

@[expose] public section

/-! The actual relative disk models turn an algebraic presentation chain
into a chain retaining the original CW cells. The only initial comparison
input is a homotopy equivalence of spaces; no homeomorphism of the original
CW structure with a canonical presentation model is required. -/

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

set_option maxHeartbeats 200000

namespace FiniteChains.PresModel
open Comb RelativeAttachment
open scoped Classical

variable {α J : ℕ → Type}

def successiveEmbedding (f : ∀ i, α i ↪ α (i + 1)) (i j : ℕ) (hij : i ≤ j) : α i ↪ α j :=
  Nat.leRecOn (C := fun k => α i ↪ α k) hij
    (fun {k} e => e.trans (f k)) (Function.Embedding.refl _)

variable [∀ i, DecidableEq (α i)]
  (w : ∀ i, J i → List (α i × Bool))
  (e : ∀ i, PresWordEmbedding (w i) (w (i + 1)))
  (ρ : ∀ i, J i → FreeGroup (α i))
  (hw : ∀ i j, FreeGroup.mk (w i j) = ρ i j)
  (hpos : ∀ i j, 0 < (w i j).length)

/-- This produces the challenge's original-cell-preserving HasChain on
the supplied K, including a genuinely finite ambient complex when asked. -/
theorem original_hasChain_of_word_embeddings (K : Whitehead.TwoComplex)
    (e₀ : ContinuousMap.HomotopyEquiv
      (ClassicalPresWordDisks (w 0) (fun j => List.length_pos_iff.mp (hpos 0 j))) K)
    (n : ℕ)
    (hp : ∀ i, i < n → (∃ a : α (i + 1), a ∉ Set.range (e i).gen) ∨
      ∃ j : J (i + 1), j ∉ Set.range (e i).cell)
    (hz : ∀ i, i < n → ∀ c : PresGroup (ρ i) × J i →₀ ℤ,
      Comb.bdry2 (univCover (ρ i)) c = 0 →
      Finsupp.mapDomain (Prod.map ((e i).groupHom (ρ i) (ρ (i + 1)) (hw i) (hw (i + 1)))
        (e i).cell) c = 0)
    (finite : Bool)
    (hfin : finite = true → Whitehead.FiniteCells K ∧ Finite (α n) ∧ Finite (J n)) :
    Whitehead.HasChain K n finite := by
  let hne (i : ℕ) (j : J i) := List.length_pos_iff.mp (hpos i j)
  let M (i : ℕ) := (e i).classicalDiskExtension (hne i) (hne (i + 1))
  apply Whitehead.hasChain_of_diskExtensionModels M K e₀ n ?_ ?_ finite ?_
  · intro i hi
    rcases hp i hi with ⟨a, ha⟩ | ⟨j, hj⟩
    · exact Or.inl ((e i).classicalDiskExtension_nonempty_of_generator
        (hne i) (hne (i + 1)) a ha)
    · exact Or.inr ((e i).classicalDiskExtension_nonempty_of_relator
        (hne i) (hne (i + 1)) j hj)
  · intro i hi
    change Whitehead.KillsPi2 ((e i).classicalDiskExtension (hne i) (hne (i + 1))).map
    rw [(e i).classicalDiskExtension_map]
    apply ((e i).classicalWordDiskMap_killsPi2_iff (hne i) (hne (i + 1))).mpr
    exact ((e i).killsPi2_iff_univCover (hpos i) (hpos (i + 1))
      (ρ i) (ρ (i + 1)) (hw i) (hw (i + 1))).mpr (hz i hi)
  · intro hf
    obtain ⟨hK, hA, hJ⟩ := hfin hf
    refine ⟨hK, ?_⟩
    intro i hi
    letI : Finite (α n) := hA
    letI : Finite (J n) := hJ
    letI : Finite (α (i + 1)) := Finite.of_injective
      (successiveEmbedding (fun i => (e i).gen) (i + 1) n hi)
      (successiveEmbedding (fun i => (e i).gen) (i + 1) n hi).injective
    letI : Finite (J (i + 1)) := Finite.of_injective
      (successiveEmbedding (fun i => (e i).cell) (i + 1) n hi)
      (successiveEmbedding (fun i => (e i).cell) (i + 1) n hi).injective
    exact (e i).classicalDiskExtension_finite (hne i) (hne (i + 1))

end FiniteChains.PresModel

namespace FiniteChains.PresChainFS
open PresModel
open scoped Classical

variable {A C : Type} {core : C → FreeGroup A} {n : ℕ} (c : PresChainFS core n)

def stageWordDisks (i : ℕ) (a : c.gen i) : Type :=
  letI := c.decGen i
  ClassicalPresWordDisks (presCanonicalWords (c.rel i) a) (presCanonicalWords_ne_nil (c.rel i) a)

instance stageWordDisks_topology (i : ℕ) (a : c.gen i) : TopologicalSpace (c.stageWordDisks i a) := by
  unfold stageWordDisks
  infer_instance

theorem hasOriginalTopologicalChain (K : Whitehead.TwoComplex) (a : c.gen 0)
    (e₀ : ContinuousMap.HomotopyEquiv (c.stageWordDisks 0 a) K)
    (hp : ∀ i, i < n → (∃ b : c.gen (i + 1), b ∉ Set.range (c.genIncl i)) ∨
      ∃ j : c.cell (i + 1), j ∉ Set.range (c.cellIncl i))
    (finite : Bool)
    (hfin : finite = true → Whitehead.FiniteCells K ∧ Finite (c.gen n) ∧ Finite (c.cell n)) :
    Whitehead.HasChain K n finite := by
  letI : ∀ i, DecidableEq (c.gen i) := c.decGen
  let f (i : ℕ) : c.gen i ↪ c.gen (i + 1) := ⟨c.genIncl i, c.genIncl_injective i⟩
  let g (i : ℕ) : c.cell i ↪ c.cell (i + 1) := ⟨c.cellIncl i, c.cellIncl_injective i⟩
  exact original_hasChain_of_word_embeddings
    (fun i => presCanonicalWords (c.rel i) (presentationMarkedGenerator f a i))
    (canonicalPresentationStep c.rel f g c.rel_incl a) c.rel
    (fun i => mk_presCanonicalWords (c.rel i) (presentationMarkedGenerator f a i))
    (fun i => presCanonicalWords_positive (c.rel i) (presentationMarkedGenerator f a i))
    K e₀ n hp c.zero_pi2 finite hfin

end FiniteChains.PresChainFS
