import RequestProject.RelativeTreeExtensionMaps
import RequestProject.PresGeneratorRelabel
import RequestProject.TreePi1Reflection
import RequestProject.AcyclicPresentationRelativeCellChains

/-! The actual acyclic-core ambient construction lifted back from its
spanning-tree presentation to the original combinatorial complex. All
original vertices, edges, and faces remain literal old cells. Pending
final Lean verification. -/

noncomputable section
open scoped Classical
namespace FiniteChains.Comb.RelativeTreeAmbientChain
open SpanningTree RelativeNormalForm RelativeTreeExtension

variable {D : Complex2} (T : SpanningTree D) {n : ℕ}
  (c : AmbientChain (treeRel T) n)

def stageEdges : ℕ → Type
  | 0 => D.E
  | _ + 1 => D.E ⊕ c.extraGen

def stageSource : ∀ i, stageEdges T c i → D.V
  | 0 => D.src
  | _ + 1 => source T

def stageTarget : ∀ i, stageEdges T c i → D.V
  | 0 => D.tgt
  | _ + 1 => target T

def stageBase : ∀ i, c.chainCell i → D.V
  | 0 => D.base
  | _ + 1 => Sum.elim D.base (fun _ => T.root)

def stageAttaching : ∀ i, c.chainCell i → List (stageEdges T c i × Bool)
  | 0 => D.att
  | i + 1 => Sum.elim (fun f => oldPath (D.att f))
      (fun s => readWord T (restrictedExtra c.rel (c.stage i) s).toWord)

/-- Keep the face family definitionally equal to the ambient chain's
family also at a variable index; this avoids transporting face labels. -/
def stages (i : ℕ) : Complex2 where
  V := D.V
  E := stageEdges T c i
  F := c.chainCell i
  src := stageSource T c i
  tgt := stageTarget T c i
  base := stageBase T c i
  att := stageAttaching T c i
  att_isLoop := by
    cases i with
    | zero => exact D.att_isLoop
    | succ i => exact (complex T (restrictedExtra c.rel (c.stage i))).att_isLoop

def trees : ∀ i, SpanningTree (stages T c i)
  | 0 => T
  | i + 1 => tree T (restrictedExtra c.rel (c.stage i))

def inclusions : ∀ i, Hom (stages T c i) (stages T c (i + 1))
  | 0 => oldInclusion T (restrictedExtra c.rel (c.stage 0))
  | i + 1 => inclusion T (restrictedExtra c.rel (c.stage i))
      (restrictedExtra c.rel (c.stage (i + 1))) (labelIncl (c.mono i)) (fun _ => rfl)

theorem inclusions_V (i : ℕ) : Function.Injective (inclusions T c i).onV := by
  cases i <;> exact Function.injective_id

theorem inclusions_E (i : ℕ) : Function.Injective (inclusions T c i).onE := by
  cases i
  · exact Sum.inl_injective
  · exact Function.injective_id

theorem inclusions_F (i : ℕ) : Function.Injective (inclusions T c i).onF := by
  cases i with
  | zero => exact Sum.inl_injective
  | succ i =>
      exact c.chainCellIncl_injective (i + 1)

theorem trees_inclusions (i : ℕ) (e : (stages T c i).E) :
    (trees T c (i + 1)).isTree ((inclusions T c i).onE e) ↔
      (trees T c i).isTree e := by
  cases i <;> exact Iff.rfl

def generatorCoordinates : ∀ i, NonTree (trees T c i) ≃ c.chainGen i
  | 0 => Equiv.refl _
  | i + 1 => generatorEquiv T (restrictedExtra c.rel (c.stage i))

theorem relatorCoordinates (i : ℕ) (f : (stages T c i).F) :
    c.chainRel i f = FreeGroup.map (generatorCoordinates T c i)
      (treeRel (trees T c i) f) := by
  cases i with
  | zero => exact (FreeGroup.map.id (treeRel T f)).symm
  | succ i =>
      exact (treeRel_equation T (restrictedExtra c.rel (c.stage i)) f).symm

def presentationCoordinates (i : ℕ) :
    Hom (presComplex (treeRel (trees T c i))) (c.cellComplex i) :=
  PresGeneratorRelabel.forward (generatorCoordinates T c i) _ _ (relatorCoordinates T c i)

def inversePresentationCoordinates (i : ℕ) :
    Hom (c.cellComplex i) (presComplex (treeRel (trees T c i))) :=
  PresGeneratorRelabel.backward (generatorCoordinates T c i) _ _ (relatorCoordinates T c i)

def collapsedInclusion (i : ℕ) :
    Hom (presComplex (treeRel (trees T c i)))
      (presComplex (treeRel (trees T c (i + 1)))) :=
  presInclHom (nonTreeIncl (trees_inclusions T c i))
    (nonTreeIncl_injective (trees_inclusions T c i) (inclusions_E T c i))
    _ _ (inclusions T c i).onF (treeRel_onF (trees_inclusions T c i))

theorem generatorCoordinates_natural (i : ℕ) (a : NonTree (trees T c i)) :
    generatorCoordinates T c (i + 1) (nonTreeIncl (trees_inclusions T c i) a) =
      c.chainGenIncl i (generatorCoordinates T c i a) := by
  cases i with
  | zero => rfl
  | succ i => rcases a with ⟨a | z, ha⟩ <;> rfl

theorem presentationCoordinates_square (i : ℕ) :
    (presentationCoordinates T c (i + 1)).comp (collapsedInclusion T c i) =
      (c.cellInclusion i).comp (presentationCoordinates T c i) := by
  apply Hom.ext'
  · exact funext fun _ => rfl
  · exact funext (generatorCoordinates_natural T c i)
  · cases i <;> rfl

theorem zeroPi2_inclusions (hinj : Function.Injective (expMatrix (treeRel T)))
    (i : ℕ) (hi : i < n + 1) : ZeroPi2 (inclusions T c i) := by
  apply zeroPi2_of_zeroPi2_presInclHom (trees_inclusions T c i) (inclusions_E T c i)
  exact zeroPi2_of_retraction_square (collapsedInclusion T c i) (c.cellInclusion i)
    (presentationCoordinates T c i) (presentationCoordinates T c (i + 1))
    (inversePresentationCoordinates T c (i + 1))
    (PresGeneratorRelabel.backward_forward_V _ _ _ _)
    (PresGeneratorRelabel.backward_forward_E _ _ _ _)
    (PresGeneratorRelabel.backward_forward_F _ _ _ _)
    (presentationCoordinates_square T c i) (c.cellInclusion_zero hinj i hi)

theorem first_inclusion_pi1Trivial : Pi1Trivial (inclusions T c 0) := by
  apply pi1Trivial_of_pi1Trivial_presInclHom (trees_inclusions T c 0) (inclusions_E T c 0)
  exact pi1Trivial_of_retraction_square (collapsedInclusion T c 0) (c.cellInclusion 0)
    (presentationCoordinates T c 0) (presentationCoordinates T c 1)
    (inversePresentationCoordinates T c 1)
    (PresGeneratorRelabel.backward_forward_V _ _ _ _)
    (PresGeneratorRelabel.backward_forward_E _ _ _ _)
    (PresGeneratorRelabel.backward_forward_F _ _ _ _)
    (presentationCoordinates_square T c 0) c.first_cellInclusion_pi1Trivial

theorem inclFrom_pi1Trivial : ∀ i, 1 ≤ i →
    Pi1Trivial (inclFrom (stages T c) (inclusions T c) i)
  | 0, hi => by omega
  | 1, _ => fun a p hp => first_inclusion_pi1Trivial T c a p hp
  | i + 2, _ => Pi1Trivial.comp_left (inclusions T c (i + 1))
      (inclFrom_pi1Trivial (i + 1) (by omega))

theorem proper (i : ℕ) (hi : i < n + 1) :
    (¬ Function.Surjective (inclusions T c i).onE) ∨
      (¬ Function.Surjective (inclusions T c i).onF) := by
  cases i with
  | zero =>
      left
      intro hs
      obtain ⟨e, he⟩ := hs (Sum.inr c.fresh)
      exact Sum.inl_ne_inr he
  | succ i =>
      rcases c.chain_proper (i + 1) hi with ⟨a, ha⟩ | ⟨f, hf⟩
      · exact False.elim (ha ⟨a, rfl⟩)
      · right
        intro hs
        exact hf (hs f)

def relativeChain (hinj : Function.Injective (expMatrix (treeRel T))) :
    RelativeCellChain (stages T c) (n + 1) where
  inc := inclusions T c
  incV := inclusions_V T c
  incE := inclusions_E T c
  incF := inclusions_F T c
  conn := by
    intro i
    cases i with
    | zero =>
        intro a b
        exact ⟨revPath (T.treePath a) ++ T.treePath b,
          (isPath_revPath (T.treePath_isPath a)).append (T.treePath_isPath b)⟩
    | succ i => exact connected T (restrictedExtra c.rel (c.stage i))
  zero := zeroPi2_inclusions T c hinj
  pi1 := fun i hi _ => inclFrom_pi1Trivial T c i hi
  proper := proper T c

/-- An explicit relative chain over D itself, from the bijective
exponent boundary of its tree presentation. No cells of D are collapsed
in the resulting chain. -/
def actualRelativeChain (h : Function.Bijective (expMatrix (treeRel T))) (n : ℕ) :
    RelativeCellChain (stages T (actualAmbientChain (treeRel T) h n)) (n + 1) :=
  relativeChain T (actualAmbientChain (treeRel T) h n) h.1

end FiniteChains.Comb.RelativeTreeAmbientChain
