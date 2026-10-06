import RequestProject.InitialPairFinsupp
import RequestProject.RelativeAmbientPresChain

/-! The acyclic-core sufficiency construction with its explicit initial
pair, actual genus replacement, actual terminal extension, and actual
topological presentation realization all supplied. Unverified source. -/

noncomputable section
open scoped Classical

namespace FiniteChains

theorem FSIsCockcroft.redecide {A J : Type} [dA : DecidableEq A]
    {ρ : J → FreeGroup A} (h : FSIsCockcroft ρ) (dA' : DecidableEq A) :
    @FSIsCockcroft A J dA' ρ := by
  have hd : dA' = dA := Subsingleton.elim _ _
  subst dA'
  exact h

end FiniteChains

namespace FiniteChains.RelativeNormalForm
variable {A C : Type} (core : C → FreeGroup A)
  (hcore : Function.Bijective (expMatrix core))

def actualInitial : AmbientChain core 0 := by
  refine AmbientChain.initial (core := core) (InitialFS.fresh A) (InitialFS.extra core)
    ?_ (InitialFS.core_trivial core hcore.2)
  exact @FSIsCockcroft.redecide _ _ _ _ (InitialFS.isCockcroft core hcore) _

def actualAmbientChain (n : ℕ) : AmbientChain core n :=
  ambientChains core hcore (actualInitial core hcore) n

def actualPresChain (n : ℕ) : PresChainFS core (n + 1) :=
  (actualAmbientChain core hcore n).toPresChainFS hcore.1

theorem actualAmbientChain_finite [Finite A] (n : ℕ) :
    Finite (actualAmbientChain core hcore n).extraGen ∧
      Finite (actualAmbientChain core hcore n).extraCell := by
  induction n with
  | zero =>
      change Finite (InitialFS.ExtraGen A) ∧ Finite (InitialFS.ExtraCell A)
      constructor
      · infer_instance
      · unfold InitialFS.ExtraCell
        infer_instance
  | succ n ih =>
      letI := ih.1
      letI := ih.2
      change Finite (NextExtraGen core hcore.2 (actualAmbientChain core hcore n).rel) ∧
        Finite (NextExtraCell core hcore.2 (actualAmbientChain core hcore n).rel)
      constructor <;> infer_instance

include hcore in
/-- Arbitrary supported acyclic presentations have strict topological
chains of every positive length. The initial presentation cells are the
unchanged core cells at stage zero. -/
theorem actual_hasChain (a : A) (n : ℕ) :
    Whitehead.HasChain (PresModel.validPresTwoComplex (PresModel.presCanonicalWords core a)
      (PresModel.presCanonicalWords_ne_nil core a)) (n + 1) false :=
  (actualAmbientChain core hcore n).hasTopologicalChain hcore.1 a false (by simp)

include hcore in
/-- Finite acyclic presentations give finite final ambient complexes. -/
theorem actual_hasFiniteChain [Finite A] [Finite C] (a : A) (n : ℕ) :
    Whitehead.HasChain (PresModel.validPresTwoComplex (PresModel.presCanonicalWords core a)
      (PresModel.presCanonicalWords_ne_nil core a)) (n + 1) true := by
  apply (actualAmbientChain core hcore n).hasTopologicalChain hcore.1 a true
  intro _
  exact ⟨inferInstance, inferInstance, (actualAmbientChain_finite core hcore n).1,
    (actualAmbientChain_finite core hcore n).2⟩

end FiniteChains.RelativeNormalForm
