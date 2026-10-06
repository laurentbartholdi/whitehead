module

public import RequestProject.AcyclicPresentationActualChains
public import RequestProject.PresWordDiskTopologicalChains
public import RequestProject.PresAcyclicExponentMatrix
public import RequestProject.TopologicalSingular.MathlibComparison

@[expose] public section

/-! The actual algebraic acyclic-core construction yields chains in the
literal original CW complex. Acyclicity of the original space and its actual
word-disk homotopy equivalence supply the exponent-boundary isomorphism;
the final theorems have no independent matrix hypothesis. -/

noncomputable section
namespace FiniteChains.RelativeNormalForm
open PresModel
open scoped Classical

variable {A C : Type} [dA : DecidableEq A] (core : C → FreeGroup A)
  (hcore : Function.Bijective (expMatrix core))

include hcore in
theorem actual_hasOriginalChain (K : Whitehead.TwoComplex) (a : A)
    (e₀ : ContinuousMap.HomotopyEquiv
      (ClassicalPresWordDisks (presCanonicalWords core a) (presCanonicalWords_ne_nil core a)) K)
    (n : ℕ) : Whitehead.HasChain K (n + 1) false := by
  have hd : dA = Classical.decEq A := Subsingleton.elim _ _
  subst dA
  let c := actualAmbientChain core hcore n
  apply (c.toPresChainFS hcore.1).hasOriginalTopologicalChain K a e₀ c.chain_proper false
  simp

include hcore in
theorem actual_hasOriginalFiniteChain [Finite A] [Finite C]
    (K : Whitehead.TwoComplex) (hK : Whitehead.FiniteCells K) (a : A)
    (e₀ : ContinuousMap.HomotopyEquiv
      (ClassicalPresWordDisks (presCanonicalWords core a) (presCanonicalWords_ne_nil core a)) K)
    (n : ℕ) : Whitehead.HasChain K (n + 1) true := by
  have hd : dA = Classical.decEq A := Subsingleton.elim _ _
  subst dA
  let c := actualAmbientChain core hcore n
  apply (c.toPresChainFS hcore.1).hasOriginalTopologicalChain K a e₀ c.chain_proper true
  intro _
  have h := actualAmbientChain_finite core hcore n
  letI : Finite c.extraGen := h.1
  letI : Finite c.extraCell := h.2
  change Whitehead.FiniteCells K ∧ Finite (A ⊕ c.extraGen) ∧
    Finite (C ⊕ {s // c.stage n s})
  exact ⟨hK, inferInstance, inferInstance⟩

/-- Transport the original singular acyclicity through the actual disk-model
comparison and extract the original presentation's exponent isomorphism. -/
theorem actual_expMatrix_bijective_of_acyclic
    (K : Whitehead.TwoComplex) (hK : Whitehead.Acyclic K) (a : A)
    (e₀ : ContinuousMap.HomotopyEquiv
      (ClassicalPresWordDisks (presCanonicalWords core a) (presCanonicalWords_ne_nil core a)) K) :
    Function.Bijective (expMatrix core) := by
  let e := (presClassicalDiskComparison (presCanonicalWords core a)
    (presCanonicalWords_ne_nil core a)).trans e₀
  have hmodel : Whitehead.Acyclic
      (Comb.orderNerveRealization (PresPos (presCanonicalWords core a))) :=
    (Whitehead.acyclic_iff_of_homotopyEquiv e).mpr hK
  exact expMatrix_bijective_of_presRealization_acyclic core (presCanonicalWords core a)
    (mk_presCanonicalWords core a) (presCanonicalWords_positive core a) hmodel

/-- Actual original-cell chains follow from singular acyclicity and the
constructed initial word-disk comparison, with arbitrary original labels. -/
theorem actual_hasOriginalChain_of_acyclic
    (K : Whitehead.TwoComplex) (hK : Whitehead.Acyclic K) (a : A)
    (e₀ : ContinuousMap.HomotopyEquiv
      (ClassicalPresWordDisks (presCanonicalWords core a) (presCanonicalWords_ne_nil core a)) K)
    (n : ℕ) : Whitehead.HasChain K (n + 1) false :=
  actual_hasOriginalChain core (actual_expMatrix_bijective_of_acyclic core K hK a e₀)
    K a e₀ n

/-- The finite original-cell version also derives its matrix premise from
actual singular acyclicity; finiteness is used only for the finite conclusion. -/
theorem actual_hasOriginalFiniteChain_of_acyclic [Finite A] [Finite C]
    (K : Whitehead.TwoComplex) (hfinite : Whitehead.FiniteCells K)
    (hK : Whitehead.Acyclic K) (a : A)
    (e₀ : ContinuousMap.HomotopyEquiv
      (ClassicalPresWordDisks (presCanonicalWords core a) (presCanonicalWords_ne_nil core a)) K)
    (n : ℕ) : Whitehead.HasChain K (n + 1) true :=
  actual_hasOriginalFiniteChain core (actual_expMatrix_bijective_of_acyclic core K hK a e₀)
    K hfinite a e₀ n

end FiniteChains.RelativeNormalForm
