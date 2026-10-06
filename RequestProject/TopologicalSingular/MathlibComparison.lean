module

public import RequestProject.TopologicalSingular.SimplexCoordinates
public import RequestProject.Statement
public import RequestProject.TopologicalSingular.SingularChainHomotopy
public import RequestProject.TopologicalSingular.ContractibleSingularChains
public import RequestProject.FreeSingularChainComparison

@[expose] public section

open scoped ContinuousMap

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

set_option maxSynthPendingDepth 3
set_option synthInstance.maxHeartbeats 40000
set_option maxHeartbeats 800000

namespace FiniteChains.TopologicalSingular
open CategoryTheory AlgebraicTopology

/-- Removing the universe lift from singular simplices is a simplicial
isomorphism, not merely a degreewise bijection. -/
noncomputable def simplicesMathlibIso (X : TopCat.{0}) :
    simplices X ≅ TopCat.toSSet.obj X :=
  NatIso.ofComponents (fun n => (((simplexCoordinates n.unop.len).symm.arrowCongr (Homeomorph.refl X)).toEquiv.trans
      (TopCat.toSSetObjEquiv X n).symm).toIso) (by
    intro n m a
    apply ConcreteCategory.hom_ext
    intro σ
    change Simplex X n.unop.len at σ
    apply (TopCat.toSSetObjEquiv X m).injective
    apply ContinuousMap.ext
    intro z
    change σ (stdSimplex.map a.unop (simplexCoordinates m.unop.len z)) =
      σ (simplexCoordinates n.unop.len (Convexity.StdSimplex.map a.unop z))
    exact congrArg σ (simplexCoordinates_map a.unop z).symm)

/-- The explicit integral chains agree with Mathlib's free singular chains. -/
noncomputable def freeComplexMathlibIso (X : TopCat.{0}) :
    complex X ≅ AlternatingFaceMapComplex.obj (TopCat.toSSet.obj X ⋙ ModuleCat.free ℤ) :=
  (alternatingFaceMapComplex (ModuleCat.{0} ℤ)).mapIso
    (Functor.isoWhiskerRight (simplicesMathlibIso X) (ModuleCat.free ℤ))

theorem freeComplexMathlibIso_natural {X Y : TopCat.{0}} (f : X ⟶ Y) :
    chainMap f.hom ≫ (freeComplexMathlibIso Y).hom =
      (freeComplexMathlibIso X).hom ≫ AlternatingFaceMapComplex.map
        (Functor.whiskerRight (TopCat.toSSet.map f) (ModuleCat.free ℤ)) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply Finsupp.lhom_ext
  intro σ r
  change Finsupp.mapDomain _ (Finsupp.mapDomain _ (Finsupp.single σ r)) =
    Finsupp.mapDomain _ (Finsupp.mapDomain _ (Finsupp.single σ r))
  simp only [Finsupp.mapDomain_single]
  rfl

/-- The actual explicit singular chain complex computes the coefficients and
singular-homology functor occurring in `Whitehead.Acyclic`. -/
noncomputable def complexMathlibIso (X : TopCat.{0}) :
    complex X ≅ ((singularChainComplexFunctor (ModuleCat.{0} ℤ)).obj
      (ModuleCat.of ℤ ℤ)).obj X :=
  freeComplexMathlibIso X ≪≫ FiniteChains.freeSingularChainComplexIso X

theorem complexMathlibIso_natural {X Y : TopCat.{0}} (f : X ⟶ Y) :
    chainMap f.hom ≫ (complexMathlibIso Y).hom =
      (complexMathlibIso X).hom ≫ ((singularChainComplexFunctor (ModuleCat.{0} ℤ)).obj
        (ModuleCat.of ℤ ℤ)).map f := by
  dsimp only [complexMathlibIso, Iso.trans_hom]
  rw [← Category.assoc, freeComplexMathlibIso_natural, Category.assoc,
    FiniteChains.freeSingularChainComplexIso_natural, Category.assoc]

noncomputable def homologyMathlibIso (X : TopCat.{0}) (n : ℕ) :
    (complex X).homology n ≅ ((singularHomologyFunctor (ModuleCat.{0} ℤ) n).obj
      (ModuleCat.of ℤ ℤ)).obj X :=
  (HomologicalComplex.homologyFunctor (ModuleCat.{0} ℤ) (ComplexShape.down ℕ) n).mapIso
    (complexMathlibIso X)

theorem homologyMathlibIso_natural {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ) :
    HomologicalComplex.homologyMap (chainMap f.hom) n ≫ (homologyMathlibIso Y n).hom =
      (homologyMathlibIso X n).hom ≫ ((singularHomologyFunctor (ModuleCat.{0} ℤ) n).obj
        (ModuleCat.of ℤ ℤ)).map f := by
  change (HomologicalComplex.homologyFunctor (ModuleCat.{0} ℤ) (ComplexShape.down ℕ) n).map _ ≫
      (HomologicalComplex.homologyFunctor (ModuleCat.{0} ℤ) (ComplexShape.down ℕ) n).map _ =
    (HomologicalComplex.homologyFunctor (ModuleCat.{0} ℤ) (ComplexShape.down ℕ) n).map _ ≫
      (HomologicalComplex.homologyFunctor (ModuleCat.{0} ℤ) (ComplexShape.down ℕ) n).map _
  rw [← Functor.map_comp, ← Functor.map_comp, complexMathlibIso_natural]

/-- Homotopy invariance for the actual Mathlib singular-homology functor. -/
theorem mathlibHomologyMap_eq_of_homotopic {X Y : TopCat.{0}} (f g : X ⟶ Y)
    (h : f.hom.Homotopic g.hom) (n : ℕ) :
    ((singularHomologyFunctor (ModuleCat.{0} ℤ) n).obj (ModuleCat.of ℤ ℤ)).map f =
      ((singularHomologyFunctor (ModuleCat.{0} ℤ) n).obj (ModuleCat.of ℤ ℤ)).map g := by
  apply (cancel_epi (homologyMathlibIso X n).hom).mp
  rw [← homologyMathlibIso_natural, ← homologyMathlibIso_natural,
    homologyMap_eq_of_homotopic h n]

/-- Homotopy equivalent spaces have isomorphic actual integral singular homology. -/
noncomputable def mathlibHomologyIsoOfHomotopyEquiv {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₕ Y) (n : ℕ) :
    ((singularHomologyFunctor (ModuleCat.{0} ℤ) n).obj (ModuleCat.of ℤ ℤ)).obj (TopCat.of X) ≅
      ((singularHomologyFunctor (ModuleCat.{0} ℤ) n).obj (ModuleCat.of ℤ ℤ)).obj (TopCat.of Y) :=
  (homologyMathlibIso (TopCat.of X) n).symm ≪≫ homologyIsoOfHomotopyEquiv e n ≪≫
    homologyMathlibIso (TopCat.of Y) n

/-- The proved prism contraction gives exactness in every positive degree. -/
theorem contractible_complex_exactAt {X : Type} [TopologicalSpace X]
    [ContractibleSpace X] (n : ℕ) : (complex X).ExactAt (n + 1) := by
  rw [HomologicalComplex.exactAt_iff' (K := complex X) (i := n + 2) (j := n + 1) (k := n)
    (ChainComplex.prev ℕ (n + 1)) (ChainComplex.next_nat_succ n)]
  apply (ShortComplex.moduleCat_exact_iff_range_eq_ker _).mpr
  change LinearMap.range (((complex X).d (n + 2) (n + 1)).hom) =
    LinearMap.ker (((complex X).d (n + 1) n).hom)
  rw [complex_d, complex_d]
  exact (contractible_ker_boundary_eq_range n).symm

end FiniteChains.TopologicalSingular

namespace Whitehead
open CategoryTheory

/-- Contractible spaces are acyclic for the actual integral singular homology
used in the statement of Theorem A, in every positive degree. -/
theorem acyclic_of_contractible (X : Type) [TopologicalSpace X] [ContractibleSpace X] :
    Acyclic X := by
  intro n hn
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hn)
  exact (FiniteChains.TopologicalSingular.contractible_complex_exactAt (X := X) m).isZero_homology.of_iso
    (FiniteChains.TopologicalSingular.homologyMathlibIso (TopCat.of X) (m + 1)).symm

/-- Acyclicity in the original statement is invariant under homotopy equivalence. -/
theorem acyclic_iff_of_homotopyEquiv {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₕ Y) : Acyclic X ↔ Acyclic Y := by
  constructor
  · intro h n hn
    exact (h n hn).of_iso
      (FiniteChains.TopologicalSingular.mathlibHomologyIsoOfHomotopyEquiv e n).symm
  · intro h n hn
    exact (h n hn).of_iso
      (FiniteChains.TopologicalSingular.mathlibHomologyIsoOfHomotopyEquiv e n)

end Whitehead
