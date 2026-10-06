import RequestProject.FreeIntegerCoproduct
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Abelian

namespace FiniteChains
open CategoryTheory

/-- Free integral chains on the actual singular simplicial set are naturally
isomorphic to the actual Mathlib singular chain complex with integral coefficients. -/
noncomputable def freeSingularChainComplexIso (X : TopCat) :
    AlgebraicTopology.AlternatingFaceMapComplex.obj (TopCat.toSSet.obj X ⋙ ModuleCat.free ℤ) ≅
      ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj
        (ModuleCat.of ℤ ℤ)).obj X :=
  (AlgebraicTopology.alternatingFaceMapComplex (ModuleCat ℤ)).mapIso
    (CategoryTheory.Functor.isoWhiskerLeft (TopCat.toSSet.obj X) freeIntegerCoproductNatIso)

/-- Categorical homology of the free singular chains is genuine integral singular homology. -/
noncomputable def freeSingularHomologyIso (X : TopCat) (n : ℕ) :
    (AlgebraicTopology.AlternatingFaceMapComplex.obj
      (TopCat.toSSet.obj X ⋙ ModuleCat.free ℤ)).homology n ≅
        (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) n).obj
          (ModuleCat.of ℤ ℤ)).obj X) :=
  (HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) n).mapIso
    (freeSingularChainComplexIso X)

/-- The coefficient identification commutes with every actual continuous map. -/
theorem freeSingularChainComplexIso_natural {X Y : TopCat} (f : X ⟶ Y) :
    AlgebraicTopology.AlternatingFaceMapComplex.map
        (Functor.whiskerRight (TopCat.toSSet.map f) (ModuleCat.free ℤ)) ≫
      (freeSingularChainComplexIso Y).hom =
    (freeSingularChainComplexIso X).hom ≫
      (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj
        (ModuleCat.of ℤ ℤ)).map f) := by
  change (AlgebraicTopology.alternatingFaceMapComplex (ModuleCat ℤ)).map _ ≫
      (AlgebraicTopology.alternatingFaceMapComplex (ModuleCat ℤ)).map _ =
    (AlgebraicTopology.alternatingFaceMapComplex (ModuleCat ℤ)).map _ ≫
      (AlgebraicTopology.alternatingFaceMapComplex (ModuleCat ℤ)).map _
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1
  apply NatTrans.ext
  funext i
  exact freeIntegerCoproductNatIso.hom.naturality ((TopCat.toSSet.map f).app i)

/-- Naturality of the identification with integral singular homology in every degree. -/
theorem freeSingularHomologyIso_natural {X Y : TopCat} (f : X ⟶ Y) (n : ℕ) :
    (HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) n).map
      (AlgebraicTopology.AlternatingFaceMapComplex.map
        (Functor.whiskerRight (TopCat.toSSet.map f) (ModuleCat.free ℤ))) ≫
      (freeSingularHomologyIso Y n).hom =
    (freeSingularHomologyIso X n).hom ≫
      (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) n).obj
        (ModuleCat.of ℤ ℤ)).map f) := by
  change (HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) n).map _ ≫
      (HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) n).map _ =
    (HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) n).map _ ≫
      (HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) n).map _
  rw [← Functor.map_comp, ← Functor.map_comp, freeSingularChainComplexIso_natural]

end FiniteChains
