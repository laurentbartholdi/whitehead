import Mathlib.Algebra.Category.ModuleCat.Adjunctions
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.LinearAlgebra.DFinsupp
import Mathlib.Algebra.Category.ModuleCat.Colimits

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains
open CategoryTheory CategoryTheory.Limits

/-- The actual free integral module agrees with the categorical coproduct of copies of ℤ. -/
noncomputable def freeIntegerCoproductIso (ι : Type) :
    (ModuleCat.free ℤ).obj ι ≅
      (sigmaConst.obj (ModuleCat.of ℤ ℤ)).obj ι :=
  by
  classical
  exact (finsuppLequivDFinsupp ℤ).toModuleIso ≪≫
    (ModuleCat.coprodIsoDirectSum (fun _ : ι => ModuleCat.of ℤ ℤ)).symm

/-- Each actual coproduct injection corresponds to the actual finitely supported generator. -/
theorem freeIntegerCoproductIso_inv_ι (ι : Type) (i : ι) (n : ℤ) :
    (freeIntegerCoproductIso ι).inv (Sigma.ι (fun _ : ι => ModuleCat.of ℤ ℤ) i n) =
      Finsupp.single i n := by
  classical
  change (finsuppLequivDFinsupp ℤ).symm
    ((ModuleCat.coprodIsoDirectSum (fun _ : ι => ModuleCat.of ℤ ℤ)).hom
      (Sigma.ι (fun _ : ι => ModuleCat.of ℤ ℤ) i n)) = _
  have h := congrArg (fun k : ModuleCat.of ℤ ℤ ⟶
      ModuleCat.of ℤ (Π₀ _ : ι, ℤ) => k n)
    (ModuleCat.ι_coprodIsoDirectSum_hom (fun _ : ι => ModuleCat.of ℤ ℤ) i)
  change (ModuleCat.coprodIsoDirectSum (fun _ : ι => ModuleCat.of ℤ ℤ)).hom
    (Sigma.ι (fun _ : ι => ModuleCat.of ℤ ℤ) i n) =
      DirectSum.lof ℤ ι (fun _ : ι => ℤ) i n at h
  rw [h]
  exact DFinsupp.toFinsupp_single i n

/-- The inverse coefficient comparison is natural under arbitrary maps of index sets. -/
theorem freeIntegerCoproductIso_inv_natural {ι κ : Type} (f : ι → κ) :
    (sigmaConst.obj (ModuleCat.of ℤ ℤ)).map (TypeCat.ofHom f) ≫ (freeIntegerCoproductIso κ).inv =
      (freeIntegerCoproductIso ι).inv ≫ (ModuleCat.free ℤ).map (TypeCat.ofHom f) := by
  apply Sigma.hom_ext
  intro i
  apply ModuleCat.hom_ext
  ext
  simp [ModuleCat.free, sigmaConst]
  change (freeIntegerCoproductIso κ).inv
      (Sigma.ι (fun _ : κ => ModuleCat.of ℤ ℤ) (f i) 1) =
    Finsupp.mapDomain f ((freeIntegerCoproductIso ι).inv
      (Sigma.ι (fun _ : ι => ModuleCat.of ℤ ℤ) i 1))
  rw [freeIntegerCoproductIso_inv_ι, freeIntegerCoproductIso_inv_ι,
    Finsupp.mapDomain_single]

/-- The coefficient comparison is a genuine natural isomorphism of functors. -/
noncomputable def freeIntegerCoproductNatIso :
    ModuleCat.free ℤ ≅ sigmaConst.obj (ModuleCat.of ℤ ℤ) :=
  NatIso.ofComponents freeIntegerCoproductIso (by
    intro ι κ f
    apply (cancel_mono (freeIntegerCoproductIso κ).inv).mp
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    rw [show f = TypeCat.ofHom f.hom from rfl, freeIntegerCoproductIso_inv_natural, ← Category.assoc,
      Iso.hom_inv_id, Category.id_comp])

end FiniteChains
