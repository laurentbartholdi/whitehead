module

/- Adapted from the local 2026-09-11 Lean audit; see PROVENANCE.json. -/

public import RequestProject.TopologicalSingular.SingularChainHomotopy
public import RequestProject.TopologicalSingular.RelativeSingularPrism

@[expose] public section

/-! # Chain maps and homotopies for actual topological pairs -/


set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.TopologicalSingular

open CategoryTheory Set

universe u
variable {X Y Z : Type u} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

theorem relativeComplex_d (A : Set X) (n : ℕ) :
    (relativeComplex A).d (n + 1) n = ModuleCat.ofHom (relativeBoundary A n) :=
  by
    unfold relativeComplex
    exact ChainComplex.of_d (fun i => ModuleCat.of ℤ (RelativeChain A i)) (fun i => ModuleCat.ofHom (relativeBoundary A i)) n

noncomputable def relativeChainMap (f : C(X, Y)) (A : Set X) (B : Set Y) (hf : MapsTo f A B) :
    relativeComplex A ⟶ relativeComplex B :=
  ChainComplex.ofHom (fun n => ModuleCat.ofHom (relativeMap f A B hf n)) (fun n => by
    rw [relativeComplex_d, relativeComplex_d]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro c
    exact (relativeMap_boundary f A B hf n c).symm)

theorem relativeChainMap_f (f : C(X, Y)) (A : Set X) (B : Set Y) (hf : MapsTo f A B) (n : ℕ) :
    (relativeChainMap f A B hf).f n = ModuleCat.ofHom (relativeMap f A B hf n) := rfl

theorem relativeChainMap_id (A : Set X) :
    relativeChainMap (ContinuousMap.id X) A A (fun _ h => h) = 𝟙 (relativeComplex A) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  exact relativeMap_id A n

theorem relativeChainMap_comp (f : C(X, Y)) (g : C(Y, Z))
    (A : Set X) (B : Set Y) (C : Set Z) (hf : MapsTo f A B) (hg : MapsTo g B C) :
    relativeChainMap (g.comp f) A C (hg.comp hf) =
      relativeChainMap f A B hf ≫ relativeChainMap g B C hg := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  exact relativeMap_comp f g A B C hf hg n

variable {f g : C(X, Y)} (H : ContinuousMap.Homotopy f g)
variable (A : Set X) (B : Set Y) (hH : ∀ t : unitInterval, ∀ x ∈ A, H (t, x) ∈ B)

noncomputable def relativePrismComponent (i j : ℕ) :
    (relativeComplex A).X i ⟶ (relativeComplex B).X j :=
  if h : j = i + 1 then h ▸ ModuleCat.ofHom (SingularPrism.relativePrism H A B hH i) else 0

theorem relativePrismComponent_succ (i : ℕ) :
    relativePrismComponent H A B hH i (i + 1) =
      ModuleCat.ofHom (SingularPrism.relativePrism H A B hH i) := by
  simp [relativePrismComponent]

noncomputable def relativeChainHomotopy :
    _root_.Homotopy
      (relativeChainMap g A B (SingularPrism.homotopy_one_mapsTo H A B hH))
      (relativeChainMap f A B (SingularPrism.homotopy_zero_mapsTo H A B hH)) where
  hom := relativePrismComponent H A B hH
  zero i j hij := by
    have hne : j ≠ i + 1 := by
      intro he
      apply hij
      subst j
      exact rfl
    simp only [relativePrismComponent, dif_neg hne]
  comm i := by
    cases i with
    | zero =>
      rw [_root_.Homotopy.dNext_zero_chainComplex, zero_add,
        _root_.Homotopy.prevD_chainComplex, relativePrismComponent_succ, relativeComplex_d,
        relativeChainMap_f, relativeChainMap_f]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro c
      change relativeMap g A B (SingularPrism.homotopy_one_mapsTo H A B hH) 0 c =
        relativeBoundary B 0 (SingularPrism.relativePrism H A B hH 0 c) +
        relativeMap f A B (SingularPrism.homotopy_zero_mapsTo H A B hH) 0 c
      rw [SingularPrism.relativePrism_identity_zero]
      abel
    | succ i =>
      rw [_root_.Homotopy.dNext_succ_chainComplex, _root_.Homotopy.prevD_chainComplex,
        relativePrismComponent_succ, relativePrismComponent_succ, relativeComplex_d,
        relativeComplex_d, relativeChainMap_f, relativeChainMap_f]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro c
      change relativeMap g A B (SingularPrism.homotopy_one_mapsTo H A B hH) (i + 1) c =
        SingularPrism.relativePrism H A B hH i (relativeBoundary A i c) +
        relativeBoundary B (i + 1) (SingularPrism.relativePrism H A B hH (i + 1) c) +
        relativeMap f A B (SingularPrism.homotopy_zero_mapsTo H A B hH) (i + 1) c
      rw [add_comm (SingularPrism.relativePrism H A B hH i (relativeBoundary A i c)),
        SingularPrism.relativePrism_identity_succ]
      abel

theorem relativeHomologyMap_eq_of_homotopy (n : ℕ) :
    HomologicalComplex.homologyMap
        (relativeChainMap f A B (SingularPrism.homotopy_zero_mapsTo H A B hH)) n =
      HomologicalComplex.homologyMap
        (relativeChainMap g A B (SingularPrism.homotopy_one_mapsTo H A B hH)) n :=
  ((relativeChainHomotopy H A B hH).homologyMap_eq n).symm

end FiniteChains.TopologicalSingular
