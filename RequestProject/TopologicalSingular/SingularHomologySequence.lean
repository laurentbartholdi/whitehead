module

/- Adapted from the local 2026-09-11 Lean audit; see PROVENANCE.json. -/

public import RequestProject.TopologicalSingular.RelativeChainHomotopy
public import RequestProject.TopologicalSingular.ContractibleSingularChains
public import Mathlib.Algebra.Homology.HomologySequence
public import Mathlib.Algebra.Category.ModuleCat.EpiMono

@[expose] public section

/-! # The long exact sequence of an actual topological pair

The inclusion of the subspace chains and the quotient map form a short
exact sequence of complexes. Mathlib's homology sequence supplies its
connecting maps and all three exactness statements. For contractible
ambient spaces the positive-degree dimension-shift is an isomorphism.
-/


set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.TopologicalSingular

open CategoryTheory CategoryTheory.Limits

universe u
variable {X : Type u} [TopologicalSpace X]

noncomputable def projectionChainMap (A : Set X) : complex X ⟶ relativeComplex A :=
  ChainComplex.ofHom
    (fun n => ModuleCat.ofHom (relativeProjection A n)) (fun n => by
    rw [complex_d, relativeComplex_d]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    exact relativeBoundary_projection A n)

theorem projectionChainMap_f (A : Set X) (n : ℕ) :
    (projectionChainMap A).f n = ModuleCat.ofHom (relativeProjection A n) := rfl

theorem inclusion_projection_zero (A : Set X) :
    chainMap (inclusion A) ≫ projectionChainMap A = 0 := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  change relativeProjection A n (map (inclusion A) n c) = 0
  exact (relativeProjection_eq_zero_iff A n _).mpr ⟨c, rfl⟩

noncomputable def pairShortComplex (A : Set X) : ShortComplex (ChainComplex (ModuleCat.{u} ℤ) ℕ) :=
  ShortComplex.mk (chainMap (inclusion A)) (projectionChainMap A) (inclusion_projection_zero A)

theorem pairShortComplex_shortExact (A : Set X) : (pairShortComplex A).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · apply (ShortComplex.moduleCat_exact_iff_range_eq_ker _).mpr
    exact (ker_relativeProjection A n).symm
  · apply (ModuleCat.mono_iff_injective _).mpr
    exact map_inclusion_injective A n
  · apply (ModuleCat.epi_iff_surjective _).mpr
    exact relativeProjection_surjective A n

noncomputable def connectingMap (A : Set X) (n : ℕ) :
    (relativeComplex A).homology (n + 1) ⟶ (complex A).homology n :=
  (pairShortComplex_shortExact A).δ (n + 1) n rfl

theorem connectingMap_comp_inclusion (A : Set X) (n : ℕ) :
    connectingMap A n ≫ HomologicalComplex.homologyMap (chainMap (inclusion A)) n = 0 :=
  (pairShortComplex_shortExact A).δ_comp (n + 1) n rfl

theorem projection_comp_connectingMap (A : Set X) (n : ℕ) :
    HomologicalComplex.homologyMap (projectionChainMap A) (n + 1) ≫ connectingMap A n = 0 :=
  (pairShortComplex_shortExact A).comp_δ (n + 1) n rfl

theorem inclusion_projection_homology_zero (A : Set X) (n : ℕ) :
    HomologicalComplex.homologyMap (chainMap (inclusion A)) n ≫
      HomologicalComplex.homologyMap (projectionChainMap A) n = 0 := by
  rw [← HomologicalComplex.homologyMap_comp, inclusion_projection_zero,
    HomologicalComplex.homologyMap_zero]

theorem homologySequence_exact_subspace (A : Set X) (n : ℕ) :
    (ShortComplex.mk _ _ (connectingMap_comp_inclusion A n)).Exact :=
  (pairShortComplex_shortExact A).homology_exact₁ (n + 1) n rfl

theorem homologySequence_exact_space (A : Set X) (n : ℕ) :
    (ShortComplex.mk _ _ (inclusion_projection_homology_zero A n)).Exact :=
  (pairShortComplex_shortExact A).homology_exact₂ n

theorem homologySequence_exact_relative (A : Set X) (n : ℕ) :
    (ShortComplex.mk _ _ (projection_comp_connectingMap A n)).Exact :=
  (pairShortComplex_shortExact A).homology_exact₃ (n + 1) n rfl

theorem contractible_complex_exactAt_allUniverses [ContractibleSpace X] (n : ℕ) :
    (complex X).ExactAt (n + 1) := by
  rw [HomologicalComplex.exactAt_iff' (K := complex X) (i := n + 2) (j := n + 1) (k := n)
    (ChainComplex.prev ℕ (n + 1)) (ChainComplex.next_nat_succ n)]
  apply (ShortComplex.moduleCat_exact_iff_range_eq_ker _).mpr
  change LinearMap.range (((complex X).d (n + 2) (n + 1)).hom) =
    LinearMap.ker (((complex X).d (n + 1) n).hom)
  rw [complex_d, complex_d]
  exact (contractible_ker_boundary_eq_range n).symm

theorem contractible_homology_isZero [ContractibleSpace X] (n : ℕ) :
    IsZero ((complex X).homology (n + 1)) :=
  (contractible_complex_exactAt_allUniverses n).isZero_homology

noncomputable def relativeHomologyIsoOfContractible [ContractibleSpace X] (A : Set X) (n : ℕ) :
    (relativeComplex A).homology (n + 2) ≅ (complex A).homology (n + 1) :=
  (pairShortComplex_shortExact A).δIso (n + 2) (n + 1) rfl
    (contractible_homology_isZero (n + 1)) (contractible_homology_isZero n)

end FiniteChains.TopologicalSingular
