import RequestProject.TopologicalSingular.NormalizedTwoCycles
import RequestProject.TopologicalSingular.CycleClassModule

namespace FiniteChains.TopologicalSingular
open CategoryTheory AlgebraicTopology
open scoped Topology
variable {X : Type} [TopologicalSpace X]

noncomputable def pi2CycleClassAddHom (x : X) :
    Additive (HomotopyGroup (Fin 2) X x) →+ (complex X).homology 2 := {
    toFun := fun a => pi2CycleClass x a.toMul
    map_zero' := pi2CycleClass_one x
    map_add' := fun a b => pi2CycleClass_mul x a.toMul b.toMul }

noncomputable def pi2CycleClassLinear (x : X) :
    Additive (HomotopyGroup (Fin 2) X x) →ₗ[ℤ] (complex X).homology 2 where
  toFun := pi2CycleClassAddHom x
  map_add' := (pi2CycleClassAddHom x).map_add
  map_smul' r a := by
    exact (map_zsmul (pi2CycleClassAddHom x) r a).trans
      (int_smul_eq_zsmul (inferInstance : Module ℤ ((complex X).homology 2)) r _).symm

variable [SimplyConnectedSpace X]

/-- A finite integral chain is sent to the sum of actual based squares
representing its normalized triangles. -/
noncomputable def normalizedPi2Chain (x : X) :
    Chain X 2 →ₗ[ℤ] Additive (HomotopyGroup (Fin 2) X x) :=
  Finsupp.linearCombination ℤ (fun tau => Additive.ofMul
    (Quotient.mk _ (basedTriangleSquare (normalizedTriangle x tau) (normalizedTriangle_face x tau))))

theorem normalizedPi2Chain_class_linear (x : X) :
    (pi2CycleClassLinear x).comp (normalizedPi2Chain x) =
      (singularCycleClassLinear 1).comp (normalizedCycleMap x) := by
  apply Finsupp.lhom_ext
  intro tau r
  simp only [LinearMap.comp_apply, normalizedPi2Chain, normalizedCycleMap,
    Finsupp.linearCombination_single]
  rw [(pi2CycleClassLinear x).map_smul, (singularCycleClassLinear 1).map_smul]
  apply congrArg (fun b : (complex X).homology 2 =>
    (inferInstance : Module ℤ ((complex X).homology 2)).smul r b)
  change pi2CycleClass x
    (Quotient.mk _ (basedTriangleSquare (normalizedTriangle x tau) (normalizedTriangle_face x tau))) =
      singularCycleClass 1 (basedTriangleCycle (normalizedTriangle x tau) x)
        (basedTriangleCycle_boundary _ (normalizedTriangle_face x tau))
  simp only [pi2CycleClass_mk, squareCycle_basedTriangleSquare]

theorem normalizedPi2Chain_class (x : X) (c : Chain X 2) (hc : boundary 1 c = 0) :
    pi2CycleClass x (normalizedPi2Chain x c).toMul = singularCycleClass 1 c hc := by
  have he := DFunLike.congr_fun (normalizedPi2Chain_class_linear x) c
  change pi2CycleClass x (normalizedPi2Chain x c).toMul =
    singularCycleClass 1 (normalizedCycleMap x c).val (normalizedCycleMap x c).property at he
  exact he.trans (normalizedCycleMap_class x c hc)

theorem pi2CycleClass_surjective (x : X) : Function.Surjective (pi2CycleClass x) := by
  intro q
  obtain ⟨c, hc, hq⟩ := singularCycleClass_representative 1 q
  exact ⟨(normalizedPi2Chain x c).toMul, (normalizedPi2Chain_class x c hc).trans hq⟩

/-- Every integral singular 2-cycle in a simply connected space is homologous
to the fundamental cycle of an actual based square. -/
theorem singularTwoCycle_square_representative (x : X) (c : Chain X 2) (hc : boundary 1 c = 0) :
    ∃ p : GenLoop (Fin 2) X x, squareCycle p - c ∈ LinearMap.range (boundary 2) := by
  obtain ⟨p, hp⟩ := Quotient.exists_rep ((normalizedPi2Chain x c).toMul)
  have he := normalizedPi2Chain_class x c hc
  rw [← hp, pi2CycleClass_mk] at he
  exact ⟨p, (singularCycleClass_eq_iff 1 _ _ _ _).mp he⟩

/-- Surjectivity of the genuine degree-two Hurewicz homomorphism, with the
actual Mathlib integral singular homology as codomain. -/
theorem singularHurewicz2_surjective (x : X) : Function.Surjective (singularHurewicz2 x) := by
  intro q
  obtain ⟨h, hh⟩ := (ModuleCat.epi_iff_surjective (homologyMathlibIso (TopCat.of X) 2).hom).mp
    inferInstance q
  obtain ⟨a, ha⟩ := pi2CycleClass_surjective x h
  refine ⟨a, ?_⟩
  change (homologyMathlibIso (TopCat.of X) 2).hom (pi2CycleClass x a) = q
  rw [ha, hh]

theorem singularHurewicz2Hom_surjective (x : X) : Function.Surjective (singularHurewicz2Hom x) := by
  intro q
  obtain ⟨a, ha⟩ := singularHurewicz2_surjective x q.toAdd
  exact ⟨a, ha⟩

end FiniteChains.TopologicalSingular
