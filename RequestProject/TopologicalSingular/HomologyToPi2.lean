import RequestProject.TopologicalSingular.NormalizedPi2Boundaries

namespace FiniteChains.TopologicalSingular
variable {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]

/-- The normalized-triangle sum on any representative of a genuine homology
class. The following theorem proves independence of that representative. -/
noncomputable def singularH2ToPi2 (x : X) (q : (complex X).homology 2) :
    Additive (HomotopyGroup (Fin 2) X x) :=
  normalizedPi2Chain x (singularCycleClass_representative 1 q).choose

theorem singularH2ToPi2_class (x : X) (c : Chain X 2) (hc : boundary 1 c = 0) :
    singularH2ToPi2 x (singularCycleClass 1 c hc) = normalizedPi2Chain x c := by
  unfold singularH2ToPi2
  apply normalizedPi2Chain_eq_of_homologous
  exact (singularCycleClass_eq_iff 1 _ c
    (singularCycleClass_representative 1 (singularCycleClass 1 c hc)).choose_spec.choose hc).mp
    (singularCycleClass_representative 1 (singularCycleClass 1 c hc)).choose_spec.choose_spec

noncomputable def singularH2ToPi2AddHom (x : X) :
    (complex X).homology 2 →+ Additive (HomotopyGroup (Fin 2) X x) where
  toFun := singularH2ToPi2 x
  map_zero' := by
    rw [← singularCycleClass_zero 1, singularH2ToPi2_class, map_zero]
  map_add' q r := by
    obtain ⟨c, hc, rfl⟩ := singularCycleClass_representative 1 q
    obtain ⟨d, hd, rfl⟩ := singularCycleClass_representative 1 r
    rw [← singularCycleClass_add 1 c d hc hd]
    simp only [singularH2ToPi2_class, map_add]

noncomputable def singularH2ToPi2Linear (x : X) :
    (complex X).homology 2 →ₗ[ℤ] Additive (HomotopyGroup (Fin 2) X x) where
  toFun := singularH2ToPi2AddHom x
  map_add' := (singularH2ToPi2AddHom x).map_add
  map_smul' r q := by
    exact (congrArg (singularH2ToPi2AddHom x)
      (int_smul_eq_zsmul (inferInstance : Module ℤ ((complex X).homology 2)) r q)).trans
      (map_zsmul (singularH2ToPi2AddHom x) r q)

/-- Applying Hurewicz to the constructed pi2 class recovers the original
homology class. The other inverse law remains a separate geometric obligation. -/
theorem pi2CycleClass_singularH2ToPi2 (x : X) (q : (complex X).homology 2) :
    pi2CycleClass x (singularH2ToPi2 x q).toMul = q := by
  obtain ⟨c, hc, rfl⟩ := singularCycleClass_representative 1 q
  rw [singularH2ToPi2_class]
  exact normalizedPi2Chain_class x c hc

theorem singularH2ToPi2_injective (x : X) : Function.Injective (singularH2ToPi2 x) := by
  intro q r h
  have he := congrArg (fun v : Additive (HomotopyGroup (Fin 2) X x) =>
    pi2CycleClass x v.toMul) h
  simpa only [pi2CycleClass_singularH2ToPi2] using he

theorem pi2CycleClassLinear_comp_singularH2ToPi2Linear (x : X) :
    (pi2CycleClassLinear x).comp (singularH2ToPi2Linear x) = LinearMap.id := by
  ext q
  exact pi2CycleClass_singularH2ToPi2 x q

end FiniteChains.TopologicalSingular
