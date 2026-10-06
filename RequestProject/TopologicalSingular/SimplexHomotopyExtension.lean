import RequestProject.TopologicalSingular.SimplexPrismRetraction

namespace FiniteChains.TopologicalSingular
open scoped unitInterval Topology
universe u
variable {X : Type u} [TopologicalSpace X] {n : ℕ}

noncomputable def simplexPrismBoundaryValue (f : C(Domain n, X))
    (H : C(I × simplexBoundary n, X)) (w : simplexPrismSide n) : X := by
  classical
  exact if h : w.val.2 ∈ simplexBoundary n then H (w.val.1, ⟨w.val.2, h⟩) else f w.val.2

theorem simplexPrismBoundaryValue_bottom (f : C(Domain n, X))
    (H : C(I × simplexBoundary n, X)) (hH : ∀ z : simplexBoundary n, H (0, z) = f z)
    (w : simplexPrismSide n) (hw : w.val.1 = 0) : simplexPrismBoundaryValue f H w = f w.val.2 := by
  classical
  unfold simplexPrismBoundaryValue
  split_ifs with h
  · rw [hw]
    exact hH ⟨w.val.2, h⟩
  · rfl

theorem simplexPrismBoundaryValue_side (f : C(Domain n, X))
    (H : C(I × simplexBoundary n, X)) (w : simplexPrismSide n)
    (hw : w.val.2 ∈ simplexBoundary n) :
    simplexPrismBoundaryValue f H w = H (w.val.1, ⟨w.val.2, hw⟩) := by
  classical
  simp only [simplexPrismBoundaryValue, dif_pos hw]

theorem simplexPrismBoundaryValue_continuous (f : C(Domain n, X))
    (H : C(I × simplexBoundary n, X)) (hH : ∀ z : simplexBoundary n, H (0, z) = f z) :
    Continuous (simplexPrismBoundaryValue f H) := by
  let S : Set (simplexPrismSide n) := {w | w.val.1 = 0}
  let T : Set (simplexPrismSide n) := {w | w.val.2 ∈ simplexBoundary n}
  have hS : IsClosed S := isClosed_eq continuous_subtype_val.fst continuous_const
  have hT : IsClosed T := (simplexBoundary_isClosed n).preimage continuous_subtype_val.snd
  have hu : S ∪ T = Set.univ := by
    ext w
    simp only [Set.mem_union, Set.mem_univ, iff_true]
    exact w.property
  have hcS : ContinuousOn (simplexPrismBoundaryValue f H) S := by
    apply (f.continuous.comp continuous_subtype_val.snd).continuousOn.congr
    intro w hw
    exact simplexPrismBoundaryValue_bottom f H hH w hw
  have hcT : ContinuousOn (simplexPrismBoundaryValue f H) T := by
    rw [continuousOn_iff_continuous_restrict]
    have hc : Continuous (fun w : T => H (w.val.val.1, ⟨w.val.val.2, w.property⟩)) := by
      apply H.continuous.comp
      exact continuous_subtype_val.subtype_val.fst.prodMk
        (continuous_subtype_val.subtype_val.snd.subtype_mk _)
    convert hc using 1
    funext w
    exact simplexPrismBoundaryValue_side f H w.val w.property
  rw [← continuousOn_univ, ← hu]
  exact hcS.union_of_isClosed hcT hS hT

/-- Glue the prescribed initial map and the prescribed boundary homotopy. -/
noncomputable def simplexPrismBoundaryMap (f : C(Domain n, X))
    (H : C(I × simplexBoundary n, X)) (hH : ∀ z : simplexBoundary n, H (0, z) = f z) :
    C(simplexPrismSide n, X) :=
  ⟨simplexPrismBoundaryValue f H, simplexPrismBoundaryValue_continuous f H hH⟩

/-- Extension over the entire simplex prism. -/
noncomputable def simplexHomotopyExtension (f : C(Domain n, X))
    (H : C(I × simplexBoundary n, X)) (hH : ∀ z : simplexBoundary n, H (0, z) = f z) :
    C(I × Domain n, X) :=
  (simplexPrismBoundaryMap f H hH).comp (simplexPrismRetraction n)

theorem simplexHomotopyExtension_zero (f : C(Domain n, X))
    (H : C(I × simplexBoundary n, X)) (hH : ∀ z : simplexBoundary n, H (0, z) = f z)
    (z : Domain n) : simplexHomotopyExtension f H hH (0, z) = f z := by
  have he := simplexPrismRetraction_fixes (0, z) (Or.inl rfl)
  change simplexPrismBoundaryValue f H (simplexPrismRetraction n (0, z)) = _
  rw [simplexPrismBoundaryValue_bottom f H hH _ (congrArg Prod.fst he)]
  rw [congrArg Prod.snd he]

theorem simplexHomotopyExtension_boundary (f : C(Domain n, X))
    (H : C(I × simplexBoundary n, X)) (hH : ∀ z : simplexBoundary n, H (0, z) = f z)
    (t : I) (z : simplexBoundary n) : simplexHomotopyExtension f H hH (t, z.val) = H (t, z) := by
  have he := simplexPrismRetraction_fixes (t, z.val) (Or.inr z.property)
  have hz : (simplexPrismRetraction n (t, z.val)).val.2 ∈ simplexBoundary n := by
    rw [congrArg Prod.snd he]
    exact z.property
  change simplexPrismBoundaryValue f H (simplexPrismRetraction n (t, z.val)) = _
  rw [simplexPrismBoundaryValue_side f H _ hz]
  apply congrArg H
  apply Prod.ext
  · exact congrArg (fun w : I × Domain n => w.1) he
  · exact Subtype.ext (congrArg (fun w : I × Domain n => w.2) he)

/-- The standard topological simplex has the homotopy extension property
relative to its entire boundary, with no restriction on the target space. -/
theorem simplex_homotopy_extension (f : C(Domain n, X))
    (H : C(I × simplexBoundary n, X)) (hH : ∀ z : simplexBoundary n, H (0, z) = f z) :
    ∃ g : C(Domain n, X), ∃ F : f.Homotopy g,
      ∀ (t : I) (z : simplexBoundary n), F (t, z.val) = H (t, z) := by
  let E := simplexHomotopyExtension f H hH
  let g : C(Domain n, X) := ⟨fun z => E (1, z), E.continuous.comp (continuous_const.prodMk continuous_id)⟩
  refine ⟨g, {
    toContinuousMap := E
    map_zero_left := simplexHomotopyExtension_zero f H hH
    map_one_left := fun _ => rfl }, ?_⟩
  exact simplexHomotopyExtension_boundary f H hH

end FiniteChains.TopologicalSingular
