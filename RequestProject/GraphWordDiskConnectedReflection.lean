module

public import RequestProject.ClassicalGraphBoundaryWords
public import RequestProject.ComponentComplex
public import Mathlib.Topology.Connected.TotallyDisconnected

@[expose] public section

/-! Attaching word disks cannot connect distinct graph components.
Thus connectedness of an actual word-disk model supplies connectedness
of its labelled combinatorial graph. No finiteness is required. Unverified. -/

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.ClassicalGraphModel
open RelativeAttachment
open scoped Classical unitInterval Topology
variable {V J M : Type} [TopologicalSpace V] [DiscreteTopology V]
  (r : BoundaryFamily J (Fin 1 → ℝ) → V)

def graphComponentSetoid : Setoid V where
  r := Comb.Reach (graphCx r)
  iseqv := {
    refl := Comb.reach_self (graphCx r)
    symm := by
      rintro a b ⟨l, hl⟩
      exact ⟨Comb.revPath l, Comb.isPath_revPath hl⟩
    trans := by
      rintro a b c ⟨l, hl⟩ ⟨m, hm⟩
      exact ⟨l ++ m, hl.append hm⟩ }

abbrev GraphComponents := Quotient (graphComponentSetoid r)
local instance : TopologicalSpace (GraphComponents r) := ⊥
local instance : DiscreteTopology (GraphComponents r) := ⟨rfl⟩

def graphComponentMap : C(DiskAttachment r, GraphComponents r) :=
  desc r (boundaryFamilyInclusion J (Fin 1 → ℝ))
    ⟨Quotient.mk _, continuous_of_discreteTopology⟩
    ⟨fun d => Quotient.mk _ (graphSrc r d.1),
      continuous_sigma (fun j =>
        (continuous_const : Continuous (fun _ : ClosedUnitBall (Fin 1 → ℝ) =>
          Quotient.mk (graphComponentSetoid r) (graphSrc r j))))⟩
    (fun a => by
      rcases a with ⟨j, a⟩
      rcases graphBoundary_cases a with rfl | rfl
      · rfl
      · apply Eq.symm
        exact Quotient.sound (show Comb.Reach (graphCx r) (graphSrc r j) (graphTgt r j)
          from ⟨[(j, true)], rfl, rfl⟩))

theorem graphComponentMap_path {x y : V}
    (p : Path (old r (boundaryFamilyInclusion J _) x)
      (old r (boundaryFamilyInclusion J _) y)) (t : I) :
    graphComponentMap r (p t) = Quotient.mk (graphComponentSetoid r) x := by
  have h := TotallyDisconnectedSpace.eq_of_continuous
    (fun t => graphComponentMap r (p t)) ((graphComponentMap r).continuous.comp p.continuous) t 0
  simpa [p.source, graphComponentMap] using h

theorem graphComponentMap_boundaryWord (W : BoundaryWords r)
    (a : UnitBoundary (Fin 2 → ℝ)) :
    graphComponentMap r (W.boundaryMap a) =
      Quotient.mk (graphComponentSetoid r) (W.vertex (squareSideMap (0, false) 0)) := by
  have hedge (s : SquareSide) :
      Quotient.mk (graphComponentSetoid r) (W.vertex (squareSideMap s 0)) =
        Quotient.mk (graphComponentSetoid r) (W.vertex (squareSideMap s 1)) := by
    exact Quotient.sound ⟨W.word s, W.isPath s⟩
  have hcorner (s : SquareSide) :
      Quotient.mk (graphComponentSetoid r) (W.vertex (squareSideMap s 0)) =
        Quotient.mk (graphComponentSetoid r) (W.vertex (squareSideMap (0, false) 0)) := by
    rcases s with ⟨i, b⟩
    fin_cases i <;> cases b
    · rfl
    · have h₁ : squareSideMap (0, true) 0 = squareSideMap (1, false) 1 := by
        apply Subtype.ext
        funext i
        fin_cases i <;> rfl
      have h₀ : squareSideMap (1, false) 0 = squareSideMap (0, false) 0 := by
        apply Subtype.ext
        funext i
        fin_cases i <;> rfl
      exact (congrArg (fun z => Quotient.mk (graphComponentSetoid r) (W.vertex z)) h₁).trans
        ((hedge (1, false)).symm.trans
          (congrArg (fun z => Quotient.mk (graphComponentSetoid r) (W.vertex z)) h₀))
    · have h₀ : squareSideMap (1, false) 0 = squareSideMap (0, false) 0 := by
        apply Subtype.ext
        funext i
        fin_cases i <;> rfl
      exact congrArg (fun z => Quotient.mk (graphComponentSetoid r) (W.vertex z)) h₀
    · have h₀ : squareSideMap (1, true) 0 = squareSideMap (0, false) 1 := by
        apply Subtype.ext
        funext i
        fin_cases i <;> rfl
      exact (congrArg (fun z => Quotient.mk (graphComponentSetoid r) (W.vertex z)) h₀).trans
        (hedge (0, false)).symm
  obtain ⟨⟨s, t⟩, hs⟩ := squareSideQuotient_surjective (unitBoundarySquareHomeomorph a)
  change squareSideMap s t = unitBoundarySquareHomeomorph a at hs
  change graphComponentMap r (W.squareMap (unitBoundarySquareHomeomorph a)) = _
  rw [← hs, W.squareMap_side, graphComponentMap_path]
  exact hcorner s

variable (W : M → BoundaryWords r)

def boundaryWordsAttaching : C(BoundaryFamily M (Fin 2 → ℝ), DiskAttachment r) :=
  ⟨fun a => (W a.1).boundaryMap a.2, continuous_sigma (fun m => (W m).boundaryMap.continuous)⟩

def wordDiskComponentMap : C(DiskAttachment (boundaryWordsAttaching r W), GraphComponents r) :=
  desc (boundaryWordsAttaching r W) (boundaryFamilyInclusion M (Fin 2 → ℝ))
    (graphComponentMap r)
    ⟨fun d => Quotient.mk _ ((W d.1).vertex (squareSideMap (0, false) 0)),
      continuous_sigma (fun j =>
        (continuous_const : Continuous (fun _ : ClosedUnitBall (Fin 2 → ℝ) =>
          Quotient.mk (graphComponentSetoid r) ((W j).vertex (squareSideMap (0, false) 0)))))⟩
    (fun a => graphComponentMap_boundaryWord r (W a.1) a.2)

theorem graphCx_isConnected_of_wordDisks
    [PreconnectedSpace (DiskAttachment (boundaryWordsAttaching r W))] :
    Comb.IsConnected (graphCx r) := by
  intro a b
  apply Quotient.exact (s := graphComponentSetoid r)
  exact TotallyDisconnectedSpace.eq_of_continuous (wordDiskComponentMap r W)
    (wordDiskComponentMap r W).continuous
    (old _ _ (old r _ a)) (old _ _ (old r _ b))

omit [DiscreteTopology V] in
theorem graph_vertices_nonempty_of_wordDisks
    [Nonempty (DiskAttachment (boundaryWordsAttaching r W))] : Nonempty V := by
  obtain ⟨x⟩ := (inferInstance : Nonempty (DiskAttachment (boundaryWordsAttaching r W)))
  obtain ⟨z, rfl⟩ := quotientMap_surjective (boundaryWordsAttaching r W)
    (boundaryFamilyInclusion M (Fin 2 → ℝ)) x
  cases z with
  | inr d => exact ⟨(W d.1).vertex (squareSideMap (0, false) 0)⟩
  | inl x =>
    obtain ⟨z, rfl⟩ := quotientMap_surjective r (boundaryFamilyInclusion J (Fin 1 → ℝ)) x
    cases z with
    | inl v => exact ⟨v⟩
    | inr d => exact ⟨graphSrc r d.1⟩

end FiniteChains.ClassicalGraphModel
