module

public import Mathlib.Topology.CWComplex.Classical.Subcomplex
public import Mathlib.Topology.Covering.Basic
public import Mathlib.Topology.Homotopy.HomotopyGroup
public import Mathlib.AlgebraicTopology.SingularHomology.Basic
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Colimits

@[expose] public section

/-! Definitions used in the statement of Theorem A. They are identical to those in
`Challenge.lean`; the theorem itself is stated and proved in `Solution.lean`. -/

noncomputable section

namespace Whitehead

open Topology CategoryTheory

/-- A connected Hausdorff CW complex with no cells above dimension two. -/
structure TwoComplex where
  space : Type
  topology : TopologicalSpace space
  hausdorff : T2Space space
  cw : CWComplex (Set.univ : Set space)
  connected : ConnectedSpace space
  dimension : ∀ n, 2 < n → IsEmpty (RelCWComplex.cell (Set.univ : Set space) n)

instance : CoeSort TwoComplex Type := ⟨TwoComplex.space⟩
attribute [instance] TwoComplex.topology TwoComplex.hausdorff TwoComplex.cw
  TwoComplex.connected

/-- Postcomposition of a based square map, preserving its boundary condition. -/
def mapSquare {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) {x : X} (p : GenLoop (Fin 2) X x) : GenLoop (Fin 2) Y (f x) :=
  ⟨f.comp p.val, fun y hy => congrArg f (GenLoop.boundary p y hy)⟩

/-- The induced map on the topological second homotopy groups is zero at every base point. -/
def KillsPi2 {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) : Prop :=
  ∀ (x : X) (p : GenLoop (Fin 2) X x),
    GenLoop.Homotopic (mapSquare f p) GenLoop.const

/-- Vanishing of all positive-degree integral singular homology groups. Connectedness is
specified separately wherever acyclicity is used. -/
def Acyclic (X : Type) [TopologicalSpace X] : Prop :=
  ∀ n : ℕ, 0 < n → Limits.IsZero
    (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) n).obj
      (ModuleCat.of ℤ ℤ)).obj (TopCat.of X))

/-- Regularity means that deck transformations act transitively on every fiber. -/
def Regular {D X : Type} [TopologicalSpace D] [TopologicalSpace X] (p : C(D, X)) : Prop :=
  ∀ d e : D, p d = p e → ∃ h : D ≃ₜ D, (∀ z, p (h z) = p z) ∧ h d = e

def HasAcyclicRegularCover (K : TwoComplex) : Prop :=
  ∃ (D : Type) (t : TopologicalSpace D),
    letI := t
    ∃ p : C(D, K), IsCoveringMap p ∧ Function.Surjective p ∧
      ConnectedSpace D ∧ Regular p ∧ Acyclic D

def FiniteCells (K : TwoComplex) : Prop :=
  Finite (Σ n, RelCWComplex.cell (Set.univ : Set K) n)

/-- Identify the given CW complex with the initial subcomplex, preserving its open cells. -/
def InitialIdentification {K L : TwoComplex}
    (C : CWComplex.Subcomplex (Set.univ : Set L)) (e : K ≃ₜ (C : Set L)) : Prop :=
  ∀ n, ∃ b : RelCWComplex.cell (Set.univ : Set K) n ≃
      {j : RelCWComplex.cell (Set.univ : Set L) n // j ∈ C.I n},
    ∀ i, (fun x : K => (e x).val) '' CWComplex.openCell (C := (Set.univ : Set K)) n i =
      CWComplex.openCell (C := (Set.univ : Set L)) n (b i).val

/-- A strict chain of subcomplexes of a common connected two-complex. Finite chains additionally
require the ambient CW complex, hence every subcomplex in the chain, to have finitely many cells. -/
def HasChain (K : TwoComplex) (n : ℕ) (finite : Bool) : Prop :=
  ∃ (L : TwoComplex) (C : Fin (n + 1) → CWComplex.Subcomplex (Set.univ : Set L))
    (e : K ≃ₜ (C 0 : Set L)),
    InitialIdentification (C 0) e ∧
    (finite = true → FiniteCells L) ∧
    (∀ i, ConnectedSpace (C i : Set L)) ∧
    ∀ i : Fin n, ∃ h : (C i.castSucc : Set L) ⊆ (C i.succ : Set L),
      (C i.castSucc : Set L) ≠ (C i.succ : Set L) ∧
      KillsPi2 ⟨Set.inclusion h, continuous_inclusion h⟩

end Whitehead
