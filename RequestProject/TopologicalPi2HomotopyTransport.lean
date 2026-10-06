module

public import RequestProject.TopologicalCoverPi2
public import RequestProject.SquareMovingBasepoint

@[expose] public section

/-! Invariance of the challenge's actual based-square zero condition under ordinary
homotopies and homotopy equivalences. Base points need not be fixed by the homotopies. -/

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Whitehead
open scoped unitInterval Topology

variable {X Y Z : Type}
variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

theorem killsPi2_precompose (f : C(X, Y)) (g : C(Y, Z)) (hg : KillsPi2 g) :
    KillsPi2 (g.comp f) := by
  intro x p
  exact hg (f x) (mapSquare f p)

theorem killsPi2_postcompose (f : C(X, Y)) (g : C(Y, Z)) (hf : KillsPi2 f) :
    KillsPi2 (g.comp f) := by
  intro x p
  have h := mapSquare_homotopic g (hf x p)
  simpa only [mapSquare_const, ← mapSquare_comp] using h

/-- An ordinary homotopy preserves the vanishing of the induced second homotopy map. -/
theorem killsPi2_of_homotopic {f g : C(X, Y)} (hfg : f.Homotopic g)
    (hg : KillsPi2 g) : KillsPi2 f := by
  obtain ⟨H⟩ := hfg
  intro x p
  obtain ⟨G⟩ := hg x p
  have hz₀ : (fun _ : Fin 2 => (0 : I)) ∈ Cube.boundary (Fin 2) := ⟨0, Or.inl rfl⟩
  let F : ContinuousMap.HomotopyWith (mapSquare f p).val (mapSquare g p).val
      SquareConstantBoundary := {
    toHomotopy := H.compContinuousMap p.val
    prop' := by
      intro t z hz
      change H (t, p z) = H (t, p (fun _ => 0))
      rw [GenLoop.boundary p z hz, GenLoop.boundary p _ hz₀] }
  let G' : ContinuousMap.HomotopyWith (mapSquare g p).val
      (ContinuousMap.const _ (g x)) SquareConstantBoundary := {
    toHomotopy := G.toHomotopy
    prop' := by
      intro t z hz
      change G (t, z) = G (t, fun _ => 0)
      rw [G.eq_fst t hz, G.eq_fst t hz₀]
      exact (GenLoop.boundary (mapSquare g p) z hz).trans
        (GenLoop.boundary (mapSquare g p) _ hz₀).symm }
  exact genLoop_null_of_movingBoundary (mapSquare f p) (F.trans G')

theorem killsPi2_homotopic_iff {f g : C(X, Y)} (hfg : f.Homotopic g) :
    KillsPi2 f ↔ KillsPi2 g :=
  ⟨killsPi2_of_homotopic hfg.symm, killsPi2_of_homotopic hfg⟩

/-- A homotopy equivalence in the target reflects the based-square zero condition. -/
theorem killsPi2_homotopyEquiv_postcomp_iff (e : ContinuousMap.HomotopyEquiv Y Z)
    (f : C(X, Y)) : KillsPi2 (e.toFun.comp f) ↔ KillsPi2 f := by
  constructor
  · intro h
    have hk := killsPi2_postcompose (e.toFun.comp f) e.invFun h
    change KillsPi2 ((e.invFun.comp e.toFun).comp f) at hk
    have hh : ((e.invFun.comp e.toFun).comp f).Homotopic f := by
      simpa using e.left_inv.comp (ContinuousMap.Homotopic.refl f)
    exact (killsPi2_homotopic_iff hh).mp hk
  · exact killsPi2_postcompose f e.toFun

/-- A homotopy equivalence in the source reflects the based-square zero condition. -/
theorem killsPi2_homotopyEquiv_precomp_iff (e : ContinuousMap.HomotopyEquiv X Y)
    (f : C(Y, Z)) : KillsPi2 (f.comp e.toFun) ↔ KillsPi2 f := by
  constructor
  · intro h
    have hk := killsPi2_precompose e.invFun (f.comp e.toFun) h
    change KillsPi2 (f.comp (e.toFun.comp e.invFun)) at hk
    have hh : (f.comp (e.toFun.comp e.invFun)).Homotopic f := by
      simpa using (ContinuousMap.Homotopic.refl f).comp e.right_inv
    exact (killsPi2_homotopic_iff hh).mp hk
  · exact killsPi2_precompose e.toFun f

/-- The zero condition is transported across a homotopy-commutative square whose
vertical maps are genuine homotopy equivalences. -/
theorem killsPi2_homotopyEquiv_square_iff {X' Y' : Type}
    [TopologicalSpace X'] [TopologicalSpace Y']
    (e : ContinuousMap.HomotopyEquiv X X') (d : ContinuousMap.HomotopyEquiv Y Y')
    (f : C(X, Y)) (g : C(X', Y'))
    (h : (g.comp e.toFun).Homotopic (d.toFun.comp f)) :
    KillsPi2 g ↔ KillsPi2 f := by
  rw [← killsPi2_homotopyEquiv_precomp_iff e g]
  rw [killsPi2_homotopic_iff h]
  exact killsPi2_homotopyEquiv_postcomp_iff d f

end Whitehead
