import RequestProject.Statement
import RequestProject.SquareBoundary
import Mathlib.Topology.Homotopy.Lifting

/-! General topological covering/pi2 results moved unchanged from Solution. -/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Whitehead
open scoped unitInterval Topology

/-- Covering maps reflect based homotopies of two-dimensional loops. -/
theorem mapSquare_homotopic_iff_of_covering {E X : Type}
    [TopologicalSpace E] [TopologicalSpace X] (p : C(E, X))
    (hp : IsCoveringMap p) {e : E} (a b : GenLoop (Fin 2) E e) :
    GenLoop.Homotopic (mapSquare p a) (mapSquare p b) ↔ GenLoop.Homotopic a b := by
  exact (hp.homotopicRel_iff_comp (f₀ := a.1) (f₁ := b.1) (S := Cube.boundary (Fin 2))
    ⟨fun _ => 0, ⟨0, Or.inl rfl⟩,
      (GenLoop.boundary a _ ⟨0, Or.inl rfl⟩).trans (GenLoop.boundary b _ ⟨0, Or.inl rfl⟩).symm⟩).symm

theorem mapSquare_homotopic {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) {x : X} {p q : GenLoop (Fin 2) X x}
    (h : GenLoop.Homotopic p q) : GenLoop.Homotopic (mapSquare f p) (mapSquare f q) :=
  h.comp_continuousMap f

@[simp] theorem mapSquare_const {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (x : X) : mapSquare f (GenLoop.const (x := x)) = GenLoop.const := by
  apply GenLoop.ext
  intro t
  rfl

/-- The continuous map induced on Mathlib's topological second homotopy quotient. -/
def pi2Map {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (x : X) : HomotopyGroup (Fin 2) X x → HomotopyGroup (Fin 2) Y (f x) :=
  Quotient.map (mapSquare f) (fun _ _ h => mapSquare_homotopic f h)

/-- A covering map is injective on Mathlib's actual second homotopy group. -/
theorem pi2Map_injective_of_covering {E X : Type}
    [TopologicalSpace E] [TopologicalSpace X] (p : C(E, X))
    (hp : IsCoveringMap p) (e : E) : Function.Injective (pi2Map p e) := by
  intro a b
  induction a using Quotient.inductionOn with
  | h a =>
    induction b using Quotient.inductionOn with
    | h b =>
      intro he
      exact Quotient.sound ((mapSquare_homotopic_iff_of_covering p hp a b).mp
        (Quotient.exact he))

/-- Radial contraction of the square, used to construct covering lifts directly. -/
def radialSquare : C(I × (Fin 2 → I), Fin 2 → I) where
  toFun ta i := ta.1 * ta.2 i
  continuous_toFun := continuous_pi (fun i =>
    (continuous_fst.subtype_val.mul
      (((continuous_apply i).comp continuous_snd).subtype_val)).subtype_mk _)

/-- A based square lifts through a covering map, including its constant boundary. -/
theorem exists_mapSquare_lift {E X : Type} [TopologicalSpace E] [TopologicalSpace X]
    (p : C(E, X)) (hp : IsCoveringMap p) (e : E) (q : GenLoop (Fin 2) X (p e)) :
    ∃ a : GenLoop (Fin 2) E e, mapSquare p a = q := by
  let z : Fin 2 → I := fun _ => 0
  have hz : z ∈ Cube.boundary (Fin 2) := ⟨0, Or.inl rfl⟩
  let H : C(I × (Fin 2 → I), X) := q.1.comp radialSquare
  have H0 : ∀ t, H (0, t) = p e := by
    intro t
    change q (fun i => 0 * t i) = p e
    simpa only [zero_mul] using GenLoop.boundary q z hz
  let F := hp.liftHomotopy H (ContinuousMap.const _ e) H0
  let G : C((Fin 2 → I), E) := F.comp ⟨fun t => (1, t), continuous_const.prodMk continuous_id⟩
  have hG : ∀ t, p (G t) = q t := by
    intro t
    have he := congrFun (hp.liftHomotopy_lifts H (ContinuousMap.const _ e) H0) (1, t)
    change p (F (1, t)) = q (fun i => 1 * t i) at he
    simp only [one_mul] at he
    exact he

  have hbase : G z = e := by
    have he := hp.const_of_comp (g := fun t : I => F (t, z))
      (F.continuous.comp (continuous_id.prodMk continuous_const))
      (fun t s => by
        have ht := congrFun (hp.liftHomotopy_lifts H (ContinuousMap.const _ e) H0) (t, z)
        have hs := congrFun (hp.liftHomotopy_lifts H (ContinuousMap.const _ e) H0) (s, z)
        change p (F (t, z)) = q (fun i => t * z i) at ht
        change p (F (s, z)) = q (fun i => s * z i) at hs
        simp only [z, mul_zero] at ht hs
        exact ht.trans hs.symm) 1 0
    exact he.trans (hp.liftHomotopy_zero H (ContinuousMap.const _ e) H0 z)
  have hboundary : ∀ t ∈ Cube.boundary (Fin 2), G t = e := by
    intro t ht
    have he := hp.constOn_of_comp square_boundary_isPreconnected G.continuous.continuousOn
      (fun a ha b hb => (hG a).trans
        ((GenLoop.boundary q a ha).trans ((GenLoop.boundary q b hb).symm.trans (hG b).symm)))
      ht hz
    exact he.trans hbase
  refine ⟨⟨G, hboundary⟩, ?_⟩
  apply GenLoop.ext
  exact hG

/-- Covering maps are surjective on actual topological second homotopy groups. -/
theorem pi2Map_surjective_of_covering {E X : Type}
    [TopologicalSpace E] [TopologicalSpace X] (p : C(E, X))
    (hp : IsCoveringMap p) (e : E) : Function.Surjective (pi2Map p e) := by
  intro q
  induction q using Quotient.inductionOn with
  | h q =>
    obtain ⟨a, ha⟩ := exists_mapSquare_lift p hp e q
    exact ⟨Quotient.mk _ a, congrArg (Quotient.mk _) ha⟩

theorem mapSquare_transAt {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) {x : X} (i : Fin 2) (p q : GenLoop (Fin 2) X x) :
    mapSquare f (GenLoop.transAt i p q) =
      GenLoop.transAt i (mapSquare f p) (mapSquare f q) := by
  apply GenLoop.ext
  intro t
  change f (if (t i : ℝ) ≤ 1 / 2 then _ else _) =
    if (t i : ℝ) ≤ 1 / 2 then _ else _
  split_ifs <;> rfl

theorem mapSquare_comp {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] (f : C(Y, Z)) (g : C(X, Y)) {x : X}
    (a : GenLoop (Fin 2) X x) :
    mapSquare (f.comp g) a = mapSquare f (mapSquare g a) := by
  apply GenLoop.ext
  intro t
  simp [mapSquare, ContinuousMap.comp_apply]

/-- Functoriality on the actual group structure of second homotopy. -/
def pi2MapHom {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (x : X) :
    HomotopyGroup (Fin 2) X x →* HomotopyGroup (Fin 2) Y (f x) where
  toFun := pi2Map f x
  map_one' := by
    change Quotient.mk _ (mapSquare f GenLoop.const) = Quotient.mk _ GenLoop.const
    rw [mapSquare_const]
  map_mul' a b := by
    induction a using Quotient.inductionOn with
    | _ p =>
      induction b using Quotient.inductionOn with
      | _ q =>
        calc
          pi2Map f x (@Mul.mul (HomotopyGroup (Fin 2) X x) inferInstance
              (Quotient.mk _ p) (Quotient.mk _ q)) =
              pi2Map f x (Quotient.mk _ (GenLoop.transAt 0 q p)) :=
            congrArg (pi2Map f x) (HomotopyGroup.mul_spec (i := (0 : Fin 2)))
          _ = (Quotient.mk _ (GenLoop.transAt 0 (mapSquare f q) (mapSquare f p)) : HomotopyGroup (Fin 2) Y (f x)) := by
            show Quotient.mk _ (mapSquare f (GenLoop.transAt 0 q p)) = _
            exact congrArg (Quotient.mk _) (mapSquare_transAt f 0 q p)
          _ = pi2Map f x (Quotient.mk _ p) * pi2Map f x (Quotient.mk _ q) :=
            (HomotopyGroup.mul_spec (i := (0 : Fin 2))).symm

/-- The square-map formulation in the challenge is exactly the zero-map condition on
Mathlib's topological homotopy group, not an auxiliary algebraic substitute. -/
theorem killsPi2_iff {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) : KillsPi2 f ↔ ∀ x z, pi2Map f x z = 1 := by
  constructor
  · intro h x z
    induction z using Quotient.inductionOn with
    | _ p => exact Quotient.sound (h x p)
  · intro h x p
    exact Quotient.exact (h x (Quotient.mk _ p))

/-- A covering induces an isomorphism on topological second homotopy groups. -/
noncomputable def pi2CoverEquiv {E X : Type}
    [TopologicalSpace E] [TopologicalSpace X] (p : C(E, X))
    (hp : IsCoveringMap p) (e : E) :
    HomotopyGroup (Fin 2) E e ≃* HomotopyGroup (Fin 2) X (p e) :=
  MulEquiv.ofBijective (pi2MapHom p e)
    ⟨pi2Map_injective_of_covering p hp e, pi2Map_surjective_of_covering p hp e⟩

/-- Postcomposing with a covering reflects the zero-map condition on `π₂`. -/
theorem killsPi2_covering_postcomp_iff {Y E X : Type}
    [TopologicalSpace Y] [TopologicalSpace E] [TopologicalSpace X]
    (f : C(Y, E)) (p : C(E, X)) (hp : IsCoveringMap p) :
    KillsPi2 (p.comp f) ↔ KillsPi2 f := by
  constructor
  · intro h y a
    apply (mapSquare_homotopic_iff_of_covering p hp (mapSquare f a) GenLoop.const).mp
    have := h y a
    simp only [ContinuousMap.comp_apply, mapSquare_comp] at this
    simpa only [mapSquare_const] using this
  · intro h y a
    have he := mapSquare_homotopic p (h y a)
    simp only [← mapSquare_comp, ← ContinuousMap.comp_apply] at he
    simpa only [mapSquare_const] using he

/-- Surjective coverings also reflect the zero-map condition when precomposed. -/
theorem killsPi2_covering_precomp_iff {E X Y : Type}
    [TopologicalSpace E] [TopologicalSpace X] [TopologicalSpace Y]
    (p : C(E, X)) (hp : IsCoveringMap p) (hs : Function.Surjective p)
    (f : C(X, Y)) : KillsPi2 (f.comp p) ↔ KillsPi2 f := by
  constructor
  · intro h x q
    obtain ⟨e, rfl⟩ := hs x
    obtain ⟨a, ha⟩ := exists_mapSquare_lift p hp e q
    have he := h e a
    change GenLoop.Homotopic (mapSquare f (mapSquare p a)) GenLoop.const at he
    rwa [ha] at he
  · intro h e a
    exact h (p e) (mapSquare p a)

end Whitehead
