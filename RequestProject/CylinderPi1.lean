module

public import Mathlib

@[expose] public section

/-!
# The double mapping cylinder and step 1 of Lemma 3.6 (Davis–Januszkiewicz–Weinberger 3.1)

Lemma `lem:geometric-pushout` of the paper considers, for a connected two-complex `X`, a
cellular map `a : Σ_q → X` and the pair `Σ_q ⊂ M_q` produced by the block construction, the
double mapping cylinder

  `W = X ∪_a (Σ_q × [0,1]) ∪_{Σ_q} M_q`

and asserts two things: `π₁(X) → π₁(W)` is injective, and `π₂(W)` is generated over
`ℤ[π₁(W)]` by the image of `π₂(X)`.

This file formalises the **space** `W` and the logical skeleton of step 1 (the radial
retraction argument, which is Lemma 2.2 of Davis–Januszkiewicz–Weinberger, used on
p. 540 of that paper).  Everything here is genuine point-set/homotopy theory, carried out
with Mathlib's fundamental group; nothing is assumed.

* `FiniteChains.Cylinder.DoubleCylinder a b` — the double mapping cylinder of
  `X ←a– S –b→ M`, as the quotient of `X ⊕ (S × [0,1]) ⊕ M` gluing `(s,0)` to `a s` and
  `(s,1)` to `b s`;
* `FiniteChains.Cylinder.lift` — its universal property: three maps on the three pieces
  which agree along the two gluing surfaces determine a map on `W` ("these maps agree along
  the gluing surfaces and give a retraction");
* `FiniteChains.Cylinder.exists_retraction_of_extends` — if `a` extends over `M` through `b`
  up to homotopy, then `W` retracts onto its copy of `X`;
* `FiniteChains.Cylinder.injective_pi1_inclX_of_extends` — hence in that case
  `π₁(X) → π₁(W)` is injective;
* `FiniteChains.Cylinder.injective_map_of_retraction`, `injective_map_of_isCoveringMap`,
  `injective_pi1_of_retracting_cover` — the general statements behind step 1: a retraction
  is injective on `π₁`, a covering map is injective on `π₁`, and therefore a space which
  admits a covering in which the chosen lift of `X` is a retract has `π₁(X) → π₁(W)`
  injective.  In the paper the covering is the pullback of the universal cover of `C_q`, the
  chosen copy of `X` is retracted radially, and the extension hypothesis of
  `exists_retraction_of_extends` is what holds on all the other copies (there the radial
  projection is defined on the whole cone, so its restriction to the boundary is
  null-homotopic).

What is *not* proved here is the existence of that covering together with its radial
retraction for the concrete block `M_q`; that is the CAT(0) input of the paper.
-/

namespace FiniteChains
namespace Cylinder

open unitInterval

universe u

/-! ## Functoriality of the fundamental group -/

section Functorial

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- `π₁` is functorial: the map induced by a composite is the composite of the induced
maps. -/
theorem map_comp_apply (f : C(X, Y)) (g : C(Y, Z)) (x : X) (u : FundamentalGroup X x) :
    FundamentalGroup.map (g.comp f) x u
      = FundamentalGroup.map g (f x) (FundamentalGroup.map f x u) := by
  simp only [FundamentalGroup.map_apply]
  induction u using Quotient.inductionOn with
  | h p => rfl

/-- `π₁` is functorial: the identity induces the identity. -/
theorem map_id_apply (x : X) (u : FundamentalGroup X x) :
    FundamentalGroup.map (ContinuousMap.id X) x u = u := by
  simp only [FundamentalGroup.map_apply]
  induction u using Quotient.inductionOn with
  | h p => rfl

/-- **A retract is `π₁`-injective.**  This is the form in which the radial retraction of
Davis–Januszkiewicz–Weinberger is used. -/
theorem injective_map_of_retraction (i : C(X, Y)) (r : C(Y, X))
    (hr : r.comp i = ContinuousMap.id X) (x : X) :
    Function.Injective (FundamentalGroup.map i x) := by
  intro u v huv
  have h1 : FundamentalGroup.map (r.comp i) x u = FundamentalGroup.map (r.comp i) x v := by
    rw [map_comp_apply, map_comp_apply, huv]
  rw [hr] at h1
  rwa [map_id_apply, map_id_apply] at h1

/-- **A covering map is `π₁`-injective.** -/
theorem injective_map_of_isCoveringMap {p : C(Y, Z)} (hp : IsCoveringMap p) (y : Y) :
    Function.Injective (FundamentalGroup.map p y) := by
  intro u v huv
  simp only [FundamentalGroup.map_apply] at huv
  exact hp.injective_path_homotopic_map y y huv

/-- **Step 1 of Lemma 3.6, in general form.**  If a space `W` has a covering `p : Ŵ → W` in
which the inclusion of `X` lifts to a map `î` admitting a retraction, then `π₁(X) → π₁(W)`
is injective. -/
theorem injective_pi1_of_retracting_cover {W Wc : Type*} [TopologicalSpace W]
    [TopologicalSpace Wc] (iX : C(X, W)) (p : C(Wc, W)) (hp : IsCoveringMap p)
    (î : C(X, Wc)) (hcomm : p.comp î = iX) (r : C(Wc, X))
    (hr : r.comp î = ContinuousMap.id X) (x : X) :
    Function.Injective (FundamentalGroup.map iX x) := by
  subst hcomm
  intro u v huv
  rw [map_comp_apply, map_comp_apply] at huv
  exact injective_map_of_retraction î r hr x (injective_map_of_isCoveringMap hp _ huv)

end Functorial

/-! ## The double mapping cylinder -/

section DoubleCylinder

variable (X S M : Type u) [TopologicalSpace X] [TopologicalSpace S] [TopologicalSpace M]

/-- The three pieces of the double mapping cylinder. -/
abbrev Pieces := X ⊕ (S × I) ⊕ M

variable {X S M}

/-- The gluing relation of the double mapping cylinder: the bottom `S × {0}` of the cylinder
is attached to `X` along `a`, the top `S × {1}` is attached to `M` along `b`. -/
inductive Glue (a : C(S, X)) (b : C(S, M)) : Pieces X S M → Pieces X S M → Prop
  | left (s : S) : Glue a b (Sum.inr (Sum.inl (s, 0))) (Sum.inl (a s))
  | right (s : S) : Glue a b (Sum.inr (Sum.inl (s, 1))) (Sum.inr (Sum.inr (b s)))

/-- The **double mapping cylinder** `W = X ∪_a (S × [0,1]) ∪_b M`. -/
def DoubleCylinder (a : C(S, X)) (b : C(S, M)) : Type u := Quot (Glue a b)

instance (a : C(S, X)) (b : C(S, M)) : TopologicalSpace (DoubleCylinder a b) :=
  inferInstanceAs (TopologicalSpace (Quot _))

variable (a : C(S, X)) (b : C(S, M))

/-- The copy of `X` inside the double mapping cylinder. -/
def inclX : C(X, DoubleCylinder a b) := ⟨fun x => Quot.mk _ (Sum.inl x), by fun_prop⟩

/-- The copy of `M` inside the double mapping cylinder. -/
def inclM : C(M, DoubleCylinder a b) := ⟨fun m => Quot.mk _ (Sum.inr (Sum.inr m)), by fun_prop⟩

/-- The cylinder inside the double mapping cylinder. -/
def inclCyl : C(S × I, DoubleCylinder a b) :=
  ⟨fun z => Quot.mk _ (Sum.inr (Sum.inl z)), by fun_prop⟩

@[simp] theorem inclCyl_zero (s : S) : inclCyl a b (s, 0) = inclX a b (a s) :=
  Quot.sound (Glue.left s)

@[simp] theorem inclCyl_one (s : S) : inclCyl a b (s, 1) = inclM a b (b s) :=
  Quot.sound (Glue.right s)

theorem inclX_surjOn (w : DoubleCylinder a b) :
    (∃ x, w = inclX a b x) ∨ (∃ z, w = inclCyl a b z) ∨ ∃ m, w = inclM a b m := by
  induction w using Quot.ind with
  | mk w =>
      match w with
      | Sum.inl x => exact Or.inl ⟨x, rfl⟩
      | Sum.inr (Sum.inl z) => exact Or.inr (Or.inl ⟨z, rfl⟩)
      | Sum.inr (Sum.inr m) => exact Or.inr (Or.inr ⟨m, rfl⟩)

/-- **The universal property of the double mapping cylinder.**  Maps on the three pieces
which agree along the two gluing surfaces glue to a map on `W`. -/
def lift {T : Type*} [TopologicalSpace T] (fX : C(X, T)) (fCyl : C(S × I, T)) (fM : C(M, T))
    (h0 : ∀ s, fCyl (s, 0) = fX (a s)) (h1 : ∀ s, fCyl (s, 1) = fM (b s)) :
    C(DoubleCylinder a b, T) := by
  refine ⟨Quot.lift (Sum.elim fX (Sum.elim fCyl fM)) ?_, ?_⟩
  · rintro _ _ (s | s)
    · exact h0 s
    · exact h1 s
  · exact continuous_quot_lift _ (by fun_prop)

@[simp] theorem lift_inclX {T : Type*} [TopologicalSpace T] (fX : C(X, T)) (fCyl : C(S × I, T))
    (fM : C(M, T)) (h0 : ∀ s, fCyl (s, 0) = fX (a s)) (h1 : ∀ s, fCyl (s, 1) = fM (b s))
    (x : X) : lift a b fX fCyl fM h0 h1 (inclX a b x) = fX x := rfl

@[simp] theorem lift_inclCyl {T : Type*} [TopologicalSpace T] (fX : C(X, T)) (fCyl : C(S × I, T))
    (fM : C(M, T)) (h0 : ∀ s, fCyl (s, 0) = fX (a s)) (h1 : ∀ s, fCyl (s, 1) = fM (b s))
    (z : S × I) : lift a b fX fCyl fM h0 h1 (inclCyl a b z) = fCyl z := rfl

@[simp] theorem lift_inclM {T : Type*} [TopologicalSpace T] (fX : C(X, T)) (fCyl : C(S × I, T))
    (fM : C(M, T)) (h0 : ∀ s, fCyl (s, 0) = fX (a s)) (h1 : ∀ s, fCyl (s, 1) = fM (b s))
    (m : M) : lift a b fX fCyl fM h0 h1 (inclM a b m) = fM m := rfl

/-- Inside `W` the attaching map `a` is homotopic to the composite of `b` with the inclusion
of `M`: the cylinder provides the homotopy. -/
theorem inclX_comp_a_homotopic :
    ((inclX a b).comp a).Homotopic ((inclM a b).comp b) :=
  ⟨{ toFun := fun z => inclCyl a b (z.2, z.1)
     map_zero_left := fun s => inclCyl_zero a b s
     map_one_left := fun s => inclCyl_one a b s }⟩

/-- **A retraction onto the copy of `X`, when `a` extends over `M`.**  If there is a map
`fM : M → X` and a homotopy from `a` to `fM ∘ b`, then the double mapping cylinder retracts
onto its copy of `X`.  In the covering space of the paper this is the situation at every
copy of `X` other than the chosen one: there the radial projection is defined on the whole
cone, so its restriction to the boundary surface is null-homotopic and the required
extension exists. -/
theorem exists_retraction_of_extends (fM : C(M, X)) (H : C(S × I, X))
    (h0 : ∀ s, H (s, 0) = a s) (h1 : ∀ s, H (s, 1) = fM (b s)) :
    ∃ r : C(DoubleCylinder a b, X), r.comp (inclX a b) = ContinuousMap.id X := by
  refine ⟨lift a b (ContinuousMap.id X) H fM (fun s => h0 s) (fun s => h1 s), ?_⟩
  ext x
  rfl

/-- **Injectivity on `π₁` in the extendable case.**  If `a` extends over `M` through `b` up
to homotopy, then `π₁(X) → π₁(W)` is injective. -/
theorem injective_pi1_inclX_of_extends (fM : C(M, X)) (H : C(S × I, X))
    (h0 : ∀ s, H (s, 0) = a s) (h1 : ∀ s, H (s, 1) = fM (b s)) (x : X) :
    Function.Injective (FundamentalGroup.map (inclX a b) x) := by
  obtain ⟨r, hr⟩ := exists_retraction_of_extends a b fM H h0 h1
  exact injective_map_of_retraction _ r hr x

/-- **The null-homotopic case.**  If the attaching map `a` is null-homotopic then
`π₁(X) → π₁(W)` is injective.  This is the situation at the copies of `X` other than the
chosen one in the covering used by Davis–Januszkiewicz–Weinberger: there the radial
projection is defined on the whole cone, so its restriction to the boundary surface is
null-homotopic, and the retraction is constant on that copy. -/
theorem injective_pi1_inclX_of_nullhomotopic (x₀ : X)
    (h : (a : C(S, X)).Homotopic (ContinuousMap.const S x₀)) (x : X) :
    Function.Injective (FundamentalGroup.map (inclX a b) x) := by
  obtain ⟨H⟩ := h
  refine injective_pi1_inclX_of_extends a b (ContinuousMap.const M x₀)
    ⟨fun z => H (z.2, z.1), by fun_prop⟩ (fun s => H.apply_zero s) (fun s => H.apply_one s) x

end DoubleCylinder

end Cylinder
end FiniteChains
