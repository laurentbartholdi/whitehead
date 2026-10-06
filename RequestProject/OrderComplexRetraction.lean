module

public import RequestProject.OrderComplexHtpyIn

@[expose] public section

/-!
# A retraction on path classes across one gluing step

Let a subposet `U` of an ambient poset be covered by two subposets `A` and `B` such that no
comparability inside `U` is mixed, and let `J = A ∩ B` be nonempty, connected and simply
connected.  Then the inclusion of `A` into `U` is injective on path classes: a loop inside `A`
which is null-homotopic inside `U` is already null-homotopic inside `A`.

Nothing is assumed about the fundamental group of `B`.  The proof is the explicit van Kampen
retraction, written directly on edge paths:

* choose a vertex `j0` of `J` and, for every vertex `v` of `J`, a path `γ v : j0 → v` inside
  `J` (`γ v = []` for the vertices that are not in `J`);
* `FiniteChains.Comb.retrVert` sends a vertex to itself if it lies in `A` and to `j0`
  otherwise;
* `FiniteChains.Comb.retrGerm` sends an oriented edge of `A` to itself and any other oriented
  edge `u → v` to `γ u ⁻¹ γ v`;
* `FiniteChains.Comb.retrPath` applies this edgewise.

The two formulas agree, up to homotopy inside `A`, on the edges of `J`: this is exactly where
the simple connectedness of `J` is used (`FiniteChains.Comb.htpyIn_retrGerm_of_pathIn_B`).  The
elementary cancellations are then preserved (`FiniteChains.Comb.htpyIn_retrPath_of_stepIn`):
backtracks cancel, a two-cell of `A` is unchanged, and for a two-cell of `B` the chosen paths
telescope around its boundary.  Since a path inside `A` is returned unchanged, the assignment is
a retraction on path classes, which is the statement
`FiniteChains.Comb.injIn_union_of_unmixed`.

The initial step of a chamber filtration is handled by
`FiniteChains.Comb.injIn_of_monotone_retraction`: a monotone retraction of a subposet onto a
smaller one is also injective on path classes.

Finally, `FiniteChains.Comb.injIn_of_directed` passes from the members of an increasing
exhaustion to the whole complex: a null-homotopy is a finite derivation, so it only involves
finitely many cells and therefore stays inside one member of the exhaustion.
-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains
namespace Comb

universe u

variable {P Q : Type u} [Preorder P] [Preorder Q]

/-! ### Injectivity on path classes -/

/-- **`B` is injective on path classes inside `U`**: a loop inside `B` that is null-homotopic
inside `U` is null-homotopic inside `B`. -/
def InjIn (U B : P → Prop) : Prop :=
  ∀ (v : P) (l : List ((orderCx P).E × Bool)), B v →
    IsPath (orderCx P).src (orderCx P).tgt l v v → PathIn B l →
    HtpyIn U v v l [] → HtpyIn B v v l []

/-- Every loop inside `J` is null-homotopic inside `J`. -/
def SimplyConnectedIn (J : P → Prop) : Prop :=
  ∀ (v : P) (l : List ((orderCx P).E × Bool)), J v →
    IsPath (orderCx P).src (orderCx P).tgt l v v → PathIn J l → HtpyIn J v v l []

theorem injIn_self (U : P → Prop) : InjIn U U := fun _ _ _ _ _ h => h

/-- Both endpoints of an oriented edge with endpoints in `C` lie in `C`. -/
theorem germ_ends {C : P → Prop} {eb : (orderCx P).E × Bool} (h : C eb.1.1.1 ∧ C eb.1.1.2) :
    C (germSrc (orderCx P).src (orderCx P).tgt eb) ∧
      C (germTgt (orderCx P).src (orderCx P).tgt eb) := by
  obtain ⟨e, tag⟩ := eb
  cases tag
  · exact ⟨h.2, h.1⟩
  · exact ⟨h.1, h.2⟩

/-- Injectivity on path classes only depends on the ambient subposet up to equivalence. -/
theorem injIn_congr_left {U U' B : P → Prop} (h : ∀ x, U x ↔ U' x) (hinj : InjIn U B) :
    InjIn U' B :=
  fun v l hv hp hl hh => hinj v l hv hp hl (HtpyIn.mono (fun x hx => (h x).2 hx) hh)

/-- Injectivity on path classes composes. -/
theorem injIn_trans {U A B : P → Prop} (hBA : ∀ x, B x → A x)
    (hUA : InjIn U A) (hAB : InjIn A B) : InjIn U B := by
  intro v l hv hp hl h
  exact hAB v l hv hp hl (hUA v l (hBA v hv) hp (pathIn_mono hBA hl) h)

/-- Simple connectedness of a subposet, in the form produced by the order-complex results of the
project. -/
theorem simplyConnectedIn_of_simplyConnected {J : P → Prop}
    (hJ : SimplyConnected (orderCx {x : P // J x})) : SimplyConnectedIn J := by
  intro v l hv hp hl
  have hlift := isPath_liftPathIn l hl hv hv hp
  have hnull := hJ ⟨v, hv⟩ (liftPathIn l hl) hlift
  have h := htpyIn_mapPath (C := J) (fun x : {x : P // J x} => (x : P)) monotone_subtypeVal
    (fun x => x.2) hnull
  rw [show mapPath (orderCxMap (fun x : {x : P // J x} => (x : P)) monotone_subtypeVal)
      (liftPathIn l hl) = l from mapPath_liftPathIn l hl] at h
  simpa [mapPath] using h

/-! ### The retraction on paths -/

section Retr

variable (A : P → Prop) (j0 : P) (γ : P → List ((orderCx P).E × Bool))

open Classical in
/-- The retraction on vertices: a vertex of `A` stays where it is, any other vertex goes to the
base vertex `j0` of the intersection. -/
noncomputable def retrVert (u : P) : P := if A u then u else j0

open Classical in
/-- The retraction on oriented edges: an edge of `A` is unchanged, any other edge `u → v` is
replaced by `γ u ⁻¹ γ v`. -/
noncomputable def retrGerm (eb : (orderCx P).E × Bool) : List ((orderCx P).E × Bool) :=
  if A eb.1.1.1 ∧ A eb.1.1.2 then [eb]
  else revPath (γ (germSrc (orderCx P).src (orderCx P).tgt eb)) ++
    γ (germTgt (orderCx P).src (orderCx P).tgt eb)

/-- The retraction on edge paths. -/
noncomputable def retrPath : List ((orderCx P).E × Bool) → List ((orderCx P).E × Bool)
  | [] => []
  | eb :: t => retrGerm A γ eb ++ retrPath t

variable {A j0 γ}

@[simp] theorem retrPath_nil : retrPath A γ [] = [] := rfl

@[simp] theorem retrPath_cons (eb : (orderCx P).E × Bool) (t : List ((orderCx P).E × Bool)) :
    retrPath A γ (eb :: t) = retrGerm A γ eb ++ retrPath A γ t := rfl

theorem retrPath_append (l l' : List ((orderCx P).E × Bool)) :
    retrPath A γ (l ++ l') = retrPath A γ l ++ retrPath A γ l' := by
  induction l with
  | nil => rfl
  | cons eb t ih => simp [retrPath, ih, List.append_assoc]

omit [Preorder P] in
theorem retrVert_of_mem {u : P} (hu : A u) : retrVert A j0 u = u := by
  classical
  simp [retrVert, hu]

omit [Preorder P] in
theorem retrVert_of_not_mem {u : P} (hu : ¬ A u) : retrVert A j0 u = j0 := by
  classical
  simp [retrVert, hu]

theorem retrGerm_of_mem {eb : (orderCx P).E × Bool} (h : A eb.1.1.1 ∧ A eb.1.1.2) :
    retrGerm A γ eb = [eb] := by
  classical
  simp [retrGerm, h]

theorem retrGerm_of_not_mem {eb : (orderCx P).E × Bool} (h : ¬ (A eb.1.1.1 ∧ A eb.1.1.2)) :
    retrGerm A γ eb = revPath (γ (germSrc (orderCx P).src (orderCx P).tgt eb)) ++
      γ (germTgt (orderCx P).src (orderCx P).tgt eb) := by
  classical
  simp [retrGerm, h]

/-- A path inside `A` is returned unchanged. -/
theorem retrPath_eq_self {l : List ((orderCx P).E × Bool)} (hl : PathIn A l) :
    retrPath A γ l = l := by
  induction l with
  | nil => rfl
  | cons eb t ih =>
      obtain ⟨heb, ht⟩ := pathIn_of_cons hl
      rw [retrPath_cons, retrGerm_of_mem heb, ih ht, List.singleton_append]

/-- The retraction lands inside `A`. -/
theorem pathIn_retrPath (hγA : ∀ u : P, PathIn A (γ u)) (l : List ((orderCx P).E × Bool)) :
    PathIn A (retrPath A γ l) := by
  classical
  induction l with
  | nil => exact pathIn_nil A
  | cons eb t ih =>
      refine pathIn_append ?_ ih
      by_cases h : A eb.1.1.1 ∧ A eb.1.1.2
      · rw [retrGerm_of_mem h]
        exact pathIn_cons h (pathIn_nil A)
      · rw [retrGerm_of_not_mem h]
        exact pathIn_append (pathIn_revPath (hγA _)) (hγA _)

end Retr

/-! ### The gluing step -/

section Gluing

variable {A B U J : P → Prop} {j0 : P} {γ : P → List ((orderCx P).E × Bool)}

variable (hJA : ∀ x, J x → A x) (hJmk : ∀ x, A x → B x → J x)
  (hγpath : ∀ u : P, J u → IsPath (orderCx P).src (orderCx P).tgt (γ u) j0 u)
  (hγin : ∀ u : P, PathIn J (γ u)) (hγnil : ∀ u : P, ¬ J u → γ u = [])

include hJA hγin in
theorem pathIn_gamma_of_subset (u : P) : PathIn A (γ u) :=
  pathIn_mono hJA (hγin u)

include hJA hJmk hγpath hγnil in
/-- The chosen path from the base vertex to the image of a vertex of `B`. -/
theorem isPath_gamma {u : P} (hu : B u) :
    IsPath (orderCx P).src (orderCx P).tgt (γ u) j0 (retrVert A j0 u) := by
  by_cases hA : A u
  · rw [retrVert_of_mem hA]
    exact hγpath u (hJmk u hA hu)
  · rw [retrVert_of_not_mem hA, hγnil u (fun h => hA (hJA u h))]
    rfl

include hJA hJmk hγpath hγnil in
/-- The image of an oriented edge is a path between the images of its endpoints. -/
theorem isPath_retrGerm (hmix : ∀ a b : P, a ≤ b → U a → U b → (A a ∧ A b) ∨ (B a ∧ B b))
    {eb : (orderCx P).E × Bool} (h1 : U eb.1.1.1) (h2 : U eb.1.1.2) :
    IsPath (orderCx P).src (orderCx P).tgt (retrGerm A γ eb)
      (retrVert A j0 (germSrc (orderCx P).src (orderCx P).tgt eb))
      (retrVert A j0 (germTgt (orderCx P).src (orderCx P).tgt eb)) := by
  classical
  by_cases hA : A eb.1.1.1 ∧ A eb.1.1.2
  · rw [retrGerm_of_mem hA]
    have hAs := germ_ends hA
    rw [retrVert_of_mem hAs.1, retrVert_of_mem hAs.2]
    exact isPath_single _
  · rw [retrGerm_of_not_mem hA]
    have hB : B eb.1.1.1 ∧ B eb.1.1.2 := by
      rcases hmix eb.1.1.1 eb.1.1.2 eb.1.2 h1 h2 with h | h
      · exact absurd h hA
      · exact h
    have hBs := germ_ends hB
    refine isPath_append_iff.mpr ⟨j0, ?_, isPath_gamma hJA hJmk hγpath hγnil hBs.2⟩
    exact isPath_revPath (isPath_gamma hJA hJmk hγpath hγnil hBs.1)

include hJA hJmk hγpath hγnil in
/-- The image of a path is a path between the images of its endpoints. -/
theorem isPath_retrPath (hmix : ∀ a b : P, a ≤ b → U a → U b → (A a ∧ A b) ∨ (B a ∧ B b)) :
    ∀ (l : List ((orderCx P).E × Bool)) {a b : P},
      IsPath (orderCx P).src (orderCx P).tgt l a b → PathIn U l →
      IsPath (orderCx P).src (orderCx P).tgt (retrPath A γ l) (retrVert A j0 a)
        (retrVert A j0 b) := by
  intro l
  induction l with
  | nil =>
      intro a b hp _
      have : a = b := hp
      subst this
      rfl
  | cons eb t ih =>
      intro a b hp hU
      obtain ⟨ha, hrest⟩ := hp
      subst ha
      obtain ⟨hUe, hUt⟩ := pathIn_of_cons hU
      refine isPath_append_iff.mpr
        ⟨retrVert A j0 (germTgt (orderCx P).src (orderCx P).tgt eb), ?_, ih hrest hUt⟩
      exact isPath_retrGerm hJA hJmk hγpath hγnil hmix hUe.1 hUe.2

include hJA hJmk hγpath hγin in
/-- **On the edges of `J` the two formulas agree.**  This is the only place where the simple
connectedness of the intersection is used. -/
theorem htpyIn_retrGerm_of_pathIn_B (hJsc : SimplyConnectedIn J) (hj0 : J j0)
    {eb : (orderCx P).E × Bool} (hB : B eb.1.1.1 ∧ B eb.1.1.2) :
    HtpyIn A (retrVert A j0 (germSrc (orderCx P).src (orderCx P).tgt eb))
      (retrVert A j0 (germTgt (orderCx P).src (orderCx P).tgt eb))
      (retrGerm A γ eb)
      (revPath (γ (germSrc (orderCx P).src (orderCx P).tgt eb)) ++
        γ (germTgt (orderCx P).src (orderCx P).tgt eb)) := by
  classical
  by_cases hA : A eb.1.1.1 ∧ A eb.1.1.2
  · -- the edge lies in `J`
    set s : P := germSrc (orderCx P).src (orderCx P).tgt eb with hs
    set t : P := germTgt (orderCx P).src (orderCx P).tgt eb with ht
    have hAs : A s ∧ A t := germ_ends hA
    have hBs : B s ∧ B t := germ_ends hB
    have hJs : J s := hJmk s hAs.1 hBs.1
    have hJt : J t := hJmk t hAs.2 hBs.2
    have hγs : IsPath (orderCx P).src (orderCx P).tgt (γ s) j0 s := hγpath s hJs
    have hγt : IsPath (orderCx P).src (orderCx P).tgt (γ t) j0 t := hγpath t hJt
    have hγsA : PathIn A (γ s) := pathIn_gamma_of_subset hJA hγin s
    have hγtA : PathIn A (γ t) := pathIn_gamma_of_subset hJA hγin t
    have hebPath : IsPath (orderCx P).src (orderCx P).tgt [eb] s t := isPath_single eb
    have hebA : PathIn A [eb] := pathIn_cons hA (pathIn_nil A)
    -- the loop `γ s · eb · γ t ⁻¹` lies in `J` and is therefore null-homotopic inside `J`
    have hloopPath : IsPath (orderCx P).src (orderCx P).tgt
        (γ s ++ ([eb] ++ revPath (γ t))) j0 j0 :=
      isPath_append_iff.mpr ⟨s, hγs,
        isPath_append_iff.mpr ⟨t, hebPath, isPath_revPath hγt⟩⟩
    have hebJ : J eb.1.1.1 ∧ J eb.1.1.2 :=
      ⟨hJmk _ hA.1 hB.1, hJmk _ hA.2 hB.2⟩
    have hloopIn : PathIn J (γ s ++ ([eb] ++ revPath (γ t))) :=
      pathIn_append (hγin s)
        (pathIn_append (pathIn_cons hebJ (pathIn_nil J)) (pathIn_revPath (hγin t)))
    have hnull : HtpyIn A j0 j0 (γ s ++ ([eb] ++ revPath (γ t))) [] :=
      HtpyIn.mono hJA (hJsc j0 _ hj0 hloopPath hloopIn)
    -- conjugate the null-homotopy by `γ s ⁻¹` and `γ t`
    have hconj : HtpyIn A s t
        (revPath (γ s) ++ (γ s ++ ([eb] ++ revPath (γ t))) ++ γ t)
        (revPath (γ s) ++ [] ++ γ t) :=
      hnull.congr_append (isPath_revPath hγs) hγt (pathIn_revPath hγsA) hγtA
    -- the left-hand side is homotopic to `eb`
    have hcancel1 : HtpyIn A s s (revPath (γ s) ++ γ s) [] := htpyIn_revPath_append hγs hγsA
    have hcancel2 : HtpyIn A t t (revPath (γ t) ++ γ t) [] := htpyIn_revPath_append hγt hγtA
    have hstep1 : HtpyIn A s t ([eb] ++ (revPath (γ t) ++ γ t)) ([eb] ++ []) :=
      HtpyIn.append_congr hebPath
        (isPath_append_iff.mpr ⟨j0, isPath_revPath hγt, hγt⟩) hebA
        (pathIn_append (pathIn_revPath hγtA) hγtA) (HtpyIn.refl _) hcancel2
    have hstep2 : HtpyIn A s t ((revPath (γ s) ++ γ s) ++ ([eb] ++ (revPath (γ t) ++ γ t)))
        ([] ++ ([eb] ++ (revPath (γ t) ++ γ t))) :=
      HtpyIn.append_congr (isPath_append_iff.mpr ⟨j0, isPath_revPath hγs, hγs⟩)
        (isPath_append_iff.mpr ⟨t, hebPath, isPath_append_iff.mpr ⟨j0, isPath_revPath hγt, hγt⟩⟩)
        (pathIn_append (pathIn_revPath hγsA) hγsA)
        (pathIn_append hebA (pathIn_append (pathIn_revPath hγtA) hγtA))
        hcancel1 (HtpyIn.refl _)
    have hmain : HtpyIn A s t [eb] (revPath (γ s) ++ γ t) := by
      have h1 : HtpyIn A s t [eb] ((revPath (γ s) ++ γ s) ++ ([eb] ++ (revPath (γ t) ++ γ t))) := by
        refine (HtpyIn.trans ?_ hstep2.symm)
        simpa using hstep1.symm
      refine h1.trans ?_
      have h2 : (revPath (γ s) ++ γ s) ++ ([eb] ++ (revPath (γ t) ++ γ t)) =
          revPath (γ s) ++ (γ s ++ ([eb] ++ revPath (γ t))) ++ γ t := by
        simp [List.append_assoc]
      rw [h2]
      refine hconj.trans ?_
      simpa using HtpyIn.refl (A := A) (a := s) (b := t) (revPath (γ s) ++ γ t)
    rw [retrGerm_of_mem hA, retrVert_of_mem hAs.1, retrVert_of_mem hAs.2]
    exact hmain
  · rw [retrGerm_of_not_mem hA]
    exact HtpyIn.refl _

include hJA hJmk hγpath hγin hγnil in
/-- **Telescoping along a path of `B`.**  The image of a path of `B` from `u` to `v` is
homotopic, inside `A`, to `γ u ⁻¹ γ v`. -/
theorem htpyIn_retrPath_of_pathIn_B (hJsc : SimplyConnectedIn J) (hj0 : J j0) :
    ∀ (l : List ((orderCx P).E × Bool)) {u v : P},
      IsPath (orderCx P).src (orderCx P).tgt l u v → PathIn B l → B u → B v →
      HtpyIn A (retrVert A j0 u) (retrVert A j0 v) (retrPath A γ l)
        (revPath (γ u) ++ γ v) := by
  intro l
  induction l with
  | nil =>
      intro u v hp _ hu _
      have huv : u = v := hp
      subst huv
      have hγu : IsPath (orderCx P).src (orderCx P).tgt (γ u) j0 (retrVert A j0 u) :=
        isPath_gamma hJA hJmk hγpath hγnil hu
      have hγuA : PathIn A (γ u) := pathIn_gamma_of_subset hJA hγin u
      exact (htpyIn_revPath_append hγu hγuA).symm
  | cons eb t ih =>
      intro u v hp hBl hu hv
      obtain ⟨ha, hrest⟩ := hp
      subst ha
      obtain ⟨hBe, hBt⟩ := pathIn_of_cons hBl
      set m : P := germTgt (orderCx P).src (orderCx P).tgt eb with hm
      have hBm : B m := (germ_ends hBe).2
      have hγu : IsPath (orderCx P).src (orderCx P).tgt
          (γ (germSrc (orderCx P).src (orderCx P).tgt eb)) j0
          (retrVert A j0 (germSrc (orderCx P).src (orderCx P).tgt eb)) :=
        isPath_gamma hJA hJmk hγpath hγnil hu
      have hγm : IsPath (orderCx P).src (orderCx P).tgt (γ m) j0 (retrVert A j0 m) :=
        isPath_gamma hJA hJmk hγpath hγnil hBm
      have hγv : IsPath (orderCx P).src (orderCx P).tgt (γ v) j0 (retrVert A j0 v) :=
        isPath_gamma hJA hJmk hγpath hγnil hv
      have hγuA : PathIn A (γ (germSrc (orderCx P).src (orderCx P).tgt eb)) :=
        pathIn_gamma_of_subset hJA hγin _
      have hγmA : PathIn A (γ m) := pathIn_gamma_of_subset hJA hγin m
      have hγvA : PathIn A (γ v) := pathIn_gamma_of_subset hJA hγin v
      have hgerm := htpyIn_retrGerm_of_pathIn_B (A := A) (γ := γ) hJA hJmk hγpath hγin hJsc hj0 hBe
      have hih := ih hrest hBt hBm hv
      have hfirst : IsPath (orderCx P).src (orderCx P).tgt (retrGerm A γ eb)
          (retrVert A j0 (germSrc (orderCx P).src (orderCx P).tgt eb)) (retrVert A j0 m) := by
        refine HtpyIn.isPath hgerm.symm ?_
        exact isPath_append_iff.mpr ⟨j0, isPath_revPath hγu, hγm⟩
      have hsecond : IsPath (orderCx P).src (orderCx P).tgt (retrPath A γ t)
          (retrVert A j0 m) (retrVert A j0 v) :=
        HtpyIn.isPath hih.symm (isPath_append_iff.mpr ⟨j0, isPath_revPath hγm, hγv⟩)
      have hfirstA : PathIn A (retrGerm A γ eb) := by
        classical
        by_cases hA : A eb.1.1.1 ∧ A eb.1.1.2
        · rw [retrGerm_of_mem hA]; exact pathIn_cons hA (pathIn_nil A)
        · rw [retrGerm_of_not_mem hA]
          exact pathIn_append (pathIn_revPath hγuA) hγmA
      have hsecondA : PathIn A (retrPath A γ t) :=
        pathIn_retrPath (fun x => pathIn_gamma_of_subset hJA hγin x) t
      have hcomb : HtpyIn A (retrVert A j0 (germSrc (orderCx P).src (orderCx P).tgt eb))
          (retrVert A j0 v) (retrGerm A γ eb ++ retrPath A γ t)
          ((revPath (γ (germSrc (orderCx P).src (orderCx P).tgt eb)) ++ γ m) ++
            (revPath (γ m) ++ γ v)) :=
        HtpyIn.append_congr hfirst hsecond hfirstA hsecondA hgerm hih
      refine hcomb.trans ?_
      -- cancel `γ m ⁻¹ γ m` in the middle
      have hcancel : HtpyIn A j0 j0 (γ m ++ revPath (γ m)) [] :=
        htpyIn_append_revPath hγm hγmA
      have hmid : HtpyIn A (retrVert A j0 (germSrc (orderCx P).src (orderCx P).tgt eb))
          (retrVert A j0 v)
          (revPath (γ (germSrc (orderCx P).src (orderCx P).tgt eb)) ++
            (γ m ++ revPath (γ m)) ++ γ v)
          (revPath (γ (germSrc (orderCx P).src (orderCx P).tgt eb)) ++ [] ++ γ v) :=
        hcancel.congr_append (isPath_revPath hγu) hγv (pathIn_revPath hγuA) hγvA
      have hrw : (revPath (γ (germSrc (orderCx P).src (orderCx P).tgt eb)) ++ γ m) ++
          (revPath (γ m) ++ γ v) =
          revPath (γ (germSrc (orderCx P).src (orderCx P).tgt eb)) ++
            (γ m ++ revPath (γ m)) ++ γ v := by
        simp [List.append_assoc]
      rw [hrw]
      simpa using hmid

include hJA hJmk hγpath hγin hγnil in
/-- **The retraction respects one elementary cancellation.** -/
theorem htpyIn_retrPath_of_stepIn
    (hmix : ∀ a b : P, a ≤ b → U a → U b → (A a ∧ A b) ∨ (B a ∧ B b))
    (hJsc : SimplyConnectedIn J) (hj0 : J j0) {a b : P}
    {l l' : List ((orderCx P).E × Bool)} (h : StepIn U a b l l') :
    HtpyIn A (retrVert A j0 a) (retrVert A j0 b) (retrPath A γ l) (retrPath A γ l') := by
  classical
  obtain ⟨⟨hpl, hpl', hc⟩, hUl, hUl'⟩ := h
  have hγA : ∀ x : P, PathIn A (γ x) := fun x => pathIn_gamma_of_subset hJA hγin x
  rcases hc with ⟨p', q', eb, hlEq, hl'Eq⟩ | ⟨p', q', t, hlEq, hl'Eq⟩
  · -- a backtrack
    subst hlEq
    subst hl'Eq
    have hUp' : PathIn U p' := pathIn_of_append_left hUl
    have hUrest : PathIn U (eb :: revGerm eb :: q') := pathIn_of_append_right hUl
    obtain ⟨hUe, hUrest'⟩ := pathIn_of_cons hUrest
    have hUq' : PathIn U q' := (pathIn_of_cons hUrest').2
    -- endpoints of the pieces
    obtain ⟨c, hpc, hrest⟩ := isPath_append_iff.mp hpl
    obtain ⟨hcs, hrest2⟩ := hrest
    obtain ⟨hmid, hq'⟩ := hrest2
    have hPp' : IsPath (orderCx P).src (orderCx P).tgt (retrPath A γ p')
        (retrVert A j0 a) (retrVert A j0 c) :=
      isPath_retrPath hJA hJmk hγpath hγnil hmix p' hpc hUp'
    have hcq : IsPath (orderCx P).src (orderCx P).tgt q'
        (germTgt (orderCx P).src (orderCx P).tgt (revGerm eb)) b := hq'
    have hPq' : IsPath (orderCx P).src (orderCx P).tgt (retrPath A γ q')
        (retrVert A j0 (germTgt (orderCx P).src (orderCx P).tgt (revGerm eb)))
        (retrVert A j0 b) :=
      isPath_retrPath hJA hJmk hγpath hγnil hmix q' hcq hUq'
    have hrevTgt : germTgt (orderCx P).src (orderCx P).tgt (revGerm eb) =
        germSrc (orderCx P).src (orderCx P).tgt eb := germTgt_revGerm (X := orderCx P) eb
    -- the two images cancel
    have hkey : HtpyIn A (retrVert A j0 (germSrc (orderCx P).src (orderCx P).tgt eb))
        (retrVert A j0 (germSrc (orderCx P).src (orderCx P).tgt eb))
        (retrGerm A γ eb ++ retrGerm A γ (revGerm eb)) [] := by
      by_cases hA : A eb.1.1.1 ∧ A eb.1.1.2
      · have hA' : A (revGerm eb).1.1.1 ∧ A (revGerm eb).1.1.2 := hA
        rw [retrGerm_of_mem hA, retrGerm_of_mem hA']
        have hsrc : A (germSrc (orderCx P).src (orderCx P).tgt eb) := (germ_ends hA).1
        refine HtpyIn.of_step ⟨⟨?_, rfl, Or.inl ⟨[], [], eb, rfl, rfl⟩⟩, ?_, pathIn_nil A⟩
        · refine ⟨?_, ?_, ?_⟩
          · rw [retrVert_of_mem hsrc]
          · exact (germSrc_revGerm (X := orderCx P) eb).symm
          · rw [retrVert_of_mem hsrc]; exact germTgt_revGerm (X := orderCx P) eb
        · exact pathIn_cons hA (pathIn_cons hA (pathIn_nil A))
      · have hA' : ¬ (A (revGerm eb).1.1.1 ∧ A (revGerm eb).1.1.2) := hA
        rw [retrGerm_of_not_mem hA, retrGerm_of_not_mem hA']
        have hB : B eb.1.1.1 ∧ B eb.1.1.2 := by
          rcases hmix eb.1.1.1 eb.1.1.2 eb.1.2 hUe.1 hUe.2 with h | h
          · exact absurd h hA
          · exact h
        have hBs := germ_ends hB
        set s : P := germSrc (orderCx P).src (orderCx P).tgt eb with hs
        set t : P := germTgt (orderCx P).src (orderCx P).tgt eb with ht
        have hγs : IsPath (orderCx P).src (orderCx P).tgt (γ s) j0 (retrVert A j0 s) :=
          isPath_gamma hJA hJmk hγpath hγnil hBs.1
        have hγt : IsPath (orderCx P).src (orderCx P).tgt (γ t) j0 (retrVert A j0 t) :=
          isPath_gamma hJA hJmk hγpath hγnil hBs.2
        have hsimp : germSrc (orderCx P).src (orderCx P).tgt (revGerm eb) = t := by
          simpa only [ht] using germSrc_revGerm (X := orderCx P) eb
        have hsimp' : germTgt (orderCx P).src (orderCx P).tgt (revGerm eb) = s := by
          simpa only [hs] using germTgt_revGerm (X := orderCx P) eb
        rw [hsimp, hsimp']
        -- `(γ s ⁻¹ γ t)(γ t ⁻¹ γ s) ≃ []`
        have hcancelt : HtpyIn A j0 j0 (γ t ++ revPath (γ t)) [] :=
          htpyIn_append_revPath hγt (hγA t)
        have hmid : HtpyIn A (retrVert A j0 s) (retrVert A j0 s)
            (revPath (γ s) ++ (γ t ++ revPath (γ t)) ++ γ s)
            (revPath (γ s) ++ [] ++ γ s) :=
          hcancelt.congr_append (isPath_revPath hγs) hγs (pathIn_revPath (hγA s)) (hγA s)
        have hrw : (revPath (γ s) ++ γ t) ++ (revPath (γ t) ++ γ s) =
            revPath (γ s) ++ (γ t ++ revPath (γ t)) ++ γ s := by
          simp [List.append_assoc]
        rw [hrw]
        refine hmid.trans ?_
        simpa using htpyIn_revPath_append hγs (hγA s)
    have hcs' : c = germSrc (orderCx P).src (orderCx P).tgt eb := hcs
    subst hcs'
    have hglue : HtpyIn A (retrVert A j0 a) (retrVert A j0 b)
        (retrPath A γ p' ++ (retrGerm A γ eb ++ retrGerm A γ (revGerm eb)) ++ retrPath A γ q')
        (retrPath A γ p' ++ [] ++ retrPath A γ q') := by
      refine hkey.congr_append hPp' ?_ (pathIn_retrPath hγA p') (pathIn_retrPath hγA q')
      rw [hrevTgt] at hPq'
      exact hPq'
    have hrwl : retrPath A γ (p' ++ eb :: revGerm eb :: q') =
        retrPath A γ p' ++ (retrGerm A γ eb ++ retrGerm A γ (revGerm eb)) ++ retrPath A γ q' := by
      rw [retrPath_append]
      simp [retrPath, List.append_assoc]
    rw [hrwl, retrPath_append]
    simpa using hglue
  · -- a two-cell
    subst hlEq
    subst hl'Eq
    have hfront : PathIn U (p' ++ (orderCx P).att t) := pathIn_of_append_left hUl
    have hUp' : PathIn U p' := pathIn_of_append_left hfront
    have hUatt : PathIn U ((orderCx P).att t) := pathIn_of_append_right hfront
    have hUq' : PathIn U q' := pathIn_of_append_right hUl
    obtain ⟨c, hfrontPath, hq'⟩ := isPath_append_iff.mp hpl
    obtain ⟨d, hpc, hatt⟩ := isPath_append_iff.mp hfrontPath
    have hbase : d = t.1.1 := hatt.1
    have hbase' : c = t.1.1 := by
      obtain ⟨-, h2⟩ := hatt
      obtain ⟨-, h2'⟩ := h2
      obtain ⟨-, h3⟩ := h2'
      exact h3.symm
    subst hbase
    subst hbase'
    have hPp' : IsPath (orderCx P).src (orderCx P).tgt (retrPath A γ p')
        (retrVert A j0 a) (retrVert A j0 t.1.1) :=
      isPath_retrPath hJA hJmk hγpath hγnil hmix p' hpc hUp'
    have hPq' : IsPath (orderCx P).src (orderCx P).tgt (retrPath A γ q')
        (retrVert A j0 t.1.1) (retrVert A j0 b) :=
      isPath_retrPath hJA hJmk hγpath hγnil hmix q' hq' hUq'
    have hv1 := hUatt ((⟨(t.1.1, t.1.2.1), t.2.1⟩ : OrdEdge P), true) (by simp [orderCx])
    have hv2 := hUatt ((⟨(t.1.2.1, t.1.2.2), t.2.2⟩ : OrdEdge P), true) (by simp [orderCx])
    have hUx : U t.1.1 := hv1.1
    have hUy : U t.1.2.1 := hv1.2
    have hUz : U t.1.2.2 := hv2.2
    have hkey : HtpyIn A (retrVert A j0 t.1.1) (retrVert A j0 t.1.1)
        (retrPath A γ ((orderCx P).att t)) [] := by
      by_cases hallA : A t.1.1 ∧ A t.1.2.1 ∧ A t.1.2.2
      · -- the two-cell lies in `A`
        have hattA : PathIn A ((orderCx P).att t) := by
          intro e he
          have hmem : e = ((⟨(t.1.1, t.1.2.1), t.2.1⟩ : OrdEdge P), true) ∨
              e = ((⟨(t.1.2.1, t.1.2.2), t.2.2⟩ : OrdEdge P), true) ∨
              e = ((⟨(t.1.1, t.1.2.2), le_trans t.2.1 t.2.2⟩ : OrdEdge P), false) := by
            simpa [orderCx, or_assoc] using he
          rcases hmem with rfl | rfl | rfl
          · exact ⟨hallA.1, hallA.2.1⟩
          · exact ⟨hallA.2.1, hallA.2.2⟩
          · exact ⟨hallA.1, hallA.2.2⟩
        rw [retrPath_eq_self hattA, retrVert_of_mem hallA.1]
        refine HtpyIn.of_step ⟨⟨(orderCx P).att_isLoop t, rfl,
          Or.inr ⟨[], [], t, by simp, rfl⟩⟩, hattA, pathIn_nil A⟩
      · -- the two-cell lies in `B`
        have hallB : B t.1.1 ∧ B t.1.2.1 ∧ B t.1.2.2 := by
          by_cases hx : A t.1.1
          · by_cases hy : A t.1.2.1
            · have hz : ¬ A t.1.2.2 := fun hz => hallA ⟨hx, hy, hz⟩
              have h1 := hmix t.1.2.1 t.1.2.2 t.2.2 hUy hUz
              have h2 := hmix t.1.1 t.1.2.2 (le_trans t.2.1 t.2.2) hUx hUz
              rcases h1 with h1 | h1
              · exact absurd h1.2 hz
              · rcases h2 with h2 | h2
                · exact absurd h2.2 hz
                · exact ⟨h2.1, h1.1, h1.2⟩
            · have h1 := hmix t.1.1 t.1.2.1 t.2.1 hUx hUy
              have h2 := hmix t.1.2.1 t.1.2.2 t.2.2 hUy hUz
              rcases h1 with h1 | h1
              · exact absurd h1.2 hy
              · rcases h2 with h2 | h2
                · exact absurd h2.1 hy
                · exact ⟨h1.1, h1.2, h2.2⟩
          · have h1 := hmix t.1.1 t.1.2.1 t.2.1 hUx hUy
            have h2 := hmix t.1.1 t.1.2.2 (le_trans t.2.1 t.2.2) hUx hUz
            rcases h1 with h1 | h1
            · exact absurd h1.1 hx
            · rcases h2 with h2 | h2
              · exact absurd h2.1 hx
              · exact ⟨h1.1, h1.2, h2.2⟩
        have hattB : PathIn B ((orderCx P).att t) := by
          intro e he
          have hmem : e = ((⟨(t.1.1, t.1.2.1), t.2.1⟩ : OrdEdge P), true) ∨
              e = ((⟨(t.1.2.1, t.1.2.2), t.2.2⟩ : OrdEdge P), true) ∨
              e = ((⟨(t.1.1, t.1.2.2), le_trans t.2.1 t.2.2⟩ : OrdEdge P), false) := by
            simpa [orderCx, or_assoc] using he
          rcases hmem with rfl | rfl | rfl
          · exact ⟨hallB.1, hallB.2.1⟩
          · exact ⟨hallB.2.1, hallB.2.2⟩
          · exact ⟨hallB.1, hallB.2.2⟩
        have htel := htpyIn_retrPath_of_pathIn_B (A := A) (γ := γ) hJA hJmk hγpath hγin hγnil hJsc hj0 ((orderCx P).att t) ((orderCx P).att_isLoop t) hattB hallB.1 hallB.1
        refine htel.trans ?_
        have hγx : IsPath (orderCx P).src (orderCx P).tgt (γ t.1.1) j0
            (retrVert A j0 t.1.1) := isPath_gamma hJA hJmk hγpath hγnil hallB.1
        exact htpyIn_revPath_append hγx (hγA t.1.1)
    have hglue : HtpyIn A (retrVert A j0 a) (retrVert A j0 b)
        (retrPath A γ p' ++ retrPath A γ ((orderCx P).att t) ++ retrPath A γ q')
        (retrPath A γ p' ++ [] ++ retrPath A γ q') :=
      hkey.congr_append hPp' hPq' (pathIn_retrPath hγA p') (pathIn_retrPath hγA q')
    rw [retrPath_append, retrPath_append, retrPath_append]
    simpa using hglue

include hJA hJmk hγpath hγin hγnil in
/-- The retraction respects homotopies inside `U`. -/
theorem htpyIn_retrPath_of_htpyIn
    (hmix : ∀ a b : P, a ≤ b → U a → U b → (A a ∧ A b) ∨ (B a ∧ B b))
    (hJsc : SimplyConnectedIn J) (hj0 : J j0) {a b : P}
    {p q : List ((orderCx P).E × Bool)} (h : HtpyIn U a b p q) :
    HtpyIn A (retrVert A j0 a) (retrVert A j0 b) (retrPath A γ p) (retrPath A γ q) := by
  induction h with
  | refl => exact HtpyIn.refl _
  | tail _ hstep ih =>
      refine ih.trans ?_
      rcases hstep with hs | hs
      · exact htpyIn_retrPath_of_stepIn hJA hJmk hγpath hγin hγnil hmix hJsc hj0 hs
      · exact (htpyIn_retrPath_of_stepIn hJA hJmk hγpath hγin hγnil hmix hJsc hj0 hs).symm

end Gluing

/-- **The gluing step for injectivity on path classes.**  If `U = A ∪ B`, no comparability inside
`U` is mixed, and the intersection `J = A ∩ B` is nonempty, connected and simply connected, then
a loop inside `A` which is null-homotopic inside `U` is null-homotopic inside `A`.  Nothing is
assumed about `B`. -/
theorem injIn_union_of_unmixed {A B U J : P → Prop}
    (hmix : ∀ a b : P, a ≤ b → U a → U b → (A a ∧ A b) ∨ (B a ∧ B b))
    (hJdef : ∀ x, J x ↔ (A x ∧ B x))
    (hJconn : ConnectedIn J) (hJsc : SimplyConnectedIn J)
    {j0 : P} (hj0 : J j0) :
    InjIn U A := by
  classical
  have hJA : ∀ x, J x → A x := fun x h => ((hJdef x).1 h).1
  have hJmk : ∀ x, A x → B x → J x := fun x h h' => (hJdef x).2 ⟨h, h'⟩
  -- choose the paths `γ`
  have hex : ∀ u : P, ∃ g : List ((orderCx P).E × Bool),
      (J u → IsPath (orderCx P).src (orderCx P).tgt g j0 u) ∧ PathIn J g ∧ (¬ J u → g = []) := by
    intro u
    by_cases hu : J u
    · obtain ⟨g, hg, hgin⟩ := hJconn j0 u hj0 hu
      exact ⟨g, fun _ => hg, hgin, fun h => absurd hu h⟩
    · exact ⟨[], fun h => absurd h hu, pathIn_nil J, fun _ => rfl⟩
  choose γ hγpath hγin hγnil using hex
  intro v l hv hp hl hnull
  have h := htpyIn_retrPath_of_htpyIn (A := A) (B := B) (J := J) (γ := γ) hJA hJmk
    hγpath hγin hγnil hmix hJsc hj0 hnull
  rw [retrPath_eq_self hl, retrVert_of_mem hv] at h
  simpa only [retrPath_nil (P := P)] using h

/-! ### The initial step: a monotone retraction -/

/-- A monotone map that fixes the vertices of `B` returns a path of `B` unchanged. -/
theorem mapPath_liftPathIn_of_fix {C B : P → Prop} (f : {x : P // C x} → P) (hf : Monotone f)
    (hfix : ∀ z : {x : P // C x}, B z.1 → f z = z.1) :
    ∀ (l : List ((orderCx P).E × Bool)) (hl : PathIn C l), PathIn B l →
      mapPath (orderCxMap f hf) (liftPathIn l hl) = l
  | [], _, _ => rfl
  | e :: t, hl, hB => by
      have hrest : mapPath (orderCxMap f hf) (liftPathIn t (pathIn_of_cons hl).2) = t :=
        mapPath_liftPathIn_of_fix f hf hfix t (pathIn_of_cons hl).2 (pathIn_of_cons hB).2
      obtain ⟨he1, he2⟩ := (pathIn_of_cons hB).1
      obtain ⟨hc1, hc2⟩ := (pathIn_of_cons hl).1
      simp only [liftPathIn, mapPath, List.map_cons, List.cons.injEq]
      constructor
      · refine Prod.ext ?_ rfl
        refine Subtype.ext ?_
        refine Prod.ext ?_ ?_
        · exact hfix ⟨e.1.1.1, hc1⟩ he1
        · exact hfix ⟨e.1.1.2, hc2⟩ he2
      · exact hrest

/-- **A monotone retraction is injective on path classes.**  If the subposet `C` retracts
monotonically onto a smaller subposet `B`, fixing `B` pointwise, then a loop inside `B` that is
null-homotopic inside `C` is null-homotopic inside `B`. -/
theorem injIn_of_monotone_retraction {C B : P → Prop} (hBC : ∀ x, B x → C x)
    (f : {x : P // C x} → P) (hf : Monotone f) (hfB : ∀ z, B (f z))
    (hfix : ∀ z : {x : P // C x}, B z.1 → f z = z.1) :
    InjIn C B := by
  intro v l hv hp hl hnull
  have hvC : C v := hBC v hv
  have hlC : PathIn C l := pathIn_mono hBC hl
  have hlift : Htpy (orderCx {x : P // C x}) ⟨v, hvC⟩ ⟨v, hvC⟩ (liftPathIn l hlC)
      (liftPathIn ([] : List ((orderCx P).E × Bool)) (pathIn_nil C)) :=
    htpy_lift_of_htpyIn hnull hvC hvC hlC (pathIn_nil C)
  have hpush := htpyIn_mapPath (C := B) f hf hfB hlift
  rw [mapPath_liftPathIn_of_fix f hf hfix l hlC hl, hfix ⟨v, hvC⟩ hv] at hpush
  simpa [mapPath, liftPathIn] using hpush

/-! ### Passing to an increasing exhaustion -/

/-- **Finiteness of null-homotopies.**  A homotopy of the ambient complex only uses finitely many
cells, so it takes place inside one member of an increasing exhaustion. -/
theorem exists_htpyIn_of_htpy {D : ℕ → P → Prop} (hmono : ∀ m n, m ≤ n → ∀ x, D m x → D n x)
    (hcov : ∀ x : P, ∃ n, D n x) {a b : P} {p q : List ((orderCx P).E × Bool)}
    (h : Htpy (orderCx P) a b p q) : ∃ n, HtpyIn (D n) a b p q := by
  have hpath : ∀ l : List ((orderCx P).E × Bool), ∃ n, PathIn (D n) l := by
    intro l
    induction l with
    | nil => exact ⟨0, pathIn_nil _⟩
    | cons e t ih =>
        obtain ⟨n, hn⟩ := ih
        obtain ⟨n1, hn1⟩ := hcov e.1.1.1
        obtain ⟨n2, hn2⟩ := hcov e.1.1.2
        refine ⟨max n (max n1 n2), pathIn_cons ⟨?_, ?_⟩ ?_⟩
        · exact hmono n1 _ (le_trans (le_max_left n1 n2) (le_max_right n _)) _ hn1
        · exact hmono n2 _ (le_trans (le_max_right n1 n2) (le_max_right n _)) _ hn2
        · exact pathIn_mono (hmono n _ (le_max_left _ _)) hn
  induction h with
  | refl => exact ⟨0, Relation.ReflTransGen.refl⟩
  | @tail u v _ hstep ih =>
      obtain ⟨n, hn⟩ := ih
      obtain ⟨m1, hm1⟩ := hpath u
      obtain ⟨m2, hm2⟩ := hpath v
      refine ⟨max n (max m1 m2), ?_⟩
      refine (HtpyIn.mono (hmono n _ (le_max_left _ _)) hn).trans ?_
      have hu : PathIn (D (max n (max m1 m2))) u :=
        pathIn_mono (hmono m1 _ (le_trans (le_max_left m1 m2) (le_max_right n _))) hm1
      have hv : PathIn (D (max n (max m1 m2))) v :=
        pathIn_mono (hmono m2 _ (le_trans (le_max_right m1 m2) (le_max_right n _))) hm2
      rcases hstep with hs | hs
      · exact HtpyIn.of_step ⟨hs, hu, hv⟩
      · exact (HtpyIn.of_step ⟨hs, hv, hu⟩).symm

end Comb
end FiniteChains
