import RequestProject.HomeomorphContinuousMap
import RequestProject.ExplicitRelativeAttachment
import RequestProject.BallHomotopyExtension

/-! Homotopy extension for the literal old subspace of an attachment.
Currying in the compact time coordinate proves joint continuity on the
quotient attachment even when infinitely many cells are adjoined. -/

noncomputable section

namespace FiniteChains.RelativeAttachment
open scoped unitInterval Topology Classical

universe u
variable {A D X : Type u} [TopologicalSpace A] [TopologicalSpace D] [TopologicalSpace X]

/-- The ordinary homotopy extension property, retaining both equations as
equalities of actual continuous maps. -/
def HasHomotopyExtension (i : A → D) : Prop :=
  ∀ (Z : Type u) [TopologicalSpace Z] (f : C(D, Z)) (H : C(I × A, Z)),
    (∀ a, H (0, a) = f (i a)) →
    ∃ G : C(I × D, Z), (∀ d, G (0, d) = f d) ∧
      ∀ t a, G (t, i a) = H (t, a)

theorem HasHomotopyExtension.homeomorph {A' D' : Type u}
    [TopologicalSpace A'] [TopologicalSpace D'] {i : A → D}
    (h : HasHomotopyExtension i) (e : A ≃ₜ A') (d : D ≃ₜ D')
    (j : A' → D') (hsq : ∀ a, j (e a) = d (i a)) : HasHomotopyExtension j := by
  intro Z _ f H h₀
  let f' : C(D, Z) := f.comp d.toContinuousMap
  let H' : C(I × A, Z) := H.comp
    ⟨fun ta => (ta.1, e ta.2), continuous_fst.prodMk (e.continuous.comp continuous_snd)⟩
  have h'₀ : ∀ a, H' (0, a) = f' (i a) := by
    intro a
    change H (0, e a) = f (d (i a))
    rw [h₀, hsq]
  obtain ⟨G, hG₀, hGA⟩ := h Z f' H' h'₀
  refine ⟨G.comp ⟨fun td => (td.1, d.symm td.2),
    continuous_fst.prodMk (d.symm.continuous.comp continuous_snd)⟩, ?_, ?_⟩
  · intro z
    change G (0, d.symm z) = f z
    rw [hG₀]
    exact congrArg f (d.apply_symm_apply z)
  · intro t a
    have hs : d.symm (j a) = i (e.symm a) := by
      apply d.injective
      rw [d.apply_symm_apply, ← hsq, e.apply_symm_apply]
    change G (t, d.symm (j a)) = H (t, a)
    rw [hs, hGA]
    exact congrArg (fun b => H (t, b)) (e.apply_symm_apply a)

/-- The boundary of a real normed unit ball has homotopy extension by the
explicit radial cylinder retraction. -/
theorem unitBoundary_hasHomotopyExtension (E : Type u)
    [NormedAddCommGroup E] [NormedSpace ℝ E] :
    HasHomotopyExtension (unitBoundaryInclusion E) := by
  intro Z _ f H h₀
  exact ⟨ballHomotopyExtension f H h₀,
    ballHomotopyExtension_zero f H h₀, ballHomotopyExtension_boundary f H h₀⟩

/-- Homotopy extension is preserved by adjoining the disks to any base.
The old points remain the literal `old` summand of `Space r i`. -/
theorem old_hasHomotopyExtension (r : A → X) (i : A → D)
    (hr : Continuous r) (hi : Function.Injective i) (hext : HasHomotopyExtension i) :
    HasHomotopyExtension (old r i) := by
  intro Z _ f H h₀
  let fD : C(D, Z) := f.comp ⟨cell r i, cell_continuous r i⟩
  let HA : C(I × A, Z) := H.comp
    ⟨fun ta => (ta.1, r ta.2), continuous_fst.prodMk (hr.comp continuous_snd)⟩
  have hA₀ : ∀ a, HA (0, a) = fD (i a) := by
    intro a
    change H (0, r a) = f (cell r i (i a))
    rw [h₀, cell_boundary r i hi]
  obtain ⟨G, hG₀, hGA⟩ := hext Z fD HA hA₀
  let HX : C(X, C(I, Z)) :=
    (H.comp ⟨Prod.swap, continuous_swap⟩).curry
  let GD : C(D, C(I, Z)) :=
    (G.comp ⟨Prod.swap, continuous_swap⟩).curry
  have hcompat : ∀ a, HX (r a) = GD (i a) := by
    intro a
    apply ContinuousMap.ext
    intro t
    exact (hGA t a).symm
  let F : C(Space r i, C(I, Z)) := desc r i HX GD hcompat
  let L : C(I × Space r i, Z) := F.uncurry.comp ⟨Prod.swap, continuous_swap⟩
  have hOld : ∀ t x, L (t, old r i x) = H (t, x) := by
    intro t x
    change desc r i HX GD hcompat (old r i x) t = H (t, x)
    rw [desc_old]
    rfl
  have hCell : ∀ t d, L (t, cell r i d) = G (t, d) := by
    intro t d
    change desc r i HX GD hcompat (cell r i d) t = G (t, d)
    rw [desc_cell]
    rfl
  refine ⟨L, ?_, hOld⟩
  intro z
  obtain ⟨w, rfl⟩ := quotientMap_surjective r i z
  cases w with
  | inl x => exact (hOld 0 x).trans (h₀ x)
  | inr d => exact (hCell 0 d).trans (hG₀ d)

/-- Extension is simultaneous over an arbitrary disjoint family. Every
point lies in one summand, so no local finiteness assumption is needed. -/
theorem sigma_hasHomotopyExtension {J : Type u} {A D : J → Type u}
    [∀ j, TopologicalSpace (A j)] [∀ j, TopologicalSpace (D j)]
    (i : ∀ j, A j → D j) (h : ∀ j, HasHomotopyExtension (i j)) :
    HasHomotopyExtension (fun a : Σ j, A j => ⟨a.1, i a.1 a.2⟩ : (Σ j, A j) → Σ j, D j) := by
  intro Z _ f H h₀
  have hex (j : J) : ∃ G : C(I × D j, Z),
      (∀ d, G (0, d) = f ⟨j, d⟩) ∧
      ∀ t a, G (t, i j a) = H (t, ⟨j, a⟩) := by
    exact h j Z (f.comp ⟨Sigma.mk j, continuous_sigmaMk⟩)
      (H.comp ⟨fun ta => (ta.1, ⟨j, ta.2⟩),
        continuous_fst.prodMk (continuous_sigmaMk.comp continuous_snd)⟩)
      (fun a => h₀ ⟨j, a⟩)
  choose G hG₀ hGA using hex
  let F : C((Σ j, D j), C(I, Z)) := {
    toFun := fun d => (G d.1).comp
      ⟨fun t => (t, d.2), continuous_id.prodMk continuous_const⟩
    continuous_toFun := by
      apply continuous_sigma
      intro j
      exact ((G j).comp ⟨Prod.swap, continuous_swap⟩).curry.continuous }
  let L : C(I × (Σ j, D j), Z) := F.uncurry.comp ⟨Prod.swap, continuous_swap⟩
  refine ⟨L, ?_, ?_⟩
  · rintro ⟨j, d⟩
    exact hG₀ j d
  · intro t ⟨j, a⟩
    exact hGA j t a

end FiniteChains.RelativeAttachment
