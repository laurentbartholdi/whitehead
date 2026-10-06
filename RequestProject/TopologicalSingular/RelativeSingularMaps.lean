module

/- Adapted from the local 2026-09-11 Lean audit; see PROVENANCE.json. -/

public import RequestProject.TopologicalSingular.RelativeSingularChains

@[expose] public section

/-! # Functorial relative singular chains for maps of topological pairs -/


set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.TopologicalSingular

open Set Topology

universe u v w
variable {X : Type u} {Y : Type v} {Z : Type w}
variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

theorem single_mem_subChains (A : Set X) (n : ℕ) (σ : Simplex X n) (r : ℤ)
    (hσ : ∀ z, σ z ∈ A) : Finsupp.single σ r ∈ subChains A n := by
  let τ : Simplex A n := ⟨fun z => ⟨σ z, hσ z⟩, σ.continuous.subtype_mk _⟩
  refine ⟨Finsupp.single τ r, ?_⟩
  rw [map_single]
  rfl

def pairRestriction (f : C(X, Y)) (A : Set X) (B : Set Y) (h : MapsTo f A B) : C(A, B) :=
  ⟨fun a => ⟨f a.val, h a.property⟩,
    (f.continuous.comp continuous_subtype_val).subtype_mk _⟩

theorem map_mem_subChains (f : C(X, Y)) (A : Set X) (B : Set Y) (h : MapsTo f A B)
    (n : ℕ) {c : Chain X n} (hc : c ∈ subChains A n) : map f n c ∈ subChains B n := by
  obtain ⟨b, rfl⟩ := hc
  refine ⟨map (pairRestriction f A B h) n b, ?_⟩
  have he : (inclusion B).comp (pairRestriction f A B h) = f.comp (inclusion A) := rfl
  rw [← LinearMap.comp_apply, ← map_comp, he, map_comp, LinearMap.comp_apply]

noncomputable def relativeMap (f : C(X, Y)) (A : Set X) (B : Set Y) (h : MapsTo f A B) (n : ℕ) :
    RelativeChain A n →ₗ[ℤ] RelativeChain B n :=
  (subChains A n).mapQ (subChains B n) (map f n) (fun _ hc => map_mem_subChains f A B h n hc)

theorem relativeMap_projection (f : C(X, Y)) (A : Set X) (B : Set Y) (h : MapsTo f A B)
    (n : ℕ) (c : Chain X n) :
    relativeMap f A B h n (relativeProjection A n c) = relativeProjection B n (map f n c) := rfl

theorem relativeMap_boundary (f : C(X, Y)) (A : Set X) (B : Set Y) (h : MapsTo f A B)
    (n : ℕ) (c : RelativeChain A (n + 1)) :
    relativeMap f A B h n (relativeBoundary A n c) =
      relativeBoundary B n (relativeMap f A B h (n + 1) c) := by
  obtain ⟨b, rfl⟩ := relativeProjection_surjective A (n + 1) c
  simp only [relativeBoundary_projection, relativeMap_projection, map_boundary]

theorem relativeMap_id (A : Set X) (n : ℕ) :
    relativeMap (ContinuousMap.id X) A A (fun _ h => h) n = LinearMap.id := by
  apply LinearMap.ext
  intro c
  obtain ⟨b, rfl⟩ := relativeProjection_surjective A n c
  simp only [relativeMap_projection, map_id, LinearMap.id_apply]

theorem relativeMap_comp (f : C(X, Y)) (g : C(Y, Z)) (A : Set X) (B : Set Y) (C : Set Z)
    (hf : MapsTo f A B) (hg : MapsTo g B C) (n : ℕ) :
    relativeMap (g.comp f) A C (hg.comp hf) n =
      (relativeMap g B C hg n).comp (relativeMap f A B hf n) := by
  apply LinearMap.ext
  intro c
  obtain ⟨b, rfl⟩ := relativeProjection_surjective A n c
  simp only [relativeMap_projection, LinearMap.comp_apply, map_comp]

end FiniteChains.TopologicalSingular
