module

public import RequestProject.OrderNerveRealizationSubcomplex

@[expose] public section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb
open CategoryTheory Simplicial
open scoped Classical

/-- Affine interpolation is natural under every actual realized monotone map. -/
theorem orderNerveAffineRealization_natural {P Q : Type} [PartialOrder P] [PartialOrder Q]
    (f : P → Q) (hf : Monotone f) (v : Q → ℝ) (x : orderNerveRealization P) :
    orderNerveAffineRealization v (orderNerveRealizationMap f hf x) =
      orderNerveAffineRealization (v ∘ f) x := by
  obtain ⟨n, s, z, hx⟩ := orderNerveRealizationSimplex_jointly_surjective P x
  subst x
  have hn := congrArg (fun k => k z) (orderNerveRealizationSimplex_natural f hf s)
  change orderNerveRealizationMap f hf (orderNerveRealizationSimplex P s z) =
    orderNerveRealizationSimplex Q ((nerveMap hf.functor).app _ s) z at hn
  rw [hn]
  have hq := congrArg (fun k => k z)
    (orderNerveAffineRealization_simplex v ((nerveMap hf.functor).app _ s))
  have hp := congrArg (fun k => k z) (orderNerveAffineRealization_simplex (v ∘ f) s)
  change orderNerveAffineRealization v
      (orderNerveRealizationSimplex Q ((nerveMap hf.functor).app _ s) z) =
    orderNerveAffineSimplex v ((nerveMap hf.functor).app _ s) z at hq
  change orderNerveAffineRealization (v ∘ f) (orderNerveRealizationSimplex P s z) =
    orderNerveAffineSimplex (v ∘ f) s z at hp
  rw [hq, hp]
  rfl

/-- An injective monotone map preserves each actual barycentric coordinate at its image vertex. -/
theorem orderNerveRealizationCoordinates_map_injective {P Q : Type}
    [PartialOrder P] [PartialOrder Q] (f : P → Q) (hf : Monotone f)
    (hi : Function.Injective f) (x : orderNerveRealization P) (p : P) :
    orderNerveRealizationCoordinates Q (orderNerveRealizationMap f hf x) (f p) =
      orderNerveRealizationCoordinates P x p := by
  change orderNerveAffineRealization (fun q => if q = f p then 1 else 0)
    (orderNerveRealizationMap f hf x) = _
  rw [orderNerveAffineRealization_natural]
  have hv : ((fun q : Q => if q = f p then (1 : ℝ) else 0) ∘ f) =
      (fun q : P => if q = p then 1 else 0) := by
    funext q
    simp only [Function.comp_apply, hi.eq_iff]
  rw [hv]
  rfl

/-- Injective monotone maps induce injective maps of the actual geometric realizations. -/
theorem orderNerveRealizationMap_injective {P Q : Type} [PartialOrder P] [PartialOrder Q]
    (f : P → Q) (hf : Monotone f) (hi : Function.Injective f) :
    Function.Injective (orderNerveRealizationMap f hf) := by
  intro x y h
  apply orderNerveRealizationCoordinates_injective P
  funext p
  have hc := congrArg (fun z => orderNerveRealizationCoordinates Q z (f p)) h
  simpa only [orderNerveRealizationCoordinates_map_injective f hf hi] using hc

/-- Vertices outside the image of a monotone map have zero coordinate in its realization. -/
theorem orderNerveRealizationCoordinates_map_outside {P Q : Type}
    [PartialOrder P] [PartialOrder Q] (f : P → Q) (hf : Monotone f)
    (x : orderNerveRealization P) (q : Q) (hq : q ∉ Set.range f) :
    orderNerveRealizationCoordinates Q (orderNerveRealizationMap f hf x) q = 0 := by
  change orderNerveAffineRealization (fun r => if r = q then 1 else 0)
    (orderNerveRealizationMap f hf x) = 0
  rw [orderNerveAffineRealization_natural]
  obtain ⟨n, s, z, hx⟩ := orderNerveRealizationSimplex_jointly_surjective P x
  subst x
  have he := congrArg (fun k => k z)
    (orderNerveAffineRealization_simplex ((fun r : Q => if r = q then (1 : ℝ) else 0) ∘ f) s)
  change orderNerveAffineRealization _ (orderNerveRealizationSimplex P s z) =
    orderNerveAffineSimplex _ s z at he
  rw [he]
  have hn : ∀ p : P, f p ≠ q := by
    intro p hp
    exact hq ⟨p, hp⟩
  simp [orderNerveAffineSimplex, hn]

/-- The image of a realized monotone map lies in the genuine CW subcomplex
supported on its image vertices. -/
theorem orderNerveRealizationMap_mem_subcomplex {P Q : Type}
    [PartialOrder P] [PartialOrder Q] (f : P → Q) (hf : Monotone f)
    (x : orderNerveRealization P) :
    orderNerveRealizationMap f hf x ∈
      (orderNerveRealizationSubcomplex Q (Set.range f) : Set (orderNerveRealization Q)) := by
  intro q hq
  exact orderNerveRealizationCoordinates_map_outside f hf x q hq

/-- Lift a simplex whose vertices lie in a subset to the induced subposet. -/
def orderNerveSimplexSubtype {P : Type} [PartialOrder P] (A : Set P)
    {n : SimplexCategory} (s : (nerve P).obj (Opposite.op n))
    (hs : ∀ i, s.obj i ∈ A) : (nerve A).obj (Opposite.op n) where
  obj i := ⟨s.obj i, hs i⟩
  map h := homOfLE (leOfHom (s.map h))

/-- Realizing the induced subposet has exactly the supported CW subcomplex as its image. -/
theorem orderNerveRealizationSubtype_range {P : Type} [PartialOrder P] (A : Set P) :
    Set.range (orderNerveRealizationMap (Subtype.val : A → P)
      (fun _ _ h => h)) =
      (orderNerveRealizationSubcomplex P A : Set (orderNerveRealization P)) := by
  apply Set.Subset.antisymm
  · rintro x ⟨y, rfl⟩
    have h := orderNerveRealizationMap_mem_subcomplex (Subtype.val : A → P)
      (fun _ _ h => h) y
    simpa only [Subtype.range_coe_subtype, Set.setOf_mem_eq] using h
  · intro x hx
    change x ∈ orderNerveRealizationSupported P A at hx
    rw [← orderNerveRealizationSupported_union P A] at hx
    obtain ⟨n, hx⟩ := Set.mem_iUnion.mp hx
    obtain ⟨s, hx⟩ := Set.mem_iUnion.mp hx
    rw [orderNerveCharacteristicMap_openCell] at hx
    obtain ⟨z, _, hz⟩ := hx
    let t := orderNerveSimplexSubtype A s.val.val s.property
    refine ⟨orderNerveRealizationSimplex A t z, ?_⟩
    have ht : (nerveMap (show Monotone (Subtype.val : A → P) from
        fun _ _ h => h).functor).app _ t = s.val.val := by
      exact CategoryTheory.Functor.ext (fun _ => rfl)
    have he := congrArg (fun k => k z)
      (orderNerveRealizationSimplex_natural (Subtype.val : A → P)
        (fun _ _ h => h) t)
    change orderNerveRealizationMap _ _ (orderNerveRealizationSimplex A t z) =
      orderNerveRealizationSimplex P ((nerveMap _).app _ t) z at he
    rw [ht] at he
    exact he.trans hz

/-- The induced-subposet realization maps bijectively onto the supported carrier. -/
theorem orderNerveRealizationSubtype_bijective {P : Type} [PartialOrder P] (A : Set P) :
    Function.Bijective (fun y : orderNerveRealization A =>
      (⟨orderNerveRealizationMap (Subtype.val : A → P) (fun _ _ h => h) y,
        by
          have h := orderNerveRealizationMap_mem_subcomplex (Subtype.val : A → P)
            (fun _ _ h => h) y
          simpa only [Subtype.range_coe_subtype, Set.setOf_mem_eq] using h⟩ :
        (orderNerveRealizationSubcomplex P A : Set (orderNerveRealization P)))) := by
  constructor
  · intro x y h
    exact orderNerveRealizationMap_injective (Subtype.val : A → P)
      (fun _ _ h => h) Subtype.val_injective (congrArg Subtype.val h)
  · intro x
    have hx : x.val ∈ Set.range (orderNerveRealizationMap (Subtype.val : A → P)
        (fun _ _ h => h)) := by
      rw [orderNerveRealizationSubtype_range]
      exact x.property
    obtain ⟨y, hy⟩ := hx
    exact ⟨y, Subtype.ext hy⟩

end FiniteChains.Comb
