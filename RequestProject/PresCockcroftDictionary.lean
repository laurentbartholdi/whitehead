import RequestProject.PresUnivCoverIso
import RequestProject.Cockcroft
import RequestProject.CockcroftExtension

/-!
# The Cockcroft property: the topological definition and the Fox one agree

Two definitions of "Cockcroft" occur in this development.

* `FiniteChains.Comb.IsCockcroft X` — the topological one, used by the interface
  `FiniteChains.combData` of Theorem A: the Hurewicz map `π₂(X) → H₂(X)` vanishes, where
  `π₂(X)` is the module of two-cycles of the universal cover built from homotopy classes of
  edge paths and the Hurewicz map pushes such a cycle down to `X`.
* `FiniteChains.IsCockcroft ρ` — the one used throughout Section 3: every Fox cycle of the
  presentation has zero augmentation.

Using the identification of the two models of the universal cover
(`RequestProject/PresUnivCoverIso.lean`) this file proves that for the complex of a finite
presentation the two agree: `FiniteChains.Comb.isCockcroft_presComplex_iff`.
-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains
namespace Comb

open MonoidAlgebra

universe u

variable {α J : Type u} [Fintype α] [DecidableEq α] [Fintype J] [DecidableEq J]
variable (ρ : J → FreeGroup α)

omit [Fintype α] [DecidableEq α] in
/-- **The augmentation of the coordinates is the pushforward to the base.**  Summing the
coefficients of a cellular two-chain of the cover over a fibre is the same as augmenting its
coordinate vector. -/
theorem augQ_coords (v : ((FreeGroup α ⧸ relSub ρ) × J) →₀ ℤ) (j : J) :
    augQ (relSub ρ) (coords (relSub ρ) J v j) = Finsupp.mapDomain Prod.snd v j := by
  classical
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw =>
      rw [map_add, Finsupp.mapDomain_add]
      simp only [Finsupp.add_apply, Pi.add_apply, map_add] at *
      rw [hv, hw]
  | single qj n =>
      obtain ⟨q, j₀⟩ := qj
      rw [coords_single, Finsupp.mapDomain_single]
      by_cases h : j = j₀
      · subst h
        simp
      · rw [Pi.single_eq_of_ne h, Finsupp.single_apply, if_neg (Ne.symm h), map_zero]

omit [Fintype α] [Fintype J] [DecidableEq J] in
/-- The Hurewicz map read in the algebraic model of the universal cover: it forgets the deck
coordinate of a two-cell. -/
theorem hurewicz_presComplex (c : (uCover (presComplex ρ) PUnit.unit).F →₀ ℤ) :
    hurewicz (presComplex ρ) PUnit.unit c
      = Finsupp.mapDomain Prod.snd (chain2 (presUnivHom ρ) c) := by
  classical
  show Finsupp.mapDomain (univProj (presComplex ρ) PUnit.unit).onF c
    = Finsupp.mapDomain Prod.snd (Finsupp.mapDomain (uvFace ρ) c)
  rw [← Finsupp.mapDomain_comp]
  rfl

/-- **The two definitions of the Cockcroft property agree** for the complex of a finite
presentation: the Hurewicz map of `presComplex ρ` vanishes exactly when every Fox cycle of `ρ`
has zero augmentation. -/
theorem isCockcroft_presComplex_iff :
    IsCockcroft (presComplex ρ) ↔ _root_.FiniteChains.IsCockcroft ρ := by
  classical
  constructor
  · intro hc v hv j
    set w : ((FreeGroup α ⧸ relSub ρ) × J) →₀ ℤ := (coords (relSub ρ) J).symm v with hw
    have hcoords : coords (relSub ρ) J w = v := by
      rw [hw, LinearEquiv.apply_symm_apply]
    have hbdry : bdry2 (univCover ρ) w = 0 := by
      refine (univCover_bdry2_eq_zero_iff ρ w).2 ?_
      intro i
      rw [hcoords]
      exact hv i
    obtain ⟨c, hcw⟩ := chain2_presUnivHom_surjective ρ w
    have hmem : c ∈ Pi2 (presComplex ρ) PUnit.unit :=
      (mem_pi2_iff_bdry2_eq_zero ρ c).2 (by rw [hcw]; exact hbdry)
    have hzero := hc PUnit.unit c hmem
    rw [hurewicz_presComplex, hcw] at hzero
    have := augQ_coords ρ w j
    rw [hcoords, hzero] at this
    simpa using this
  · intro hc x₀ c hmem
    have hbdry : bdry2 (univCover ρ) (chain2 (presUnivHom ρ) c) = 0 :=
      (mem_pi2_iff_bdry2_eq_zero ρ c).1 hmem
    have hcyc : _root_.FiniteChains.IsFoxCycle ρ
        (coords (relSub ρ) J (chain2 (presUnivHom ρ) c)) :=
      (univCover_bdry2_eq_zero_iff ρ _).1 hbdry
    rw [hurewicz_presComplex]
    refine Finsupp.ext fun j => ?_
    rw [← augQ_coords ρ _ j]
    exact hc _ hcyc j

/-- **The characterization from the introduction of the paper, in purely topological terms.**
The presentation complex of `ρ` is Cockcroft — its Hurewicz map `π₂ → H₂` vanishes — if and
only if it admits a two-dimensional extension (a presentation containing its generators and
its two-cells, the old cells attached along the old words) whose inclusion is zero on `π₂`. -/
theorem isCockcroft_presComplex_iff_exists_zeroPi2_ext :
    IsCockcroft (presComplex ρ) ↔
      ∃ (β C : Type u) (_ : DecidableEq β) (σ : C → FreeGroup β) (f : α → β)
        (hf : Function.Injective f) (g : J → C) (_ : Function.Injective g)
        (hg : ∀ j, σ (g j) = FreeGroup.map f (ρ j)),
        ZeroPi2 (presInclHom f hf ρ σ g hg) := by
  classical
  constructor
  · intro hc
    have hfox : _root_.FiniteChains.IsCockcroft ρ := (isCockcroft_presComplex_iff ρ).1 hc
    have hg : ∀ j, capRel ρ (Sum.inl j) = FreeGroup.map id (ρ j) := fun j => by
      simp [capRel_inl]
    refine ⟨α, J ⊕ α, inferInstance, capRel ρ, id, Function.injective_id, Sum.inl,
      Sum.inl_injective, hg, ?_⟩
    exact (zeroPi2_presInclHom_iff ρ id Function.injective_id Sum.inl hg).2
      (cappedExt_zero_pi2_cellular hfox)
  · rintro ⟨β, C, _, σ, f, hf, g, hgi, hg, hz⟩
    refine (isCockcroft_presComplex_iff ρ).2 (isCockcroft_of_zeroPi2Ext ?_)
    exact
      { gen := β
        cell := C
        rel := σ
        genIncl := f
        genIncl_injective := hf
        cellIncl := g
        cellIncl_injective := hgi
        rel_incl := hg
        zero_pi2 := (zeroPi2_cellular_iff hgi (relSub_le_comap_ext ρ σ f g hg)).1
          ((zeroPi2_presInclHom_iff ρ f hf g hg).1 hz) }

end Comb
end FiniteChains
