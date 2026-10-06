import RequestProject.FreePaddingNaturality

/-! Composition and relabelling for literal supported presentation maps.
These identities are on the actual group-ring coefficients, not only on
homology classes. Awaiting the final Lean verification phase. -/

noncomputable section
open scoped Classical

namespace FiniteChains.PresInclusionFS

section Square
variable {A B D E J K L M : Type}
  [DecidableEq A] [DecidableEq B] [DecidableEq D] [DecidableEq E]
  (ρ : J → FreeGroup A) (τ : K → FreeGroup B)
  (σ : L → FreeGroup D) (υ : M → FreeGroup E)
  (g : A → B) (f : J → K) (hg : Function.Injective g) (hf : Function.Injective f)
  (hρτ : ∀ j, τ (f j) = FreeGroup.map g (ρ j))
  (a : A → D) (c : J → L) (ha : Function.Injective a) (hc : Function.Injective c)
  (hρσ : ∀ j, σ (c j) = FreeGroup.map a (ρ j))
  (b : B → E) (d : K → M) (hb : Function.Injective b) (hd : Function.Injective d)
  (hτυ : ∀ k, υ (d k) = FreeGroup.map b (τ k))
  (k : D → E) (l : L → M) (hk : Function.Injective k) (hl : Function.Injective l)
  (hσυ : ∀ z, υ (l z) = FreeGroup.map k (σ z))
  (hgen : ∀ x, k (a x) = b (g x)) (hcell : ∀ j, l (c j) = d (f j))

include hgen in
omit [DecidableEq A] [DecidableEq B] [DecidableEq D] [DecidableEq E] in
theorem square_group :
    (groupHom σ υ k l hσυ).comp (groupHom ρ σ a c hρσ) =
    (groupHom τ υ b d hτυ).comp (groupHom ρ τ g f hρτ) := by
  apply MonoidHom.ext
  intro z
  induction z using QuotientGroup.induction_on with
  | H w =>
      change QuotientGroup.mk (FreeGroup.map k (FreeGroup.map a w)) =
        QuotientGroup.mk (FreeGroup.map b (FreeGroup.map g w))
      have hm : (FreeGroup.map k).comp (FreeGroup.map a) =
          (FreeGroup.map b).comp (FreeGroup.map g) := by
        apply FreeGroup.ext_hom
        intro x
        simp only [MonoidHom.comp_apply, FreeGroup.map.of]
        exact congrArg FreeGroup.of (hgen x)
      exact congrArg (fun h : FreeGroup A →* FreeGroup E =>
        (QuotientGroup.mk (h w) : PresGroup υ)) hm

include hgen hcell in
theorem square_cells (x : J →₀ MonoidAlgebra ℤ (PresGroup ρ)) :
    (mor σ υ k l hk hl hσυ).cells ((mor ρ σ a c ha hc hρσ).cells x) =
    (mor τ υ b d hb hd hτυ).cells ((mor ρ τ g f hg hf hρτ).cells x) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy =>
      rw [PresMorFS.cells_add, PresMorFS.cells_add, PresMorFS.cells_add,
        PresMorFS.cells_add, hx, hy]
  | single j r =>
      change cells σ υ k l hσυ (cells ρ σ a c hρσ (Finsupp.single j r)) =
        cells τ υ b d hτυ (cells ρ τ g f hρτ (Finsupp.single j r))
      rw [cells_single, cells_single, cells_single, cells_single, hcell j]
      congr 1
      change MonoidAlgebra.mapDomainRingHom ℤ (groupHom σ υ k l hσυ)
        (MonoidAlgebra.mapDomainRingHom ℤ (groupHom ρ σ a c hρσ) r) =
        MonoidAlgebra.mapDomainRingHom ℤ (groupHom τ υ b d hτυ)
          (MonoidAlgebra.mapDomainRingHom ℤ (groupHom ρ τ g f hρτ) r)
      rw [BlockMor.mapDomainRingHom_comp', BlockMor.mapDomainRingHom_comp',
        square_group ρ τ σ υ g f hρτ a c hρσ b d hτυ k l hσυ hgen]
end Square

section Relabel
variable {A B J K : Type} [DecidableEq A] [DecidableEq B]
  (ρ : J → FreeGroup A) (τ : K → FreeGroup B)
  (g : A ≃ B) (f : J ≃ K)
  (hrel : ∀ j, τ (f j) = FreeGroup.map g (ρ j))

include hrel in
omit [DecidableEq A] [DecidableEq B] in
theorem inverse_rel (k : K) :
    ρ (f.symm k) = FreeGroup.map g.symm (τ k) := by
  have hk : τ k = FreeGroup.map g (ρ (f.symm k)) := by
    simpa only [Equiv.apply_symm_apply] using hrel (f.symm k)
  rw [hk]
  have hm : (FreeGroup.map g.symm).comp (FreeGroup.map g) = MonoidHom.id _ := by
    apply FreeGroup.ext_hom
    intro x
    simp
  simpa using (congrArg (fun h : FreeGroup A →* FreeGroup A => h (ρ (f.symm k))) hm).symm

theorem relabel_cells_inverse (x : K →₀ MonoidAlgebra ℤ (PresGroup τ)) :
    (mor ρ τ g f g.injective f.injective hrel).cells
      ((mor τ ρ g.symm f.symm g.symm.injective f.symm.injective
        (inverse_rel ρ τ g f hrel)).cells x) = x := by
  have hm : (groupHom ρ τ g f hrel).comp
      (groupHom τ ρ g.symm f.symm (inverse_rel ρ τ g f hrel)) = MonoidHom.id _ := by
    apply MonoidHom.ext
    intro z
    induction z using QuotientGroup.induction_on with
    | H w =>
        change QuotientGroup.mk (FreeGroup.map g (FreeGroup.map g.symm w)) = QuotientGroup.mk w
        have hw : (FreeGroup.map g).comp (FreeGroup.map g.symm) = MonoidHom.id _ := by
          apply FreeGroup.ext_hom
          intro b
          simp
        exact congrArg (fun h : FreeGroup B →* FreeGroup B =>
          (QuotientGroup.mk (h w) : PresGroup τ)) hw
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => rw [PresMorFS.cells_add, PresMorFS.cells_add, hx, hy]
  | single j r =>
      change cells ρ τ g f hrel (cells τ ρ g.symm f.symm
        (inverse_rel ρ τ g f hrel) (Finsupp.single j r)) = _
      rw [cells_single, cells_single, Equiv.apply_symm_apply]
      congr 1
      change MonoidAlgebra.mapDomainRingHom ℤ (groupHom ρ τ g f hrel)
        (MonoidAlgebra.mapDomainRingHom ℤ
          (groupHom τ ρ g.symm f.symm (inverse_rel ρ τ g f hrel)) r) = r
      rw [BlockMor.mapDomainRingHom_comp', hm]
      simp

theorem relabel_generates : FSGenerates (mor ρ τ g f g.injective f.injective hrel) := by
  intro x hx
  let inv := mor τ ρ g.symm f.symm g.symm.injective f.symm.injective
    (inverse_rel ρ τ g f hrel)
  apply Submodule.subset_span
  exact ⟨inv.cells x, inv.cells_cycle x hx, (relabel_cells_inverse ρ τ g f hrel x).symm⟩
end Relabel

section PaddingRelabel
variable {A B J K : Type} [DecidableEq A] [DecidableEq B]
  (ρ : J → FreeGroup A) (τ : K → FreeGroup B)
  (g : A → B) (hg : Function.Injective g) (f : J ≃ K)
  (hrel : ∀ j, τ (f j) = FreeGroup.map g (ρ j))

theorem paddingRelabel_generates : FSGenerates (mor ρ τ g f hg f.injective hrel) := by
  let σ := FreePadding.rel ρ g
  have hσ : ∀ j, τ (f j) = FreeGroup.map (Equiv.refl B) (σ j) := by
    intro j
    simpa [σ, FreePadding.rel] using hrel j
  let pad := FreePadding.structuralMap ρ g hg
  let relabel := mor σ τ (Equiv.refl B) f (Equiv.refl B).injective f.injective hσ
  have hc : ∀ x, (mor ρ τ g f hg f.injective hrel).cells x = relabel.cells (pad.cells x) := by
    intro x
    induction x using Finsupp.induction_linear with
    | zero => simp
    | add x y hx hy => rw [PresMorFS.cells_add, PresMorFS.cells_add,
        PresMorFS.cells_add, hx, hy]
    | single j r =>
        change cells ρ τ g f hrel (Finsupp.single j r) =
          cells σ τ (Equiv.refl B) f hσ
            ((Finsupp.single j r).mapRange (FreePadding.coefficients ρ g) (map_zero _))
        rw [Finsupp.mapRange_single, cells_single, cells_single]
        congr 1
        have hh : groupHom ρ τ g f hrel =
            (groupHom σ τ (Equiv.refl B) f hσ).comp (FreePadding.groupHom ρ g) := by
          apply MonoidHom.ext
          intro z
          induction z using QuotientGroup.induction_on with
          | H w => change QuotientGroup.mk (FreeGroup.map g w) =
              QuotientGroup.mk (FreeGroup.map (Equiv.refl B) (FreeGroup.map g w)); simp
        change MonoidAlgebra.mapDomainRingHom ℤ (groupHom ρ τ g f hrel) r =
          MonoidAlgebra.mapDomainRingHom ℤ (groupHom σ τ (Equiv.refl B) f hσ)
            (MonoidAlgebra.mapDomainRingHom ℤ (FreePadding.groupHom ρ g) r)
        rw [BlockMor.mapDomainRingHom_comp', ← hh]
  have hgen := (relabel_generates σ τ (Equiv.refl B) f hσ).comp
    (FreePadding.structuralMap_generates ρ g hg)
  intro x hx
  have hs := hgen x hx
  apply Submodule.span_mono _ hs
  rintro z ⟨y, hy, rfl⟩
  exact ⟨y, hy, (hc y).symm⟩
end PaddingRelabel

end FiniteChains.PresInclusionFS
