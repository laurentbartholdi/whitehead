import RequestProject.PresentationInclusionFinsupp

/-! Free generator padding commutes with actual labelled inclusions. In
particular a zero map on supported two-cycles remains zero after putting
both presentations into a common ambient alphabet. Unverified source. -/

noncomputable section
open scoped Classical

namespace FiniteChains.FreePadding

variable {A B V J K : Type} [DecidableEq A] [DecidableEq B] [DecidableEq V]
  (ρ : J → FreeGroup A) (τ : K → FreeGroup B)
  (g : A → B) (f : J → K) (hg : Function.Injective g) (hf : Function.Injective f)
  (hrel : ∀ j, τ (f j) = FreeGroup.map g (ρ j))
  (a : A → V) (b : B → V) (ha : Function.Injective a) (hb : Function.Injective b)
  (hab : ∀ x, a x = b (g x))

include hrel hab in
omit [DecidableEq A] [DecidableEq B] [DecidableEq V] in
theorem padded_rel (j : J) :
    rel τ b (f j) = FreeGroup.map id (rel ρ a j) := by
  change FreeGroup.map b (τ (f j)) = FreeGroup.map id (FreeGroup.map a (ρ j))
  rw [hrel j]
  have hm : (FreeGroup.map b).comp (FreeGroup.map g) = FreeGroup.map a := by
    apply FreeGroup.ext_hom
    intro x
    simp only [MonoidHom.comp_apply, FreeGroup.map.of]
    exact congrArg FreeGroup.of (hab x).symm
  simpa using congrArg (fun h : FreeGroup A →* FreeGroup V => h (ρ j)) hm

def paddedInclusion : PresMorFS (rel ρ a) (rel τ b) :=
  PresInclusionFS.mor _ _ id f Function.injective_id hf
    (padded_rel ρ τ g f hrel a b hab)

theorem padding_group_square :
    (paddedInclusion ρ τ g f hf hrel a b hab).hom.comp
      (structuralMap ρ a ha).hom =
    (structuralMap τ b hb).hom.comp (PresInclusionFS.mor ρ τ g f hg hf hrel).hom := by
  apply MonoidHom.ext
  intro z
  induction z using QuotientGroup.induction_on with
  | H w =>
      change QuotientGroup.mk (FreeGroup.map id (FreeGroup.map a w)) =
        QuotientGroup.mk (FreeGroup.map b (FreeGroup.map g w))
      have hm : FreeGroup.map a = (FreeGroup.map b).comp (FreeGroup.map g) := by
        apply FreeGroup.ext_hom
        intro x
        simp only [MonoidHom.comp_apply, FreeGroup.map.of]
        exact congrArg FreeGroup.of (hab x)
      simpa using congrArg (fun h : FreeGroup A →* FreeGroup V =>
        (QuotientGroup.mk (h w) : PresGroup (rel τ b))) hm

theorem padding_chain_square
    (x : J →₀ MonoidAlgebra ℤ (PresGroup ρ)) :
    (paddedInclusion ρ τ g f hf hrel a b hab).cells ((structuralMap ρ a ha).cells x) =
    (structuralMap τ b hb).cells ((PresInclusionFS.mor ρ τ g f hg hf hrel).cells x) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy =>
      rw [PresMorFS.cells_add, PresMorFS.cells_add, PresMorFS.cells_add,
        PresMorFS.cells_add, hx, hy]
  | single j c =>
      change Finsupp.mapDomain f
        (((Finsupp.single j c).mapRange (coefficients ρ a) (map_zero _)).mapRange
          (PresInclusionFS.coefficients (rel ρ a) (rel τ b) id f
            (padded_rel ρ τ g f hrel a b hab)) (map_zero _)) =
        (Finsupp.mapDomain f ((Finsupp.single j c).mapRange
          (PresInclusionFS.coefficients ρ τ g f hrel) (map_zero _))).mapRange
            (coefficients τ b) (map_zero _)
      simp only [Finsupp.mapRange_single, Finsupp.mapDomain_single]
      congr 1
      change MonoidAlgebra.mapDomainRingHom ℤ (paddedInclusion ρ τ g f hf hrel a b hab).hom
        (MonoidAlgebra.mapDomainRingHom ℤ (structuralMap ρ a ha).hom c) =
        MonoidAlgebra.mapDomainRingHom ℤ (structuralMap τ b hb).hom
          (MonoidAlgebra.mapDomainRingHom ℤ (PresInclusionFS.mor ρ τ g f hg hf hrel).hom c)
      rw [BlockMor.mapDomainRingHom_comp', BlockMor.mapDomainRingHom_comp',
        padding_group_square ρ τ g f hg hf hrel a b ha hb hab]

include ha hb in
theorem padding_preserves_zero
    (hzero : ∀ x, FSIsFoxCycle ρ x →
      (PresInclusionFS.mor ρ τ g f hg hf hrel).cells x = 0)
    {x} (hx : FSIsFoxCycle (rel ρ a) x) :
    (paddedInclusion ρ τ g f hf hrel a b hab).cells x = 0 :=
  fsCells_eq_zero_of_generates (structuralMap ρ a ha) (structuralMap τ b hb)
    (PresInclusionFS.mor ρ τ g f hg hf hrel)
    (paddedInclusion ρ τ g f hf hrel a b hab)
    (padding_chain_square ρ τ g f hg hf hrel a b ha hb hab)
    hzero (structuralMap_generates ρ a ha) hx

end FiniteChains.FreePadding
