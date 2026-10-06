import RequestProject.PresentationDictionary

/-!
# Free products of presentations, and injectivity of the inclusions of the factors

Step 1 of the gluing lemma needs, for the modified chambers, that the **inclusion maps of the
pieces embed the free factors** of the resulting group.  At the level of presentations this is
the statement proved here: the presentation of the free product is the disjoint union of the two
presentations, it retracts onto each factor by killing the other family of generators, and
therefore each inclusion is injective.

* `FiniteChains.coprodRel` — the presentation `⟨α ⊔ β | ρ ⊔ σ⟩` of the free product;
* `FiniteChains.coprodInl`, `FiniteChains.coprodInr` — the two inclusions of the factors;
* `FiniteChains.coprodFst`, `FiniteChains.coprodSnd` — the two retractions, which send the
  generators of the other factor to `1`;
* `FiniteChains.coprodFst_coprodInl`, `FiniteChains.coprodSnd_coprodInr` — the retraction
  identities;
* `FiniteChains.coprodInl_injective`, `FiniteChains.coprodInr_injective` — **the inclusions of
  the factors are injective**, which is the `π₁`-injectivity input in the form in which the
  chain arguments use it.

The proof uses the retraction, not normal forms, so it applies verbatim to any presentation of
the shape "disjoint union of generators and of relators", in particular to the presentation
obtained from a graph of spaces with a maximal tree in which the pieces are glued along
contractible (tree) parts.
-/

namespace FiniteChains

universe u

variable {α β J K : Type u}

/-- The presentation of the free product: generators `α ⊕ β`, relators `ρ` and `σ` read in the
corresponding free factors. -/
def coprodRel (ρ : J → FreeGroup α) (σ : K → FreeGroup β) : J ⊕ K → FreeGroup (α ⊕ β) :=
  Sum.elim (fun j => FreeGroup.map Sum.inl (ρ j)) (fun k => FreeGroup.map Sum.inr (σ k))

@[simp] theorem coprodRel_inl (ρ : J → FreeGroup α) (σ : K → FreeGroup β) (j : J) :
    coprodRel ρ σ (Sum.inl j) = FreeGroup.map Sum.inl (ρ j) := rfl

@[simp] theorem coprodRel_inr (ρ : J → FreeGroup α) (σ : K → FreeGroup β) (k : K) :
    coprodRel ρ σ (Sum.inr k) = FreeGroup.map Sum.inr (σ k) := rfl

section

variable (ρ : J → FreeGroup α) (σ : K → FreeGroup β)

/-- The homomorphism `FreeGroup (α ⊕ β) → FreeGroup α` killing the second family of
generators. -/
def killSnd : FreeGroup (α ⊕ β) →* FreeGroup α :=
  FreeGroup.lift (Sum.elim FreeGroup.of (fun _ => 1))

/-- The homomorphism `FreeGroup (α ⊕ β) → FreeGroup β` killing the first family of
generators. -/
def killFst : FreeGroup (α ⊕ β) →* FreeGroup β :=
  FreeGroup.lift (Sum.elim (fun _ => 1) FreeGroup.of)

@[simp] theorem killSnd_map_inl (w : FreeGroup α) :
    killSnd (α := α) (β := β) (FreeGroup.map Sum.inl w) = w := by
  have : (killSnd (α := α) (β := β)).comp (FreeGroup.map (Sum.inl : α → α ⊕ β)) =
      MonoidHom.id _ := by
    refine FreeGroup.ext_hom _ _ (fun a => ?_)
    simp [killSnd]
  exact congrArg (fun F : FreeGroup α →* FreeGroup α => F w) this

@[simp] theorem killSnd_map_inr (w : FreeGroup β) :
    killSnd (α := α) (β := β) (FreeGroup.map Sum.inr w) = 1 := by
  have : (killSnd (α := α) (β := β)).comp (FreeGroup.map (Sum.inr : β → α ⊕ β)) = 1 := by
    refine FreeGroup.ext_hom _ _ (fun b => ?_)
    simp [killSnd]
  exact congrArg (fun F : FreeGroup β →* FreeGroup α => F w) this

@[simp] theorem killFst_map_inr (w : FreeGroup β) :
    killFst (α := α) (β := β) (FreeGroup.map Sum.inr w) = w := by
  have : (killFst (α := α) (β := β)).comp (FreeGroup.map (Sum.inr : β → α ⊕ β)) =
      MonoidHom.id _ := by
    refine FreeGroup.ext_hom _ _ (fun b => ?_)
    simp [killFst]
  exact congrArg (fun F : FreeGroup β →* FreeGroup β => F w) this

@[simp] theorem killFst_map_inl (w : FreeGroup α) :
    killFst (α := α) (β := β) (FreeGroup.map Sum.inl w) = 1 := by
  have : (killFst (α := α) (β := β)).comp (FreeGroup.map (Sum.inl : α → α ⊕ β)) = 1 := by
    refine FreeGroup.ext_hom _ _ (fun a => ?_)
    simp [killFst]
  exact congrArg (fun F : FreeGroup α →* FreeGroup β => F w) this

/-- The inclusion of the first factor. -/
def coprodInl : PresGroup ρ →* PresGroup (coprodRel ρ σ) :=
  QuotientGroup.lift _
    ((QuotientGroup.mk' (relSub (coprodRel ρ σ))).comp (FreeGroup.map Sum.inl))
    (fun w hw => by
      have hsub : relSub ρ ≤ MonoidHom.ker ((QuotientGroup.mk' (relSub (coprodRel ρ σ))).comp
          (FreeGroup.map (Sum.inl : α → α ⊕ β))) := by
        refine Subgroup.normalClosure_le_normal ?_
        rintro _ ⟨j, rfl⟩
        refine MonoidHom.mem_ker.2 ?_
        show (QuotientGroup.mk (FreeGroup.map Sum.inl (ρ j)) : PresGroup (coprodRel ρ σ)) = 1
        rw [QuotientGroup.eq_one_iff]
        exact Subgroup.subset_normalClosure ⟨Sum.inl j, rfl⟩
      exact hsub hw)

/-- The inclusion of the second factor. -/
def coprodInr : PresGroup σ →* PresGroup (coprodRel ρ σ) :=
  QuotientGroup.lift _
    ((QuotientGroup.mk' (relSub (coprodRel ρ σ))).comp (FreeGroup.map Sum.inr))
    (fun w hw => by
      have hsub : relSub σ ≤ MonoidHom.ker ((QuotientGroup.mk' (relSub (coprodRel ρ σ))).comp
          (FreeGroup.map (Sum.inr : β → α ⊕ β))) := by
        refine Subgroup.normalClosure_le_normal ?_
        rintro _ ⟨k, rfl⟩
        refine MonoidHom.mem_ker.2 ?_
        show (QuotientGroup.mk (FreeGroup.map Sum.inr (σ k)) : PresGroup (coprodRel ρ σ)) = 1
        rw [QuotientGroup.eq_one_iff]
        exact Subgroup.subset_normalClosure ⟨Sum.inr k, rfl⟩
      exact hsub hw)

/-- The retraction onto the first factor. -/
def coprodFst : PresGroup (coprodRel ρ σ) →* PresGroup ρ :=
  QuotientGroup.lift _ ((QuotientGroup.mk' (relSub ρ)).comp killSnd)
    (fun w hw => by
      have hsub : relSub (coprodRel ρ σ) ≤
          MonoidHom.ker ((QuotientGroup.mk' (relSub ρ)).comp (killSnd (α := α) (β := β))) := by
        refine Subgroup.normalClosure_le_normal ?_
        rintro _ ⟨jk, rfl⟩
        refine MonoidHom.mem_ker.2 ?_
        show (QuotientGroup.mk (killSnd (coprodRel ρ σ jk)) : PresGroup ρ) = 1
        rw [QuotientGroup.eq_one_iff]
        cases jk with
        | inl j =>
            rw [coprodRel_inl, killSnd_map_inl]
            exact Subgroup.subset_normalClosure ⟨j, rfl⟩
        | inr k =>
            rw [coprodRel_inr, killSnd_map_inr]
            exact Subgroup.one_mem _
      exact hsub hw)

/-- The retraction onto the second factor. -/
def coprodSnd : PresGroup (coprodRel ρ σ) →* PresGroup σ :=
  QuotientGroup.lift _ ((QuotientGroup.mk' (relSub σ)).comp killFst)
    (fun w hw => by
      have hsub : relSub (coprodRel ρ σ) ≤
          MonoidHom.ker ((QuotientGroup.mk' (relSub σ)).comp (killFst (α := α) (β := β))) := by
        refine Subgroup.normalClosure_le_normal ?_
        rintro _ ⟨jk, rfl⟩
        refine MonoidHom.mem_ker.2 ?_
        show (QuotientGroup.mk (killFst (coprodRel ρ σ jk)) : PresGroup σ) = 1
        rw [QuotientGroup.eq_one_iff]
        cases jk with
        | inl j =>
            rw [coprodRel_inl, killFst_map_inl]
            exact Subgroup.one_mem _
        | inr k =>
            rw [coprodRel_inr, killFst_map_inr]
            exact Subgroup.subset_normalClosure ⟨k, rfl⟩
      exact hsub hw)

/-- The first retraction undoes the first inclusion. -/
theorem coprodFst_coprodInl (x : PresGroup ρ) : coprodFst ρ σ (coprodInl ρ σ x) = x := by
  refine QuotientGroup.induction_on x (fun w => ?_)
  show (QuotientGroup.mk (killSnd (FreeGroup.map Sum.inl w)) : PresGroup ρ) =
    QuotientGroup.mk w
  rw [killSnd_map_inl]

/-- The second retraction undoes the second inclusion. -/
theorem coprodSnd_coprodInr (y : PresGroup σ) : coprodSnd ρ σ (coprodInr ρ σ y) = y := by
  refine QuotientGroup.induction_on y (fun w => ?_)
  show (QuotientGroup.mk (killFst (FreeGroup.map Sum.inr w)) : PresGroup σ) =
    QuotientGroup.mk w
  rw [killFst_map_inr]

/-- **The inclusion of the first factor is injective.** -/
theorem coprodInl_injective : Function.Injective (coprodInl ρ σ) :=
  Function.LeftInverse.injective (g := coprodFst ρ σ) (coprodFst_coprodInl ρ σ)

/-- **The inclusion of the second factor is injective.** -/
theorem coprodInr_injective : Function.Injective (coprodInr ρ σ) :=
  Function.LeftInverse.injective (g := coprodSnd ρ σ) (coprodSnd_coprodInr ρ σ)

end

/-- A homomorphism with a left inverse is injective: the abstract form of the `π₁`-injectivity
argument used above and in the radial retraction of the article's Step 1. -/
theorem injective_of_retraction {G H : Type u} [Group G] [Group H] (f : G →* H) (r : H →* G)
    (h : ∀ x, r (f x) = x) : Function.Injective f :=
  Function.LeftInverse.injective (g := r) h

end FiniteChains
