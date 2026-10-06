import RequestProject.BlockFamilyAmalgamation

/-!
# Individual factors of a simultaneous substitution

The simultaneous substituted group is the actual wide amalgamated product of the
individual substituted groups over the original group.  Both comparison maps are
constructed here from the presentation and pushout universal properties.  In
particular, injectivity of every individual base map implies injectivity of every
individual factor in the simultaneous group, and hence of its group-ring map.

There is no finiteness or nonemptiness assumption on the family.  These are group
and group-ring comparison results; they do not assert the polygon coefficient
calculation or property (B2).


-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.BlockFamily

noncomputable section

variable {α Jr Sx : Type} {Zt Mt : Sx → Type}
  (ρ : Jr ⊕ Sx → FreeGroup α)
  (bsub : ∀ s : Sx, Mt s → FreeGroup (α ⊕ Zt s))

/-- Replace only the selected original relator, retaining all other entries. -/
abbrev IndividualGroup (s : Sx) :=
  PresGroup (substPresF (oneRel ρ s) (fun _ : PUnit.{1} => bsub s))

/-- The actual inclusion of the generators of one individual substitution. -/
def individualGenEmb (s : Sx) :
    α ⊕ (Σ _ : PUnit.{1}, Zt s) → α ⊕ (Σ t : Sx, Zt t) :=
  Sum.elim Sum.inl (fun p => Sum.inr ⟨s, p.2⟩)

theorem individualGenEmb_old (s : Sx) (w : FreeGroup α) :
    FreeGroup.map (individualGenEmb (Zt := Zt) s)
        (FreeGroup.map (Sum.inl (β := Σ _ : PUnit.{1}, Zt s)) w) =
      FreeGroup.map (Sum.inl (β := Σ t : Sx, Zt t)) w := by
  have h : (FreeGroup.map (individualGenEmb (α := α) (Zt := Zt) s)).comp
      (FreeGroup.map (Sum.inl (β := Σ _ : PUnit.{1}, Zt s))) =
      FreeGroup.map (Sum.inl (β := Σ t : Sx, Zt t)) := by
    apply FreeGroup.ext_hom
    intro a
    simp [individualGenEmb]
  exact DFunLike.congr_fun h w

theorem individualGenEmb_block (s : Sx) (w : FreeGroup (α ⊕ Zt s)) :
    FreeGroup.map (individualGenEmb (Zt := Zt) s)
        (FreeGroup.map (genEmb (Zt := fun _ : PUnit.{1} => Zt s) PUnit.unit) w) =
      FreeGroup.map (genEmb (Zt := Zt) s) w := by
  have h : (FreeGroup.map (individualGenEmb (α := α) (Zt := Zt) s)).comp
      (FreeGroup.map (genEmb (Zt := fun _ : PUnit.{1} => Zt s) PUnit.unit)) =
      FreeGroup.map (genEmb (Zt := Zt) s) := by
    apply FreeGroup.ext_hom
    rintro (a | z) <;> simp [individualGenEmb, genEmb]
  exact DFunLike.congr_fun h w

/-- The canonical map of an individual substituted factor to the simultaneous group.
Its definition uses the genuine simultaneous fillings to kill the other old entries. -/
def factorToFamily (hfill : FilledF ρ bsub) (s : Sx) :
    IndividualGroup ρ bsub s →* PresGroup (substPresF ρ bsub) :=
  QuotientGroup.lift _
    ((QuotientGroup.mk' (relSub (substPresF ρ bsub))).comp
      (FreeGroup.map (individualGenEmb (Zt := Zt) s))) (by
    refine Subgroup.normalClosure_le_normal ?_
    rintro _ ⟨k, rfl⟩
    change (QuotientGroup.mk (FreeGroup.map (individualGenEmb (Zt := Zt) s)
      (substPresF (oneRel ρ s) (fun _ : PUnit.{1} => bsub s) k)) :
      PresGroup (substPresF ρ bsub)) = 1
    rcases k with (r | ⟨p, m⟩)
    · rw [substPresF_inl, individualGenEmb_old]
      rcases r with (r | t)
      · exact (QuotientGroup.eq_one_iff _).2
          (Subgroup.subset_normalClosure ⟨Sum.inl r, rfl⟩)
      · exact (QuotientGroup.eq_one_iff _).2 (hfill t.val)
    · cases p
      rw [substPresF_inr, individualGenEmb_block]
      exact (QuotientGroup.eq_one_iff _).2
        (Subgroup.subset_normalClosure ⟨Sum.inr ⟨s, m⟩, rfl⟩))

@[simp] theorem factorToFamily_mk (hfill : FilledF ρ bsub) (s : Sx)
    (w : FreeGroup (α ⊕ (Σ _ : PUnit.{1}, Zt s))) :
    factorToFamily ρ bsub hfill s (QuotientGroup.mk w) =
      QuotientGroup.mk (FreeGroup.map (individualGenEmb (Zt := Zt) s) w) := rfl

/-- The original group maps to an individual factor by the single substitution,
with the original relator indexing restored. -/
def individualBase
    (hone : ∀ s, FilledF (oneRel ρ s) (fun _ : PUnit.{1} => bsub s))
    (s : Sx) : PresGroup ρ →* IndividualGroup ρ bsub s :=
  (substHomF (oneRel ρ s) (fun _ : PUnit.{1} => bsub s) (hone s)).comp
    (oneEquiv ρ s).toMonoidHom

@[simp] theorem individualBase_mk
    (hone : ∀ s, FilledF (oneRel ρ s) (fun _ : PUnit.{1} => bsub s))
    (s : Sx) (w : FreeGroup α) :
    individualBase ρ bsub hone s (QuotientGroup.mk w) =
      QuotientGroup.mk (FreeGroup.map (Sum.inl (β := Σ _ : PUnit.{1}, Zt s)) w) := rfl

/-- Compatibility of the actual factor maps with the common original group. -/
theorem factorToFamily_comp_individualBase (hfill : FilledF ρ bsub)
    (hone : ∀ s, FilledF (oneRel ρ s) (fun _ : PUnit.{1} => bsub s)) (s : Sx) :
    (factorToFamily ρ bsub hfill s).comp (individualBase ρ bsub hone s) =
      substHomF ρ bsub hfill := by
  apply MonoidHom.ext
  intro x
  induction x using QuotientGroup.induction_on with
  | _ w =>
      change factorToFamily ρ bsub hfill s
        (individualBase ρ bsub hone s (QuotientGroup.mk w)) =
          substHomF ρ bsub hfill (QuotientGroup.mk w)
      rw [individualBase_mk, factorToFamily_mk, individualGenEmb_old, substHomF_mk]

/-- The block free group maps to its own individual substituted factor. -/
def individualBlockFree (s : Sx) : FreeGroup (α ⊕ Zt s) →* IndividualGroup ρ bsub s :=
  (QuotientGroup.mk' _).comp
    (FreeGroup.map (genEmb (Zt := fun _ : PUnit.{1} => Zt s) PUnit.unit))

theorem individualBlockFree_mark
    (hone : ∀ s, FilledF (oneRel ρ s) (fun _ : PUnit.{1} => bsub s))
    (s : Sx) (a : α) :
    individualBlockFree ρ bsub s (FreeGroup.of (Sum.inl a)) =
      individualBase ρ bsub hone s (QuotientGroup.mk (FreeGroup.of a)) := rfl

theorem individualBlockFree_rel (s : Sx) (m : Mt s) :
    individualBlockFree ρ bsub s (bsub s m) = 1 := by
  apply (QuotientGroup.eq_one_iff _).2
  exact Subgroup.subset_normalClosure ⟨Sum.inr ⟨PUnit.unit, m⟩, rfl⟩

theorem factorToFamily_block (hfill : FilledF ρ bsub)
    (s : Sx) (w : FreeGroup (α ⊕ Zt s)) :
    factorToFamily ρ bsub hfill s (individualBlockFree ρ bsub s w) =
      QuotientGroup.mk (FreeGroup.map (genEmb (Zt := Zt) s) w) := by
  change factorToFamily ρ bsub hfill s
    (QuotientGroup.mk (FreeGroup.map
      (genEmb (Zt := fun _ : PUnit.{1} => Zt s) PUnit.unit) w)) = _
  rw [factorToFamily_mk, individualGenEmb_block]

/-- A concrete marked receiver in the wide amalgamated product of the individual factors. -/
def familyAmalgamMaps
    (hone : ∀ s, FilledF (oneRel ρ s) (fun _ : PUnit.{1} => bsub s)) :
    BlockMaps ρ bsub (Monoid.PushoutI.base (individualBase ρ bsub hone)) where
  b s := (Monoid.PushoutI.of s).comp (individualBlockFree ρ bsub s)
  mark s a := by
    rw [MonoidHom.comp_apply, individualBlockFree_mark ρ bsub hone,
      Monoid.PushoutI.of_apply_eq_base]
  rel s m := by rw [MonoidHom.comp_apply, individualBlockFree_rel, map_one]

/-- The comparison from the simultaneous presentation to the actual wide pushout. -/
def familyToAmalgam
    (hone : ∀ s, FilledF (oneRel ρ s) (fun _ : PUnit.{1} => bsub s)) :
    PresGroup (substPresF ρ bsub) →* Monoid.PushoutI (individualBase ρ bsub hone) :=
  (familyAmalgamMaps ρ bsub hone).psi

@[simp] theorem familyToAmalgam_old
    (hone : ∀ s, FilledF (oneRel ρ s) (fun _ : PUnit.{1} => bsub s)) (a : α) :
    familyToAmalgam ρ bsub hone (QuotientGroup.mk (FreeGroup.of (Sum.inl a))) =
      Monoid.PushoutI.base (individualBase ρ bsub hone)
        (QuotientGroup.mk (FreeGroup.of a)) := by
  change FreeGroup.lift (familyAmalgamMaps ρ bsub hone).gen (FreeGroup.of _) = _
  rw [FreeGroup.lift_apply_of]
  rfl

@[simp] theorem familyToAmalgam_internal
    (hone : ∀ s, FilledF (oneRel ρ s) (fun _ : PUnit.{1} => bsub s))
    (s : Sx) (z : Zt s) :
    familyToAmalgam ρ bsub hone
        (QuotientGroup.mk (FreeGroup.of (Sum.inr ⟨s, z⟩))) =
      Monoid.PushoutI.of s (individualBlockFree ρ bsub s (FreeGroup.of (Sum.inr z))) := by
  change FreeGroup.lift (familyAmalgamMaps ρ bsub hone).gen (FreeGroup.of _) = _
  rw [FreeGroup.lift_apply_of]
  rfl

theorem familyToAmalgam_comp_base (hfill : FilledF ρ bsub)
    (hone : ∀ s, FilledF (oneRel ρ s) (fun _ : PUnit.{1} => bsub s)) :
    (familyToAmalgam ρ bsub hone).comp (substHomF ρ bsub hfill) =
      Monoid.PushoutI.base (individualBase ρ bsub hone) :=
  (familyAmalgamMaps ρ bsub hone).psi_comp_substHomF hfill

/-- The factor comparison triangle identifies the composite with the genuine pushout injection. -/
theorem familyToAmalgam_comp_factor (hfill : FilledF ρ bsub)
    (hone : ∀ s, FilledF (oneRel ρ s) (fun _ : PUnit.{1} => bsub s)) (s : Sx) :
    (familyToAmalgam ρ bsub hone).comp (factorToFamily ρ bsub hfill s) =
      Monoid.PushoutI.of s := by
  have hw : ((familyToAmalgam ρ bsub hone).comp (factorToFamily ρ bsub hfill s)).comp
      (QuotientGroup.mk' _) =
      (Monoid.PushoutI.of (φ := individualBase ρ bsub hone) s).comp
        (QuotientGroup.mk' _) := by
    apply FreeGroup.ext_hom
    rintro (a | ⟨p, z⟩)
    · change familyToAmalgam ρ bsub hone
        (QuotientGroup.mk (FreeGroup.of (Sum.inl a))) =
          Monoid.PushoutI.of s
            (individualBase ρ bsub hone s (QuotientGroup.mk (FreeGroup.of a)))
      rw [familyToAmalgam_old, Monoid.PushoutI.of_apply_eq_base]
    · cases p
      exact familyToAmalgam_internal ρ bsub hone s z
  apply MonoidHom.ext
  intro x
  induction x using QuotientGroup.induction_on with
  | _ w => exact DFunLike.congr_fun hw w

/-- The inverse comparison, obtained from the wide pushout universal property. -/
def amalgamToFamily (hfill : FilledF ρ bsub)
    (hone : ∀ s, FilledF (oneRel ρ s) (fun _ : PUnit.{1} => bsub s)) :
    Monoid.PushoutI (individualBase ρ bsub hone) →* PresGroup (substPresF ρ bsub) :=
  Monoid.PushoutI.lift (factorToFamily ρ bsub hfill) (substHomF ρ bsub hfill)
    (factorToFamily_comp_individualBase ρ bsub hfill hone)

@[simp] theorem amalgamToFamily_of (hfill : FilledF ρ bsub)
    (hone : ∀ s, FilledF (oneRel ρ s) (fun _ : PUnit.{1} => bsub s))
    (s : Sx) (x : IndividualGroup ρ bsub s) :
    amalgamToFamily ρ bsub hfill hone (Monoid.PushoutI.of s x) =
      factorToFamily ρ bsub hfill s x := by
  simp [amalgamToFamily]

@[simp] theorem amalgamToFamily_base (hfill : FilledF ρ bsub)
    (hone : ∀ s, FilledF (oneRel ρ s) (fun _ : PUnit.{1} => bsub s))
    (x : PresGroup ρ) :
    amalgamToFamily ρ bsub hfill hone
        (Monoid.PushoutI.base (individualBase ρ bsub hone) x) =
      substHomF ρ bsub hfill x := by
  simp [amalgamToFamily]

theorem amalgamToFamily_comp_familyToAmalgam (hfill : FilledF ρ bsub)
    (hone : ∀ s, FilledF (oneRel ρ s) (fun _ : PUnit.{1} => bsub s)) :
    (amalgamToFamily ρ bsub hfill hone).comp (familyToAmalgam ρ bsub hone) =
      MonoidHom.id _ := by
  have hw : ((amalgamToFamily ρ bsub hfill hone).comp
      (familyToAmalgam ρ bsub hone)).comp (QuotientGroup.mk' _) =
      (QuotientGroup.mk' (relSub (substPresF ρ bsub))) := by
    apply FreeGroup.ext_hom
    rintro (a | ⟨s, z⟩)
    · change amalgamToFamily ρ bsub hfill hone
        (familyToAmalgam ρ bsub hone
          (QuotientGroup.mk (FreeGroup.of (Sum.inl a)))) = _
      rw [familyToAmalgam_old, amalgamToFamily_base]
      rfl
    · change amalgamToFamily ρ bsub hfill hone
        (familyToAmalgam ρ bsub hone
          (QuotientGroup.mk (FreeGroup.of (Sum.inr ⟨s, z⟩)))) = _
      rw [familyToAmalgam_internal, amalgamToFamily_of, factorToFamily_block]
      rfl
  apply MonoidHom.ext
  intro x
  induction x using QuotientGroup.induction_on with
  | _ w => exact DFunLike.congr_fun hw w

theorem familyToAmalgam_comp_amalgamToFamily (hfill : FilledF ρ bsub)
    (hone : ∀ s, FilledF (oneRel ρ s) (fun _ : PUnit.{1} => bsub s)) :
    (familyToAmalgam ρ bsub hone).comp (amalgamToFamily ρ bsub hfill hone) =
      MonoidHom.id _ := by
  apply Monoid.PushoutI.hom_ext
  · intro s
    apply MonoidHom.ext
    intro x
    change familyToAmalgam ρ bsub hone
      (amalgamToFamily ρ bsub hfill hone (Monoid.PushoutI.of s x)) =
        Monoid.PushoutI.of s x
    rw [amalgamToFamily_of]
    exact DFunLike.congr_fun (familyToAmalgam_comp_factor ρ bsub hfill hone s) x
  · apply MonoidHom.ext
    intro x
    change familyToAmalgam ρ bsub hone
      (amalgamToFamily ρ bsub hfill hone
        (Monoid.PushoutI.base (individualBase ρ bsub hone) x)) =
          Monoid.PushoutI.base (individualBase ρ bsub hone) x
    rw [amalgamToFamily_base]
    exact DFunLike.congr_fun (familyToAmalgam_comp_base ρ bsub hfill hone) x

/-- The simultaneous group is the wide amalgamated product, including for an empty family. -/
def familyAmalgamEquiv (hfill : FilledF ρ bsub)
    (hone : ∀ s, FilledF (oneRel ρ s) (fun _ : PUnit.{1} => bsub s)) :
    PresGroup (substPresF ρ bsub) ≃* Monoid.PushoutI (individualBase ρ bsub hone) where
  toFun := familyToAmalgam ρ bsub hone
  invFun := amalgamToFamily ρ bsub hfill hone
  left_inv x := DFunLike.congr_fun (amalgamToFamily_comp_familyToAmalgam ρ bsub hfill hone) x
  right_inv x := DFunLike.congr_fun (familyToAmalgam_comp_amalgamToFamily ρ bsub hfill hone) x
  map_mul' := map_mul (familyToAmalgam ρ bsub hone)

/-- Each individual factor embeds when every individual substitution embeds the original group.
The only injectivity input concerns the already constructed individual base maps. -/
theorem factorToFamily_injective (hfill : FilledF ρ bsub)
    (hone : ∀ s, FilledF (oneRel ρ s) (fun _ : PUnit.{1} => bsub s))
    (hinj : ∀ s, Function.Injective
      (substHomF (oneRel ρ s) (fun _ : PUnit.{1} => bsub s) (hone s)))
    (s : Sx) : Function.Injective (factorToFamily ρ bsub hfill s) := by
  have hj : ∀ s, Function.Injective (individualBase ρ bsub hone s) :=
    fun t => (hinj t).comp (oneEquiv ρ t).injective
  have hs := Monoid.PushoutI.of_injective hj s
  intro x y hxy
  apply hs
  calc
    Monoid.PushoutI.of s x =
        familyToAmalgam ρ bsub hone (factorToFamily ρ bsub hfill s x) :=
      (DFunLike.congr_fun (familyToAmalgam_comp_factor ρ bsub hfill hone s) x).symm
    _ = familyToAmalgam ρ bsub hone (factorToFamily ρ bsub hfill s y) :=
      congrArg (familyToAmalgam ρ bsub hone) hxy
    _ = Monoid.PushoutI.of s y :=
      DFunLike.congr_fun (familyToAmalgam_comp_factor ρ bsub hfill hone s) y

/-- The coefficient homomorphism used to extend a calculation in an individual factor. -/
def factorRingHom (hfill : FilledF ρ bsub) (s : Sx) :
    MonoidAlgebra ℤ (IndividualGroup ρ bsub s) →+*
      MonoidAlgebra ℤ (PresGroup (substPresF ρ bsub)) :=
  MonoidAlgebra.mapDomainRingHom ℤ (factorToFamily ρ bsub hfill s)

theorem factorRingHom_injective (hfill : FilledF ρ bsub)
    (hone : ∀ s, FilledF (oneRel ρ s) (fun _ : PUnit.{1} => bsub s))
    (hinj : ∀ s, Function.Injective
      (substHomF (oneRel ρ s) (fun _ : PUnit.{1} => bsub s) (hone s)))
    (s : Sx) : Function.Injective (factorRingHom ρ bsub hfill s) :=
  fun _ _ h => MonoidAlgebra.coeff_injective
    (Finsupp.mapDomain_injective (factorToFamily_injective ρ bsub hfill hone hinj s)
      (congrArg MonoidAlgebra.coeff h))

end

end FiniteChains.BlockFamily
