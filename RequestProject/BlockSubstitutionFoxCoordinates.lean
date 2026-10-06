module

public import RequestProject.FoxCoordinateSubstitution

@[expose] public section

/-! Internal Fox coordinates of the actual simultaneous word substitution. -/
namespace FiniteChains.BlockFamily
universe u
variable {A Jr S : Type u} {I Z M : S → Type u}
  (ρ : Jr ⊕ S → FreeGroup A) (u : ∀ s, I s → FreeGroup A)
  (β : ∀ s, M s → FreeGroup (I s ⊕ Z s))

/-- The actual homomorphism from a marked block presentation to the substituted
group, obtained by substituting its markings and including its own generators. -/
def markedBlockHom (s : S) : PresGroup (β s) →*
    PresGroup (substPresF ρ (fun s m => blockSubst u s (β s m))) :=
  QuotientGroup.lift _
    ((QuotientGroup.mk' (relSub (substPresF ρ (fun s m => blockSubst u s (β s m))))).comp
      ((FreeGroup.map (genEmb s)).comp (blockSubst u s))) (by
    refine Subgroup.normalClosure_le_normal ?_
    rintro _ ⟨m, rfl⟩
    exact (QuotientGroup.eq_one_iff _).mpr
      (Subgroup.subset_normalClosure ⟨Sum.inr ⟨s, m⟩, rfl⟩))

@[simp] theorem markedBlockHom_mk (s : S) (w : FreeGroup (I s ⊕ Z s)) :
    markedBlockHom ρ u β s (QuotientGroup.mk w) =
      QuotientGroup.mk (FreeGroup.map (genEmb s) (blockSubst u s w)) := rfl

theorem markedBlockHom_coeff (s : S) (x : FreeGroupRing (I s ⊕ Z s)) :
    MonoidAlgebra.mapDomainRingHom ℤ (markedBlockHom ρ u β s)
      (quotRingHom ℤ (relSub (β s)) x) =
    quotRingHom ℤ (relSub (substPresF ρ (fun s m => blockSubst u s (β s m))))
      (freeRingMap (genEmb s) (MonoidAlgebra.mapDomainRingHom ℤ (blockSubst u s) x)) := by
  change MonoidAlgebra.mapDomainRingHom ℤ (markedBlockHom ρ u β s)
      (MonoidAlgebra.mapDomainRingHom ℤ (QuotientGroup.mk' (relSub (β s))) x) =
    MonoidAlgebra.mapDomainRingHom ℤ
      (QuotientGroup.mk' (relSub (substPresF ρ (fun s m => blockSubst u s (β s m)))))
      (MonoidAlgebra.mapDomainRingHom ℤ (FreeGroup.map (genEmb s))
        (MonoidAlgebra.mapDomainRingHom ℤ (blockSubst u s) x))
  simp only [BlockMor.mapDomainRingHom_comp']
  congr 1

variable [DecidableEq A] [DecidableEq S]
  [∀ s, DecidableEq (I s)] [∀ s, DecidableEq (Z s)]

/-- The internal column of the substituted presentation is precisely the block
column with its coefficients sent through the constructed block homomorphism. -/
theorem foxMatrix_markedBlock_internal (s : S) (z : Z s) (m : M s) :
    foxMatrixPres (substPresF ρ (fun s m => blockSubst u s (β s m)))
      (Sum.inr ⟨s, z⟩) (Sum.inr ⟨s, m⟩) =
    MonoidAlgebra.mapDomainRingHom ℤ (markedBlockHom ρ u β s)
      (foxMatrixPres (β s) (Sum.inr z) m) := by
  rw [foxMatrixPres, foxMatrixPres, markedBlockHom_coeff, substPresF_inr]
  change quotRingHom ℤ _
      (fox (genEmb s (Sum.inr z)) (FreeGroup.map (genEmb s) (blockSubst u s (β s m)))) = _
  rw [fox_map (genEmb s) (genEmb_injective s), fox_blockSubst_internal]

end FiniteChains.BlockFamily
