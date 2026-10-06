import RequestProject.InitialComplexFinsupp
import RequestProject.FreeGeneratorPaddingFinsupp

/-! A concrete initial ambient presentation for every acyclic core.
The added alphabet contains a free padding generator, including when the
core alphabet is empty. All core generators and relators retain their
literal `Sum.inl` labels. No ordering or finiteness of the core is assumed
by the final construction. -/

noncomputable section
open scoped Classical

namespace FiniteChains.InitialFS
open RelativeNormalForm

variable {A M : Type}

private def chosenOrder (A : Type) : LinearOrder A :=
  IsWellOrder.linearOrder (@WellOrderingRel A)

abbrev ExtraGen (A : Type) := (A × Bool) ⊕ PUnit

def ExtraCell (A : Type) : Type :=
  letI : LinearOrder A := chosenOrder A
  A ⊕ CrossY A

/-- A canonical genuinely new generator, independent of whether `A` is empty. -/
def fresh (A : Type) : ExtraGen A := Sum.inr PUnit.unit

instance (A : Type) : Nonempty (ExtraGen A) := ⟨fresh A⟩

def generatorEmbedding : GenY A → A ⊕ ExtraGen A
  | Sum.inl a => Sum.inl a
  | Sum.inr b => Sum.inr (Sum.inl b)

theorem generatorEmbedding_injective :
    Function.Injective (generatorEmbedding (A := A)) := by
  intro x y h
  cases x <;> cases y <;> simp_all [generatorEmbedding]

def baseRel (core : M → FreeGroup A) : M ⊕ ExtraCell A → FreeGroup (GenY A) :=
  letI : LinearOrder A := chosenOrder A
  relY core

@[simp] theorem baseRel_core (core : M → FreeGroup A) (m : M) :
    baseRel core (Sum.inl m) = FreeGroup.map Sum.inl (core m) := rfl

def extra (core : M → FreeGroup A) : ExtraCell A → FreeGroup (A ⊕ ExtraGen A) :=
  fun c => FreeGroup.map generatorEmbedding (baseRel core (Sum.inr c))

private theorem generatorEmbedding_map_core (w : FreeGroup A) :
    FreeGroup.map generatorEmbedding (FreeGroup.map Sum.inl w) =
      FreeGroup.map (Sum.inl (β := ExtraGen A)) w := by
  have h : (FreeGroup.map generatorEmbedding).comp (FreeGroup.map Sum.inl) =
      FreeGroup.map (Sum.inl (β := ExtraGen A)) := by
    apply FreeGroup.ext_hom
    intro a
    simp [generatorEmbedding]
  exact congrArg (fun f : FreeGroup A →* FreeGroup (A ⊕ ExtraGen A) => f w) h

theorem rawPresentation_eq_padding (core : M → FreeGroup A) :
    rawPresentation core (extra core) = FreePadding.rel (baseRel core) generatorEmbedding := by
  funext c
  cases c with
  | inl m => exact (generatorEmbedding_map_core (core m)).symm
  | inr c => rfl

theorem baseRel_isCockcroft (core : M → FreeGroup A)
    (hcore : Function.Bijective (expMatrix core)) : FSIsCockcroft (baseRel core) := by
  letI : LinearOrder A := chosenOrder A
  letI : DecidableEq A := Classical.decEq A
  exact fsIsCockcroft_relY_of_expMatrix_bijective core hcore

theorem baseRel_core_trivial (core : M → FreeGroup A)
    (hcore : Function.Surjective (expMatrix core)) (a : A) :
    (QuotientGroup.mk (FreeGroup.of (Sum.inl a)) : PresGroup (baseRel core)) = 1 := by
  letI : LinearOrder A := chosenOrder A
  letI : DecidableEq A := Classical.decEq A
  exact xEl_eq_one (r := core) (expSurjective_of_expMatrix_surjective core hcore) a

/-- The explicit initial pair is Cockcroft for arbitrary supported core
chains. The extra free generator preserves Cockcroftness by the actual
free-padding structural map and its proved generation theorem. -/
theorem isCockcroft (core : M → FreeGroup A)
    (hcore : Function.Bijective (expMatrix core)) :
    FSIsCockcroft (rawPresentation core (extra core)) := by
  rw [rawPresentation_eq_padding]
  exact fsIsCockcroft_of_generates
    (FreePadding.structuralMap (baseRel core) generatorEmbedding generatorEmbedding_injective)
    (FreePadding.structuralMap_generates (baseRel core) generatorEmbedding generatorEmbedding_injective)
    (baseRel_isCockcroft core hcore)

/-- The original core maps trivially into the actual padded initial group. -/
theorem core_trivial (core : M → FreeGroup A)
    (hcore : Function.Surjective (expMatrix core)) (a : A) :
    (QuotientGroup.mk (FreeGroup.of (Sum.inl a)) :
      PresGroup (rawPresentation core (extra core))) = 1 := by
  rw [rawPresentation_eq_padding]
  have h := congrArg (FreePadding.groupHom (baseRel core) generatorEmbedding)
    (baseRel_core_trivial core hcore a)
  rw [map_one] at h
  change (QuotientGroup.mk
    (FreeGroup.map generatorEmbedding (FreeGroup.of (Sum.inl a))) :
      PresGroup (FreePadding.rel (baseRel core) generatorEmbedding)) = 1 at h
  simpa only [FreeGroup.map.of, generatorEmbedding] using h

/-- Both initial hypotheses required by the ambient fixed-core induction,
for the explicitly supplied `extra` and `fresh` above. -/
theorem conclusions (core : M → FreeGroup A)
    (hcore : Function.Bijective (expMatrix core)) :
    FSIsCockcroft (rawPresentation core (extra core)) ∧
      ∀ a : A, (QuotientGroup.mk (FreeGroup.of (Sum.inl a)) :
        PresGroup (rawPresentation core (extra core))) = 1 :=
  ⟨isCockcroft core hcore, core_trivial core hcore.2⟩

end FiniteChains.InitialFS
