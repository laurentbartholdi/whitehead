module

public import RequestProject.RelativeNormalizedWords
public import RequestProject.HNNEmbedding
public import Mathlib.GroupTheory.PushoutI

@[expose] public section

/-! Simultaneous rule 1 is injective for arbitrary presentations. Independent
HNN receivers share the old group through a wide amalgam; no finite ordering
of the set of extra generators is needed. Awaiting final Lean verification.
-/

noncomputable section
open scoped Classical commutatorElement

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.RelativeNormalForm

section Receiver
variable {G : Type} [Group G]

abbrev PairReceiver (z : G) :=
  HNNExtension (Monoid.Coprod G (Multiplicative ℤ))
    (Subgroup.zpowers (freeGen (G := G)))
    (Subgroup.zpowers (Monoid.Coprod.inl z * freeGen))
    (zpowersEquivZpowers not_isOfFinOrder_freeGen (not_isOfFinOrder_mul_freeGen z))

def pairReceiverBase (z : G) : G →* PairReceiver z :=
  (HNNExtension.of : Monoid.Coprod G (Multiplicative ℤ) →* PairReceiver z).comp
    Monoid.Coprod.inl

def pairReceiverA (z : G) : PairReceiver z := HNNExtension.t
def pairReceiverB (z : G) : PairReceiver z := HNNExtension.of freeGen

theorem pairReceiver_commutator (z : G) :
    ⁅pairReceiverA z, pairReceiverB z⁆ = pairReceiverBase z z := by
  have hgen :
      (zpowersEquivZpowers not_isOfFinOrder_freeGen (not_isOfFinOrder_mul_freeGen z))
        ⟨freeGen (G := G), Subgroup.mem_zpowers _⟩ =
      ⟨Monoid.Coprod.inl z * freeGen, Subgroup.mem_zpowers _⟩ := by
    have hsymm : (zpowersEquivInt (not_isOfFinOrder_freeGen (G := G))).symm
        ⟨freeGen, Subgroup.mem_zpowers _⟩ = Multiplicative.ofAdd (1 : ℤ) := by
      rw [MulEquiv.symm_apply_eq]
      exact Subtype.ext (by simp [zpowersEquivInt])
    change (zpowersEquivInt (not_isOfFinOrder_mul_freeGen z))
      ((zpowersEquivInt not_isOfFinOrder_freeGen).symm _) = _
    rw [hsymm]
    exact Subtype.ext (by simp [zpowersEquivInt])
  have hconj := HNNExtension.equiv_eq_conj
    (φ := zpowersEquivZpowers not_isOfFinOrder_freeGen (not_isOfFinOrder_mul_freeGen z))
    ⟨freeGen (G := G), Subgroup.mem_zpowers _⟩
  rw [hgen] at hconj
  change HNNExtension.of (Monoid.Coprod.inl z * freeGen) =
    pairReceiverA z * pairReceiverB z * (pairReceiverA z)⁻¹ at hconj
  rw [map_mul] at hconj
  change pairReceiverBase z z * pairReceiverB z =
    pairReceiverA z * pairReceiverB z * (pairReceiverA z)⁻¹ at hconj
  rw [commutatorElement_def, ← hconj]
  group

theorem pairReceiverBase_injective (z : G) : Function.Injective (pairReceiverBase z) :=
  rule_one_embedding z

end Receiver

variable {A Z J : Type} (ρ : J → FreeGroup (A ⊕ Z))

def pairRel : J → FreeGroup (PairGen A Z) := fun j => pairSubstitution (ρ j)

def pairSubGroupHom : PresGroup ρ →* PresGroup (pairRel ρ) :=
  QuotientGroup.lift _ ((QuotientGroup.mk' _).comp pairSubstitution) (by
    refine Subgroup.normalClosure_le_normal ?_
    rintro _ ⟨j, rfl⟩
    exact (QuotientGroup.eq_one_iff _).mpr
      (Subgroup.subset_normalClosure ⟨j, rfl⟩))

def familyPairBase (z : Z) : PresGroup ρ →*
    PairReceiver (QuotientGroup.mk (FreeGroup.of (Sum.inr z)) : PresGroup ρ) :=
  pairReceiverBase _

abbrev PairAmalgam := Monoid.PushoutI (familyPairBase ρ)

def pairReceiverLift : FreeGroup (PairGen A Z) →* PairAmalgam ρ :=
  FreeGroup.lift (Sum.elim
    (fun a => Monoid.PushoutI.base (familyPairBase ρ)
      (QuotientGroup.mk (FreeGroup.of (Sum.inl a))))
    (fun p => Monoid.PushoutI.of p.1
      (if p.2 then pairReceiverB
        (QuotientGroup.mk (FreeGroup.of (Sum.inr p.1)) : PresGroup ρ)
       else pairReceiverA
        (QuotientGroup.mk (FreeGroup.of (Sum.inr p.1)) : PresGroup ρ))))

/-- The prescribed commutator of each pair is the corresponding original
generator in the common amalgamated base group. -/
theorem pairReceiverLift_comp :
    (pairReceiverLift ρ).comp (pairSubstitution (A := A) (Z := Z)) =
      (Monoid.PushoutI.base (familyPairBase ρ)).comp (QuotientGroup.mk' (relSub ρ)) := by
  apply FreeGroup.ext_hom
  intro x
  cases x with
  | inl a => simp [pairReceiverLift]
  | inr z =>
      simp only [MonoidHom.comp_apply, pairSubstitution_extra, map_commutatorElement]
      change ⁅Monoid.PushoutI.of (φ := familyPairBase ρ) z
          (pairReceiverA (QuotientGroup.mk (FreeGroup.of (Sum.inr z)) : PresGroup ρ)),
        Monoid.PushoutI.of (φ := familyPairBase ρ) z
          (pairReceiverB (QuotientGroup.mk (FreeGroup.of (Sum.inr z)) : PresGroup ρ))⁆ = _
      rw [← map_commutatorElement, pairReceiver_commutator]
      exact Monoid.PushoutI.of_apply_eq_base (familyPairBase ρ) z _

def pairComparison : PresGroup (pairRel ρ) →* PairAmalgam ρ :=
  QuotientGroup.lift _ (pairReceiverLift ρ) (by
    refine Subgroup.normalClosure_le_normal ?_
    rintro _ ⟨j, rfl⟩
    change pairReceiverLift ρ (pairSubstitution (ρ j)) = 1
    have h := congrArg (fun f : FreeGroup (A ⊕ Z) →* PairAmalgam ρ => f (ρ j))
      (pairReceiverLift_comp ρ)
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply] at h
    rw [h]
    have hj : (QuotientGroup.mk (ρ j) : PresGroup ρ) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (Subgroup.subset_normalClosure ⟨j, rfl⟩)
    rw [QuotientGroup.mk'_apply, hj, map_one])

theorem pairComparison_comp : (pairComparison ρ).comp (pairSubGroupHom ρ) =
    Monoid.PushoutI.base (familyPairBase ρ) := by
  apply MonoidHom.ext
  intro g
  induction g using QuotientGroup.induction_on with
  | H w =>
      exact congrArg (fun f : FreeGroup (A ⊕ Z) →* PairAmalgam ρ => f w)
        (pairReceiverLift_comp ρ)

/-- Actual simultaneous generator substitution is injective, including for
an infinite or empty family of extra generators. -/
theorem pairSubGroupHom_injective : Function.Injective (pairSubGroupHom ρ) := by
  intro g h he
  apply Monoid.PushoutI.base_injective (φ := familyPairBase ρ)
    (fun z => pairReceiverBase_injective _)
  have hc := congrArg (pairComparison ρ) he
  change ((pairComparison ρ).comp (pairSubGroupHom ρ)) g =
    ((pairComparison ρ).comp (pairSubGroupHom ρ)) h at hc
  simpa only [pairComparison_comp] using hc

end FiniteChains.RelativeNormalForm
