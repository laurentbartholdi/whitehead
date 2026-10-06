import RequestProject.ReceivedTreePaths

/-! A genuine regular cover on all sheets of the receiving group. -/
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb.ReceivedTree
open SpanningTree
universe u
variable {K : Complex2.{u}} (T : SpanningTree K) {G : Type u} [Group G]
  (φ : PresGroup (treeRel T) →* G)

/-- This cover has precisely the coefficient group's sheets. It can be
disconnected when the receiver is not surjective; no connectedness is asserted. -/
noncomputable def cover : Complex2.{u} where
  V := G × K.V
  E := G × K.E
  F := G × K.F
  src := src
  tgt := tgt T φ
  base f := (f.1, K.base f.2)
  att f := liftPath T φ (K.att f.2) f.1
  att_isLoop f := by
    have h := liftPath_isPath T φ (K.att_isLoop f.2) f.1
    rwa [wordValue_att, mul_one] at h

noncomputable def projection : Hom (cover T φ) K where
  onV := Prod.snd
  onE := Prod.snd
  onF := Prod.snd
  src_onE _ := rfl
  tgt_onE _ := rfl
  base_onF _ := rfl
  att_onF f := (liftPath_projection T φ (K.att f.2) f.1).symm

/-- Every oriented edge and every based face lifts uniquely. -/
theorem projection_isCovering : IsCovering (projection T φ) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro v
    exact ⟨(1, v), rfl⟩
  · rintro ⟨g, v⟩
    refine Function.bijective_iff_has_inverse.2 ⟨fun e => ⟨liftGerm T φ g e.1, ?_⟩, ?_, ?_⟩
    · show germSrc src (tgt T φ) (liftGerm T φ g e.1) = (g, v)
      rw [germSrc_liftGerm]
      exact congrArg (fun w => (g, w)) e.2
    · rintro ⟨e, he⟩
      have he' : germSrc src (tgt T φ) e = (g, v) := he
      refine Subtype.ext ?_
      obtain ⟨⟨g₁, e⟩, b⟩ := e
      cases b
      · have hg : g₁ * germValue T φ (e, true) = g := congrArg Prod.fst he'
        show liftGerm T φ g (e, false) = ((g₁, e), false)
        have hh : g * germValue T φ (e, false) = g₁ := by
          rw [← hg, mul_assoc, germValue_true_mul_false, mul_one]
        simp [liftGerm, hh]
      · have hg : g₁ = g := congrArg Prod.fst he'
        show liftGerm T φ g (e, true) = ((g₁, e), true)
        simp [liftGerm, hg]
    · rintro ⟨e, he⟩
      apply Subtype.ext
      exact liftGerm_projection T φ g e
  · refine Function.bijective_iff_has_inverse.2 ⟨fun f => (f.1.2.1, f.1.1), ?_, ?_⟩
    · rintro ⟨g, f⟩
      rfl
    · rintro ⟨⟨f, ⟨g, v⟩⟩, hv⟩
      apply Subtype.ext
      have h : K.base f = v := hv
      subst v
      rfl

noncomputable def deck : DeckAction (cover T φ) G where
  smulV h x := (h * x.1, x.2)
  smulE h x := (h * x.1, x.2)
  smulF h x := (h * x.1, x.2)
  one_smulV _ := by simp
  mul_smulV _ _ _ := by simp [mul_assoc]
  one_smulE _ := by simp
  mul_smulE _ _ _ := by simp [mul_assoc]
  one_smulF _ := by simp
  mul_smulF _ _ _ := by simp [mul_assoc]
  src_smul _ _ := rfl
  tgt_smul h x := by
    change (h * x.1 * germValue T φ (x.2, true), K.tgt x.2) =
      (h * (x.1 * germValue T φ (x.2, true)), K.tgt x.2)
    rw [mul_assoc]
  base_smul _ _ := rfl
  att_smul h f := liftPath_translate T φ (K.att f.2) h f.1

theorem projection_isRegular : IsRegular (projection T φ) (deck T φ) := by
  refine ⟨fun _ _ => rfl, ?_⟩
  rintro ⟨g, v⟩ ⟨h, w⟩ he
  have hv : v = w := he
  subst w
  refine ⟨h * g⁻¹, ?_, ?_⟩
  · change (h * g⁻¹ * g, v) = (h, v)
    simp
  · intro k hk
    have hg : k * g = h := congrArg Prod.fst hk
    rw [← hg]
    group

end FiniteChains.Comb.ReceivedTree
