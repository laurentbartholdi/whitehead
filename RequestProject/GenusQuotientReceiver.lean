import RequestProject.ChamberQuotientCocycleGluing
import RequestProject.GenusReceivedSpineCover
import RequestProject.PresUniversalGroupCoordinates
import RequestProject.GenusNonemptyMarkedReading

/-! Construct the old-piece cocycle from the actual finite-spine receiver,
then glue it to a base receiver using only the genuine marked readings.
This source is part of the pending reverse-comparison proof.
-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb.OrdCocycle
open SpanningTree
open scoped Classical
universe u v
variable {P : Type u} [Preorder P] {G : Type v} [Group G]
  (T : SpanningTree (orderCx P)) (φ : PresGroup (treeRel T) →* G)

noncomputable def fromTreeReceiver : OrdCocycle P G where
  val a b := if hab : a ≤ b then φ (wordClass T [ordPos hab]) else 1
  comp := by
    intro a b c hab hbc
    simp only [dif_pos hab, dif_pos hbc, dif_pos (hab.trans hbc)]
    rw [← map_mul, ← wordClass_append]
    exact congrArg φ (wordClass_htpy T (htpy_orderCx_tri hab hbc))

theorem fromTreeReceiver_readGerm (e : (orderCx P).E × Bool) :
    (fromTreeReceiver T φ).readGerm e = φ (wordClass T [e]) := by
  obtain ⟨⟨⟨a, b⟩, hab⟩, side⟩ := e
  cases side
  · change (if h : a ≤ b then φ (wordClass T [ordPos h]) else 1)⁻¹ =
      φ (wordClass T [ordNeg hab])
    rw [dif_pos hab]
    have hr : wordClass T [ordNeg hab] = (wordClass T [ordPos hab])⁻¹ := by
      change QuotientGroup.mk (pathWord T [ordNeg hab]) =
        (QuotientGroup.mk (pathWord T [ordPos hab]))⁻¹
      rw [← QuotientGroup.mk_inv, ← pathWord_revPath]
      rfl
    rw [hr, map_inv]
  · change (if h : a ≤ b then φ (wordClass T [ordPos h]) else 1) = _
    rw [dif_pos hab]
    rfl

theorem fromTreeReceiver_readPath (p : List ((orderCx P).E × Bool)) :
    (fromTreeReceiver T φ).readPath p = φ (wordClass T p) := by
  induction p with
  | nil => simp [wordClass, pathWord_nil]
  | cons e p ih =>
    rw [readPath_cons, fromTreeReceiver_readGerm, ih, ← map_mul, ← wordClass_append]
    rfl

/-- Every actual fundamental-group homomorphism is realized by a cocycle.
The spanning tree is constructed from connectedness and has the prescribed root. -/
theorem exists_of_monodromy (hP : IsConnected (orderCx P)) (x : P)
    (ψ : Pi1 (orderCx P) x →* G) :
    ∃ c : OrdCocycle P G, ∀ p : Loop (orderCx P) x,
      c.readPath p.1 = ψ (Pi1.mk p) := by
  obtain ⟨T, hT⟩ := SpanningTree.exists_of_isConnected hP x
  subst x
  refine ⟨fromTreeReceiver T (ψ.comp (SpanningTree.presToPi1 T)), ?_⟩
  intro p
  rw [fromTreeReceiver_readPath]
  change ψ (SpanningTree.presToPi1 T (SpanningTree.pi1ToPres T (Pi1.mk p))) = _
  rw [SpanningTree.presToPi1_pi1ToPres]

end FiniteChains.Comb.OrdCocycle

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb BlockFamily
universe v
variable (q₀ : ℕ) [NeZero q₀] {G : Type v} [Group G]
  (φ : PresGroup (namedSpinePresentation q₀) →* G)

noncomputable def oldSpineReceiver :
    Pi1 (orderCx (QOld (cmpRel (GenusVertex q₀)))) (posQCube (gBase q₀)) →* G :=
  φ.comp (namedSpineToOldEquiv q₀).symm.toMonoidHom

theorem oldSpineReceiver_marked (x : Fin q₀ × Bool) :
    oldSpineReceiver q₀ φ
      (Pi1.mk ⟨mapPath (surfCx (cmpRel (GenusVertex q₀)))
        (gSig q₀ (x.1.val, x.2)),
        isPath_mapPath (surfCx _) (isPath_gSig q₀ (x.1.val, x.2))⟩) =
      φ (QuotientGroup.mk (FreeGroup.of (Sum.inr x))) := by
  have hm := namedSpineToOld_marked q₀ x
  rw [spineMarkedLoop_toOld_class] at hm
  change φ ((namedSpineToOldEquiv q₀).symm _) = _
  rw [← hm, MulEquiv.symm_apply_apply]

/-- The receiver is carried by an actual cocycle on the old geometric block;
the standard surface loops read the exact distinguished names. -/
theorem exists_oldSpineCocycle :
    ∃ c : OrdCocycle (QOld (cmpRel (GenusVertex q₀))) G,
      (∀ p : Loop (orderCx (QOld (cmpRel (GenusVertex q₀)))) (posQCube (gBase q₀)),
        c.readPath p.1 = oldSpineReceiver q₀ φ (Pi1.mk p)) ∧
      ∀ x : Fin q₀ × Bool,
        c.readPath (mapPath (surfCx (cmpRel (GenusVertex q₀)))
          (gSig q₀ (x.1.val, x.2))) =
          φ (QuotientGroup.mk (FreeGroup.of (Sum.inr x))) := by
  letI : Nonempty (GenusVertex q₀) := ⟨cV (gc q₀) (cyc (8 * q₀) 0)⟩
  obtain ⟨c, hread⟩ := OrdCocycle.exists_of_monodromy isConnected_orderCx_qOld
    (posQCube (gBase q₀))
    (oldSpineReceiver q₀ φ)
  refine ⟨c, hread, ?_⟩
  intro x
  rw [hread ⟨_, isPath_mapPath (surfCx _) (isPath_gSig q₀ (x.1.val, x.2))⟩]
  exact oldSpineReceiver_marked q₀ φ x

/-- Given the actual readings of the base, the reverse receiver extends over
the whole geometric quotient and has the prescribed homomorphism on old loops. -/
theorem exists_quotientReceiver {X : Type} [Preorder X]
    (att : NeSpx (cmpRel (GenusVertex q₀)) →o X) (base : OrdCocycle X G)
    (hbase : ∀ x : Fin q₀ × Bool,
      base.readPath (mapPath (orderCxMap att att.monotone) (gSig q₀ (x.1.val, x.2))) =
        φ (QuotientGroup.mk (FreeGroup.of (Sum.inr x)))) :
    ∃ c : OrdCocycle (Qpos (cmpRel (GenusVertex q₀)) X att) G,
      (∀ x y, c.val (qNew x) (qNew y) = base.val x y) ∧
      c.val (qNew (att (gBase q₀))) (qOldIncl (posQCube (gBase q₀))) = 1 ∧
      ∀ p : Loop (orderCx (QOld (cmpRel (GenusVertex q₀)))) (posQCube (gBase q₀)),
        c.readPath (mapPath (orderCxMap (qOldIncl (att := att)) qOldIncl_monotone) p.1) =
          oldSpineReceiver q₀ φ (Pi1.mk p) := by
  obtain ⟨old, hread, hmark⟩ := exists_oldSpineCocycle q₀ φ
  obtain ⟨c, hcold, hcbase, hccyl⟩ := exists_quotientCocycle_of_marked q₀ att old base
    (fun x => (hmark x).trans (hbase x).symm)
  refine ⟨c, hcbase, hccyl, ?_⟩
  intro p
  have he : c.comap (qOldIncl (att := att)) qOldIncl_monotone = old :=
    OrdCocycle.eq_of_val_eq hcold
  rw [← OrdCocycle.comap_readPath, he]
  exact hread p

variable {A Jr S : Type} (ρ : Jr ⊕ S → FreeGroup A)
  (q : S → ℕ) [∀ s, NeZero (q s)] (u : ∀ s, Fin (q s) × Bool → FreeGroup A)

/-- In the actual simultaneously substituted group, the old-piece receiver
reads each marked loop as the specified old word, with no injectivity premise. -/
theorem exists_receivedOldCocycle (s : S) :
    ∃ c : OrdCocycle (QOld (cmpRel (GenusVertex (q s))))
        (PresGroup (substPresF ρ (familyFiniteSpineWordBlock q u))),
      (∀ p : Loop (orderCx (QOld (cmpRel (GenusVertex (q s))))) (posQCube (gBase (q s))),
        c.readPath p.1 = oldSpineReceiver (q s) (familySpineHom ρ q u s) (Pi1.mk p)) ∧
      ∀ x : Fin (q s) × Bool,
        c.readPath (mapPath (surfCx (cmpRel (GenusVertex (q s))))
          (gSig (q s) (x.1.val, x.2))) =
          QuotientGroup.mk (FreeGroup.map
            (Sum.inl (β := Σ s, SpinePresentationGen (q s))) (u s x)) := by
  obtain ⟨c, hc, hm⟩ := exists_oldSpineCocycle (q s) (familySpineHom ρ q u s)
  refine ⟨c, hc, ?_⟩
  intro x
  rw [hm, familySpineHom_marked]

end FiniteChains.Davis.Genus

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb PresModel BlockFamily
universe v
variable {α Jr : Type} (ρ : Jr ⊕ PUnit.{1} → FreeGroup α)
  (q : ℕ) [NeZero q] (u : Fin q × Bool → FreeGroup α)
  (hrho : ρ (Sum.inr PUnit.unit) = commWord u (finitePairs q))
  {G : Type v} [Group G] (j : PresGroup ρ →* G)

/-- The receiver on the named base presentation is the original receiver
after the proved elimination of the auxiliary names. -/
noncomputable def namedBaseReceiver : PresGroup (namedPres ρ q u) →* G :=
  j.comp (SurfaceWordExpansion.elimination ρ u (finitePairs q) hrho)

omit [NeZero q] in
theorem namedBaseReceiver_marked (x : Fin q × Bool) :
    namedBaseReceiver ρ q u hrho j (QuotientGroup.mk (FreeGroup.of (Sum.inr x))) =
      j (QuotientGroup.mk (u x)) := by
  change j (QuotientGroup.mk
    (SurfaceWordExpansion.foldNames u (FreeGroup.of (Sum.inr x)))) = _
  simp only [SurfaceWordExpansion.foldNames, FreeGroup.lift_apply_of, Sum.elim_inr]

noncomputable def namedBaseCocycle :
    OrdCocycle (PresPos (genusNonemptyW (namedPres ρ q u) (namedA (α := α) q)
      (namedB (α := α) q) q)) G :=
  (presGroupCocycle (namedPres ρ q u)
    (genusNonemptyW (namedPres ρ q u) (namedA (α := α) q) (namedB (α := α) q) q)
    (mk_genusNonemptyW _ _ _ _ (namedPres_surface ρ q u))).postcompose
      (namedBaseReceiver ρ q u hrho j)

theorem namedBaseCocycle_marked (x : Fin q × Bool) :
    (namedBaseCocycle ρ q u hrho j).readPath
      (mapPath (orderCxMap
        (genusNonemptyAtt (namedPres ρ q u) (namedA (α := α) q) (namedB (α := α) q) q)
        (genusNonemptyAtt (namedPres ρ q u) (namedA (α := α) q) (namedB (α := α) q) q).monotone)
        (gSig q (x.1.val, x.2))) = j (QuotientGroup.mk (u x)) := by
  let ep := namedPres ρ q u
  let aa := namedA (α := α) q
  let bb := namedB (α := α) q
  let w := genusNonemptyW ep aa bb q
  have hh := (namedBaseCocycle ρ q u hrho j).readPath_htpy
    (genusNonempty_hread ep aa bb q PUnit.unit.{1} (x.1.val, x.2))
  simp only [List.nil_append, revPath_nil, List.append_nil] at hh
  rw [hh]
  have hl : genusLw aa bb q PUnit.unit.{1} (x.1.val, x.2) = [(Sum.inr x, true)] :=
    namedLw_eq q PUnit.unit x
  rw [hl]
  change (namedBaseCocycle ρ q u hrho j).readPath (genLoop w (Sum.inr x)) = _
  rw [namedBaseCocycle, OrdCocycle.postcompose_readPath]
  change namedBaseReceiver ρ q u hrho j
    (reading w (fun a => (QuotientGroup.mk (FreeGroup.of a) : PresGroup ep))
      (presGroup_wordVal_eq_one ep w (mk_genusNonemptyW _ _ _ _ (namedPres_surface ρ q u)))
      (genClass w (Sum.inr x))) = _
  rw [reading_genClass]
  exact namedBaseReceiver_marked ρ q u hrho j x

/-- Concrete gluing over the prescribed word model. All base relators and
the surface comparison are discharged by the original word relation and
the exact distinguished-name agreement, rather than assumed presentations. -/
theorem exists_namedQuotientReceiver
    (φ : PresGroup (namedSpinePresentation q) →* G)
    (hm : ∀ x : Fin q × Bool,
      φ (QuotientGroup.mk (FreeGroup.of (Sum.inr x))) = j (QuotientGroup.mk (u x))) :
    ∃ c : OrdCocycle (Qpos (cmpRel (GenusVertex q))
        (PresPos (genusNonemptyW (namedPres ρ q u) (namedA (α := α) q) (namedB (α := α) q) q))
        (genusNonemptyAtt (namedPres ρ q u) (namedA (α := α) q) (namedB (α := α) q) q)) G,
      (∀ x y, c.val (qNew x) (qNew y) = (namedBaseCocycle ρ q u hrho j).val x y) ∧
      c.val
        (qNew (genusNonemptyAtt (namedPres ρ q u) (namedA (α := α) q) (namedB (α := α) q) q
          (gBase q))) (qOldIncl (posQCube (gBase q))) = 1 ∧
      ∀ p : Loop (orderCx (QOld (cmpRel (GenusVertex q)))) (posQCube (gBase q)),
        c.readPath (mapPath
          (orderCxMap (qOldIncl (att := genusNonemptyAtt (namedPres ρ q u)
            (namedA (α := α) q) (namedB (α := α) q) q)) qOldIncl_monotone) p.1) =
          oldSpineReceiver q φ (Pi1.mk p) := by
  apply exists_quotientReceiver q φ _ (namedBaseCocycle ρ q u hrho j)
  intro x
  exact (namedBaseCocycle_marked ρ q u hrho j x).trans (hm x).symm

noncomputable abbrev namedQuotientPos :=
  Qpos (cmpRel (GenusVertex q))
    (PresPos (genusNonemptyW (namedPres ρ q u) (namedA (α := α) q) (namedB (α := α) q) q))
    (genusNonemptyAtt (namedPres ρ q u) (namedA (α := α) q) (namedB (α := α) q) q)

noncomputable abbrev namedQuotientBase : namedQuotientPos ρ q u :=
  qNew (genusNonemptyAtt (namedPres ρ q u) (namedA (α := α) q) (namedB (α := α) q) q
    (gBase q))

noncomputable def namedSpineIntoQuotient :
    PresGroup (namedSpinePresentation q) →*
      Pi1 (orderCx (namedQuotientPos ρ q u)) (namedQuotientBase ρ q u) :=
  (quotientOldBasedInclusion (gBase q)).comp (namedSpineToOldEquiv q).toMonoidHom

/-- A reverse homomorphism on the actual geometric fundamental group, with
its full action on the named spine and on the base proved simultaneously.
This is stronger than agreement merely on distinguished marked generators. -/
theorem exists_namedQuotientReading
    (φ : PresGroup (namedSpinePresentation q) →* G)
    (hm : ∀ x : Fin q × Bool,
      φ (QuotientGroup.mk (FreeGroup.of (Sum.inr x))) = j (QuotientGroup.mk (u x))) :
    ∃ ψ : Pi1 (orderCx (namedQuotientPos ρ q u)) (namedQuotientBase ρ q u) →* G,
      ψ.comp (namedSpineIntoQuotient ρ q u) = φ ∧
      ψ.comp
        (pi1Map (orderCxMap (qNew (att := genusNonemptyAtt (namedPres ρ q u)
          (namedA (α := α) q) (namedB (α := α) q) q)) qNew_monotone)
          (genusNonemptyAtt (namedPres ρ q u) (namedA (α := α) q) (namedB (α := α) q) q
            (gBase q))) =
        (namedBaseCocycle ρ q u hrho j).monodromy
          (genusNonemptyAtt (namedPres ρ q u) (namedA (α := α) q) (namedB (α := α) q) q
            (gBase q)) := by
  obtain ⟨c, hb, he, ho⟩ := exists_namedQuotientReceiver ρ q u hrho j φ hm
  refine ⟨c.monodromy (namedQuotientBase ρ q u), ?_, ?_⟩
  · have h := monodromy_quotientOldBasedInclusion (gBase q) c
      (oldSpineReceiver q φ) he ho
    change ((c.monodromy (namedQuotientBase ρ q u)).comp
      (quotientOldBasedInclusion (gBase q))).comp (namedSpineToOldEquiv q).toMonoidHom = φ
    rw [h]
    apply MonoidHom.ext
    intro z
    change φ ((namedSpineToOldEquiv q).symm ((namedSpineToOldEquiv q) z)) = φ z
    rw [MulEquiv.symm_apply_apply]
  · exact monodromy_quotientBaseInclusion _ c (namedBaseCocycle ρ q u hrho j) hb

end FiniteChains.Davis.Genus
