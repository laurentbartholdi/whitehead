import RequestProject.PuncturedCubeCoverFillings
import RequestProject.PosetCoverPuncturedLower
import RequestProject.NerveMaximalDeletion
import RequestProject.OrderNervePositiveFillings
import RequestProject.GenusOrdinaryPairCollapse

/-! The actual ordinary genus-collapse top-cell step preserves H2 in every cover. -/
namespace FiniteChains.Davis.Genus
open RACG Mirror Comb Nerve
variable (q : ℕ) [NeZero q]
  {P : Type} [PartialOrder P] {f : P → GenusTruncatedCell q}

/-- Both required lower-link fillings in the actual sheet of a lifted top cube.
Earlier collapse stages do not remove any other boundary cells. -/
theorem genus_ordinary_lifted_link_fillings (hf : IsPosetCover f)
    (left right : List (GenusCollapsePair q))
    (s t : QOld (cmpRel (GenusVertex q)))
    (hs : s.1.spx.card = 2) (ht : t.1.spx.card = 3) (hordinary : t.1.sgn ≠ 0)
    (hsplit : genusChainCollapse q = left ++
      ((qCubeToCoordinate t.1, Sum.inl (qCubeToCoordinate s.1)) :: right))
    (v : P) (hv : f v = Sum.inl t) :
    FillsDegreeIn (fun p =>
      (genusCollapseStage q left (f p) ∧ f p ≠ Sum.inl s) ∧ p < v) 2 ∧
    FillsDegreeIn (fun p =>
      (genusCollapseStage q left (f p) ∧ f p ≠ Sum.inl s) ∧ p < v) 3 := by
  let pair : GenusCollapsePair q :=
    (qCubeToCoordinate t.1, Sum.inl (qCubeToCoordinate s.1))
  have htail : qCubeToCoordinate t.1 ∈ (pair :: right).map Prod.fst := by simp [pair]
  have hcert := genusCollapseStage_suffix_certificate q left (pair :: right) hsplit
  have hi : qCubeToCoordinate t.1 ∈ spineInc (ASC.orderComplex (GenusVertex q))
      (Sum.inl (qCubeToCoordinate s.1)) := by
    have hm : qCubeToCoordinate t.1 ∈
        spineInc (ASC.orderComplex (GenusVertex q)) (Sum.inl (qCubeToCoordinate s.1)) ∩
        Collapse.remainingTops (topCubes (ASC.orderComplex (GenusVertex q))) left := by
      rw [hcert.2.1]
      exact Finset.mem_singleton_self _
    exact (Finset.mem_inter.mp hm).1
  let e : {x : GenusTruncatedCell q // x < f v ∧ x ≠ Sum.inl s} ≃o
      OldPuncturedBoundary s t := {
    toFun := fun x => ⟨x.1, hv ▸ x.2.1, x.2.2⟩
    invFun := fun x => ⟨x.1, hv.symm ▸ x.2.1, x.2.2⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_rel_iff' := by intros; rfl }
  have hcover := (hf.puncturedLower_isPosetCover v (Sum.inl s)).postcompose_orderIso e
  have hfill := ordinaryTruncatedBoundary_cover_fillings hordinary hi hcover
  have hne : ∃ p : P, p < v ∧ f p ≠ Sum.inl s := by
    obtain ⟨x, hxs, hxt⟩ := genus_top_boundary_nonempty q (Sum.inl s) hs t ht
    obtain ⟨p, hp⟩ := hcover.surj ⟨x, hxt, hxs⟩
    exact ⟨p.1, p.2⟩
  have he (p : P) : (p < v ∧ f p ≠ Sum.inl s) ↔
      (genusCollapseStage q left (f p) ∧ f p ≠ Sum.inl s) ∧ p < v := by
    constructor
    · rintro ⟨hpv, hps⟩
      refine ⟨⟨genusCollapseStage_boundary_mem q left (pair :: right) hsplit t htail
        (f p) ?_, hps⟩, hpv⟩
      rw [← hv]
      exact hf.strictMono hpv
    · exact fun h => ⟨h.2, h.1.2⟩
  constructor
  · apply fillsDegreeIn_congr he
    apply fillsDegreeIn_of_subtype hne
    exact nerve_oneCycle_filling_of_strict hfill.1
  · apply fillsDegreeIn_congr he
    apply fillsDegreeIn_of_subtype hne
    exact nerve_twoCycle_filling_of_strict hfill.2

/-- Deleting one actual lifted ordinary top cell, after deleting its free-face
fiber, gives both surjectivity and injectivity on H2 by explicit finite chains. -/
theorem genus_ordinary_lifted_top_homology (hf : IsPosetCover f)
    (left right : List (GenusCollapsePair q))
    (s t : QOld (cmpRel (GenusVertex q)))
    (hs : s.1.spx.card = 2) (ht : t.1.spx.card = 3) (hordinary : t.1.sgn ≠ 0)
    (hsplit : genusChainCollapse q = left ++
      ((qCubeToCoordinate t.1, Sum.inl (qCubeToCoordinate s.1)) :: right))
    (v : P) (hv : f v = Sum.inl t) :
    let C := fun p => genusCollapseStage q left (f p) ∧ f p ≠ Sum.inl s
    GeneratesDegreeIn C (fun p => C p ∧ p ≠ v) 3 ∧
      ReflectsBoundsIn C (fun p => C p ∧ p ≠ v) 3 := by
  let pair : GenusCollapsePair q :=
    (qCubeToCoordinate t.1, Sum.inl (qCubeToCoordinate s.1))
  have htail : qCubeToCoordinate t.1 ∈ (pair :: right).map Prod.fst := by simp [pair]
  have hcert := genusCollapseStage_suffix_certificate q left (pair :: right) hsplit
  have htC : genusCollapseStage q left (Sum.inl t) :=
    ⟨genus_later_top_boundary_avoids_prefix_faces q left (pair :: right) hsplit
      (Sum.inl t) t htail (le_refl _),
      ((Collapse.mem_remainingTops _ _ _).mp hcert.1).2⟩
  let C := fun p => genusCollapseStage q left (f p) ∧ f p ≠ Sum.inl s
  have hvC : C v := by
    refine ⟨hv ▸ htC, ?_⟩
    rw [hv]
    intro he
    have hdim := congrArg (fun c : QOld (cmpRel (GenusVertex q)) => c.1.spx.card)
      (Sum.inl.inj he)
    change t.1.spx.card = s.1.spx.card at hdim
    omega
  have hmax : ∀ p, C p → v ≤ p → p = v := by
    intro p _ hvp
    have hp : f p = Sum.inl t := genus_top_cell_maximal q t ht (f p)
      (by rw [← hv]; exact hf.mono hvp)
    exact (hf.up_inj (le_refl v) hvp (hv.trans hp.symm)).symm
  have hlink := genus_ordinary_lifted_link_fillings q hf left right s t hs ht hordinary
    hsplit v hv
  exact ⟨generatesDegreeIn_delete_maximal hvC hmax hlink.1,
    reflectsBoundsIn_delete_maximal hmax hlink.2⟩

end FiniteChains.Davis.Genus
