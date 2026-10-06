module

public import RequestProject.CutPuncturedBoundaryAcyclic
public import RequestProject.GenusCutPairCollapse
public import RequestProject.PosetCoverPuncturedLower
public import RequestProject.NerveDegreeTransfer

@[expose] public section

/-! Fillings in the actual sheet of a top cube paired with its cut facet. -/
namespace FiniteChains.Davis.Genus
open RACG Mirror Comb Nerve
variable (q : ℕ) [NeZero q]
  {P : Type} [PartialOrder P] {f : P → GenusTruncatedCell q}

theorem genus_cut_lifted_link_fillings (hf : IsPosetCover f)
    (left right : List (GenusCollapsePair q))
    (t : QOld (cmpRel (GenusVertex q))) (hne : t.1.spx.Nonempty)
    (ht : t.1.spx.card = 3) (hpositive : t.1.sgn = 0)
    (hsplit : genusChainCollapse q = left ++
      ((qCubeToCoordinate t.1, Sum.inr t.1.spx) :: right))
    (v : P) (hv : f v = Sum.inl t) (n : ℕ) :
    FillsDegreeIn (fun p =>
      (genusCollapseStage q left (f p) ∧ f p ≠ Sum.inr (fullCutCell t hne)) ∧ p < v) n := by
  let pair : GenusCollapsePair q := (qCubeToCoordinate t.1, Sum.inr t.1.spx)
  have htail : qCubeToCoordinate t.1 ∈ (pair :: right).map Prod.fst := by simp [pair]
  let e : {x : GenusTruncatedCell q // x < f v ∧ x ≠ Sum.inr (fullCutCell t hne)} ≃o
      CutPuncturedBoundary t hne := {
    toFun := fun x => ⟨x.1, hv ▸ x.2.1, x.2.2⟩
    invFun := fun x => ⟨x.1, hv.symm ▸ x.2.1, x.2.2⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_rel_iff' := by intros; rfl }
  let E := (hf.puncturedLowerOrderIso v (Sum.inr (fullCutCell t hne))).trans e
  have hfill := exists_bdry_eq_of_cycle_of_orderIso E
    (positiveCutPuncturedBoundary_acyclic t hne hpositive ht)
  have hnonempty : ∃ p : P, p < v ∧ f p ≠ Sum.inr (fullCutCell t hne) := by
    have hdim : truncatedCellDimension (Sum.inr (fullCutCell t hne) : GenusTruncatedCell q) = 2 := by
      change t.1.spx.card - 1 = 2
      omega
    obtain ⟨x, hxs, hxt⟩ := genus_top_boundary_nonempty q (Sum.inr (fullCutCell t hne))
      hdim t ht
    exact ⟨(E.symm ⟨x, hxt, hxs⟩).1, (E.symm ⟨x, hxt, hxs⟩).2⟩
  have he (p : P) : (p < v ∧ f p ≠ Sum.inr (fullCutCell t hne)) ↔
      (genusCollapseStage q left (f p) ∧ f p ≠ Sum.inr (fullCutCell t hne)) ∧ p < v := by
    constructor
    · rintro ⟨hpv, hps⟩
      refine ⟨⟨genusCollapseStage_boundary_mem q left (pair :: right) hsplit t htail
        (f p) ?_, hps⟩, hpv⟩
      rw [← hv]
      exact hf.strictMono hpv
    · exact fun h => ⟨h.2, h.1.2⟩
  apply fillsDegreeIn_congr he
  apply fillsDegreeIn_of_subtype hnonempty
  exact fun c hc _ hcyc => hfill c hc hcyc

end FiniteChains.Davis.Genus
