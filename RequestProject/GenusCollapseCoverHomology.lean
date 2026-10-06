module

public import RequestProject.GenusOrdinaryPairCoverHomology
public import RequestProject.GenusCutPairCoverHomology
public import RequestProject.GenusCollapseIteration

@[expose] public section

/-! The entire chosen geometric collapse preserves H2 in arbitrary covers. -/
namespace FiniteChains.Davis.Genus
open RACG Mirror Comb Nerve
variable (q : ℕ) [NeZero q]
  {P : Type} [PartialOrder P] {f : P → GenusTruncatedCell q}

theorem genus_pair_cover_homology (hf : IsPosetCover f)
    (left right : List (GenusCollapsePair q)) (pair : GenusCollapsePair q)
    (hsplit : genusChainCollapse q = left ++ pair :: right) :
    GeneratesDegreeIn (fun p => genusCollapseStage q left (f p))
      (fun p => genusCollapseStage q (left ++ [pair]) (f p)) 3 ∧
    ReflectsBoundsIn (fun p => genusCollapseStage q left (f p))
      (fun p => genusCollapseStage q (left ++ [pair]) (f p)) 3 := by
  have hp : pair ∈ genusChainCollapse q := by
    rw [hsplit]
    exact List.mem_append.mpr (Or.inr List.mem_cons_self)
  obtain ⟨t, s, ht, hs⟩ := genus_pair_cells q pair hp
  have he : pair = (qCubeToCoordinate t.1, truncatedFaceIndex s) :=
    Prod.ext ht.symm hs.symm
  rw [he] at hsplit ⊢
  cases s with
  | inl s => exact genus_ordinary_pair_cover_homology q hf left right s t hsplit
  | inr σ => exact genus_recorded_cut_pair_cover_homology q hf left right σ t hsplit

/-- All intermediate comparisons use chains on the actual surviving cells. -/
theorem genus_collapse_suffix_cover_homology (hf : IsPosetCover f)
    (right left : List (GenusCollapsePair q))
    (hsplit : genusChainCollapse q = left ++ right) :
    GeneratesDegreeIn (fun p => genusCollapseStage q left (f p))
      (fun p => genusCollapseStage q (left ++ right) (f p)) 3 ∧
    ReflectsBoundsIn (fun p => genusCollapseStage q left (f p))
      (fun p => genusCollapseStage q (left ++ right) (f p)) 3 := by
  induction right generalizing left with
  | nil =>
    simp only [List.append_nil]
    constructor
    · intro z hz _ hcyc
      exact ⟨z, hz, 0, AddSubgroup.zero_mem _, hcyc, by simp⟩
    · intro c _ _ hbound
      exact hbound
  | cons pair right ih =>
    have hfirst := genus_pair_cover_homology q hf left right pair hsplit
    have htail := ih (left ++ [pair]) (by simpa only [List.append_assoc,
      List.singleton_append] using hsplit)
    have hgen := generatesDegreeIn_trans
      (fun p hp => genusCollapseStage_append_subset q left [pair] (f p) hp)
      hfirst.1 htail.1
    have href := reflectsBoundsIn_trans
      (fun p hp => genusCollapseStage_append_subset q (left ++ [pair]) right (f p) hp)
      hfirst.2 htail.2
    simpa only [List.append_assoc, List.singleton_append] using And.intro hgen href

/-- The actual surviving spine and the whole truncated block have the same H2
in every poset cover, including infinitely many sheets. This asserts both chain
generation and reflection of boundaries, with no homology premise. -/
theorem genusSpine_cover_homology (hf : IsPosetCover f) :
    GeneratesDegreeIn (fun _ : P => True) (fun p => f p ∈ genusSpineCellSet q) 3 ∧
    ReflectsBoundsIn (fun _ : P => True) (fun p => f p ∈ genusSpineCellSet q) 3 := by
  have h := genus_collapse_suffix_cover_homology q hf (genusChainCollapse q) [] (by simp)
  have hstart : (fun p => genusCollapseStage q [] (f p)) = (fun _ : P => True) := by
    funext p
    exact propext ⟨fun _ => trivial, fun _ => genusCollapseStage_nil q (f p)⟩
  have hfinish : (fun p => genusCollapseStage q ([] ++ genusChainCollapse q) (f p)) =
      (fun p => f p ∈ genusSpineCellSet q) := by
    funext p
    exact propext (by simpa only [List.nil_append] using genusCollapseStage_final_iff q (f p))
  rwa [hstart, hfinish] at h

end FiniteChains.Davis.Genus
