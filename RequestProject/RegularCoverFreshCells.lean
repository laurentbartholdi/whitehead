import RequestProject.RegularCoverAcyclicChains
import RequestProject.FreshLoopTreeStrictness

/-! The actual descended chains have stronger strictness than a generic
cellular chain: a fresh loop or a fresh face at every step. Thus tree
collapse cannot erase their strict inclusions. Pending final Lean check. -/

noncomputable section
open scoped Classical
namespace FiniteChains.Comb
universe u

namespace RelativeCellChain
variable {c : ℕ → Complex2.{u}} {n : ℕ} (R : RelativeCellChain c n)
  {K : Complex2.{u}} (p : Hom (c 0) K)

theorem descInc_freshLoopOrFace (i : ℕ) (h : FreshLoopOrFace (R.inc i)) :
    FreshLoopOrFace (R.descInc p i) := by
  rcases h with ⟨e, hloop, he⟩ | ⟨f, hf⟩
  · left
    cases i with
    | zero =>
        have hoff : ∀ d, (inclFrom c R.inc 1).onE d ≠ e := by
          intro d hd
          exact he ⟨d, hd⟩
        let w : OffE (inclFrom c R.inc 1) := ⟨e, hoff⟩
        refine ⟨Sum.inr w, ?_, ?_⟩
        · change pushV p (inclFrom c R.inc 1) ((c 1).src e) =
            pushV p (inclFrom c R.inc 1) ((c 1).tgt e)
          exact congrArg (pushV p (inclFrom c R.inc 1)) hloop
        · rintro ⟨d, hd⟩
          exact Sum.inl_ne_inr hd
    | succ i =>
        have hoff : ∀ d, (inclFrom c R.inc (i + 2)).onE d ≠ e := by
          intro d hd
          exact he ⟨(inclFrom c R.inc (i + 1)).onE d, hd⟩
        let w : OffE (inclFrom c R.inc (i + 2)) := ⟨e, hoff⟩
        refine ⟨Sum.inr w, ?_, ?_⟩
        · change pushV p (inclFrom c R.inc (i + 2)) ((c (i + 2)).src e) =
            pushV p (inclFrom c R.inc (i + 2)) ((c (i + 2)).tgt e)
          exact congrArg (pushV p (inclFrom c R.inc (i + 2))) hloop
        · rintro ⟨d, hd⟩
          cases d with
          | inl d => exact Sum.inl_ne_inr hd
          | inr d =>
              exact he ⟨d.val, pushE_eq_inr_imp p _ (R.inclE (i + 2))
                ((R.inc (i + 1)).onE d.val) w hd⟩
  · right
    cases i with
    | zero =>
        have hoff : ∀ d, (inclFrom c R.inc 1).onF d ≠ f := by
          intro d hd
          exact hf ⟨d, hd⟩
        refine ⟨Sum.inr (⟨f, hoff⟩ : OffF (inclFrom c R.inc 1)), ?_⟩
        rintro ⟨d, hd⟩
        exact Sum.inl_ne_inr hd
    | succ i =>
        have hoff : ∀ d, (inclFrom c R.inc (i + 2)).onF d ≠ f := by
          intro d hd
          exact hf ⟨(inclFrom c R.inc (i + 1)).onF d, hd⟩
        let w : OffF (inclFrom c R.inc (i + 2)) := ⟨f, hoff⟩
        refine ⟨Sum.inr w, ?_⟩
        rintro ⟨d, hd⟩
        cases d with
        | inl d => exact Sum.inl_ne_inr hd
        | inr d =>
            exact hf ⟨d.val, pushF_eq_inr_imp p _ (R.inclF (i + 2))
              ((R.inc (i + 1)).onF d.val) w hd⟩

end RelativeCellChain

namespace RelativeTreeAmbientChain
open SpanningTree RelativeNormalForm
variable {D : Complex2} (T : SpanningTree D) {n : ℕ}
  (c : AmbientChain (treeRel T) n)

theorem inclusions_freshLoopOrFace (i : ℕ) (hi : i < n + 1) :
    FreshLoopOrFace (inclusions T c i) := by
  cases i with
  | zero =>
      left
      refine ⟨Sum.inr c.fresh, rfl, ?_⟩
      rintro ⟨d, hd⟩
      exact Sum.inl_ne_inr hd
  | succ i =>
      rcases c.chain_proper (i + 1) hi with ⟨a, ha⟩ | ⟨f, hf⟩
      · exact False.elim (ha ⟨a, rfl⟩)
      · exact Or.inr ⟨f, hf⟩

end RelativeTreeAmbientChain

theorem regularCoverChain_freshLoopOrFace {D K : Complex2}
    (T : SpanningTree D) (hD : IsAcyclic D) (p : Hom D K)
    (n i : ℕ) (hi : i < n + 1) :
    FreshLoopOrFace (regularCoverChainInclusion T hD p n i) :=
  (acyclicRelativeCellChain T hD n).descInc_freshLoopOrFace p i
    (RelativeTreeAmbientChain.inclusions_freshLoopOrFace T
      (RelativeNormalForm.actualAmbientChain (SpanningTree.treeRel T)
        (SpanningTree.expMatrix_bijective_of_acyclic T hD) n) i hi)

end FiniteChains.Comb
