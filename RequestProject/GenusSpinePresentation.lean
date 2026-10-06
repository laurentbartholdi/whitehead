import RequestProject.GenusSpineSurfaceFilling
import RequestProject.GenusSpineComponent
import RequestProject.TreePresentation

/-! A finite presentation read from the actual connected marked genus spine. -/
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb
variable (q : ℕ) [NeZero q]

theorem markedSpineLoop_hfilling :
    commWord (fun x : Fin q × Bool => Pi1.mk (markedSpineLoop q x))
      (finitePairs q) = 1 := by
  apply markedSpine_inclusion_pi1_injective q
  rw [map_one, map_commWord,
    commWord_congr (markedSpineLoop_inclusion_class q)]
  exact spineMarkedLoop_hfilling q

theorem markedSpineSurfacePath_nullhomotopic :
    Htpy (markedSpineCx q) (markedSpineBase q) (markedSpineBase q)
      (surfacePath (markedSpineLoop q) (finitePairs q)) [] :=
  surfacePath_nullhomotopic _ _ (markedSpineLoop_hfilling q)

noncomputable def markedSpineTree : SpanningTree (markedSpineCx q) :=
  Classical.choose (markedSpine_exists_tree q)

theorem markedSpineTree_root : (markedSpineTree q).root = markedSpineBase q :=
  Classical.choose_spec (markedSpine_exists_tree q)

abbrev SpinePresentationGen := SpanningTree.NonTree (markedSpineTree q)
abbrev SpinePresentationRel := (markedSpineCx q).F

instance : Finite (SpinePresentationGen q) := inferInstance
instance : Finite (SpinePresentationRel q) := inferInstance

noncomputable def spinePresentation : SpinePresentationRel q → FreeGroup (SpinePresentationGen q) :=
  SpanningTree.treeRel (markedSpineTree q)

noncomputable def spinePresentationPi1Equiv :
    Pi1 (markedSpineCx q) (markedSpineTree q).root ≃* PresGroup (spinePresentation q) :=
  SpanningTree.pi1EquivPres (markedSpineTree q)

noncomputable def spinePresentationMarkedWord (x : Fin q × Bool) :
    FreeGroup (SpinePresentationGen q) :=
  SpanningTree.pathWord (markedSpineTree q) (markedSpineLoop q x).1

/-- Reading a surface path in the genuine spanning-tree presentation preserves its word. -/
theorem pathWord_surfacePath {X : Complex2} {a : X.V} {ι : Type}
    (T : SpanningTree X) (f : ι → Loop X a) (ps : List (ι × ι)) :
    SpanningTree.pathWord T (surfacePath f ps) =
      commWord (fun i => SpanningTree.pathWord T (f i).1) ps := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    simp only [surfacePath, SpanningTree.pathWord_append, SpanningTree.pathWord_revPath,
      ih, commWord_cons]

/-- The marked relation holds in this actual finite cell presentation. -/
theorem spinePresentationMarkedWord_hfilling :
    commWord (fun x => (QuotientGroup.mk' (relSub (spinePresentation q)))
      (spinePresentationMarkedWord q x)) (finitePairs q) = 1 := by
  have h := SpanningTree.wordClass_htpy (markedSpineTree q)
    (markedSpineSurfacePath_nullhomotopic q)
  change (QuotientGroup.mk' (relSub (spinePresentation q)))
      (SpanningTree.pathWord (markedSpineTree q)
        (surfacePath (markedSpineLoop q) (finitePairs q))) = 1 at h
  rw [pathWord_surfacePath, map_commWord] at h
  exact h

/-- Attach a disk along each of the genuine marked words. -/
noncomputable def cappedSpinePresentation :
    SpinePresentationRel q ⊕ (Fin q × Bool) → FreeGroup (SpinePresentationGen q)
  | .inl f => spinePresentation q f
  | .inr x => spinePresentationMarkedWord q x

end FiniteChains.Davis.Genus
