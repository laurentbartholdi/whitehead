module

public import RequestProject.GenusSpineMarking
public import RequestProject.ComponentComplex
public import RequestProject.SpanningTree

@[expose] public section

/-! The genuine connected component carrying the canonical spine marking. -/
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Davis.Genus
open Comb
variable (q : ℕ) [NeZero q]

noncomputable def markedSpineCx : Complex2 := component (genusSpineCx q) (spineBase q)

def markedSpineBase : (markedSpineCx q).V :=
  ⟨spineBase q, reach_self _ _⟩

instance : Finite (markedSpineCx q).V := by
  change Finite (CV (genusSpineCx q) (spineBase q))
  unfold CV
  infer_instance

instance : Finite (markedSpineCx q).E := by
  unfold markedSpineCx
  infer_instance

instance : Finite (markedSpineCx q).F := by
  unfold markedSpineCx
  infer_instance

theorem markedSpineCx_isConnected : IsConnected (markedSpineCx q) :=
  component_isConnected (spineBase q)

noncomputable def markedSpineLoop (x : Fin q × Bool) :
    Loop (markedSpineCx q) (markedSpineBase q) :=
  ⟨liftGerms (genusSpineCx q) (spineBase q) (spineMarkedLoop q x).1,
    isPath_liftGerms (reach_self _ _) (reach_self _ _) (spineMarkedLoop q x).2⟩

theorem markedSpineLoop_inclusion (x : Fin q × Bool) :
    mapPath (componentIncl (genusSpineCx q) (spineBase q)) (markedSpineLoop q x).1 =
      (spineMarkedLoop q x).1 := by
  exact map_cForget_liftGerms
    (reach_of_mem_path (spineMarkedLoop q x).2 (reach_self _ _))

theorem markedSpineLoop_inclusion_class (x : Fin q × Bool) :
    pi1Map (componentIncl (genusSpineCx q) (spineBase q)) (markedSpineBase q)
      (Pi1.mk (markedSpineLoop q x)) = Pi1.mk (spineMarkedLoop q x) := by
  apply congrArg Pi1.mk
  apply Subtype.ext
  exact markedSpineLoop_inclusion q x

theorem markedSpine_exists_tree :
    ∃ T : SpanningTree (markedSpineCx q), T.root = markedSpineBase q :=
  SpanningTree.exists_of_isConnected (markedSpineCx_isConnected q) (markedSpineBase q)

/-- Passing to the actual component loses no based homotopies. -/
theorem markedSpine_inclusion_pi1_injective :
    Function.Injective
      (pi1Map (componentIncl (genusSpineCx q) (spineBase q)) (markedSpineBase q)) := by
  rw (config := { transparency := .default }) [injective_iff_map_eq_one]
  rintro ⟨p⟩ hp
  have h : Htpy (genusSpineCx q) (spineBase q) (spineBase q)
      (mapPath (componentIncl (genusSpineCx q) (spineBase q)) p.1) [] :=
    Quotient.exact hp
  have hl := htpy_liftGerms (reach_self (genusSpineCx q) (spineBase q))
    (reach_self (genusSpineCx q) (spineBase q)) h
  rw (config := { transparency := .default }) [mapPath_componentIncl, liftGerms_map_cForget] at hl
  exact Quotient.sound hl

theorem markedSpine_inclusion_pi1_surjective :
    Function.Surjective
      (pi1Map (componentIncl (genusSpineCx q) (spineBase q)) (markedSpineBase q)) := by
  rintro ⟨p⟩
  let lp : Loop (markedSpineCx q) (markedSpineBase q) :=
    ⟨liftGerms (genusSpineCx q) (spineBase q) p.1,
      isPath_liftGerms (reach_self _ _) (reach_self _ _) p.2⟩
  refine ⟨Pi1.mk lp, ?_⟩
  apply congrArg Pi1.mk
  apply Subtype.ext
  exact map_cForget_liftGerms (reach_of_mem_path p.2 (reach_self _ _))

/-- The marked component has precisely the fundamental group of the full spine at its base. -/
noncomputable def markedSpinePi1Equiv :
    Pi1 (markedSpineCx q) (markedSpineBase q) ≃* Pi1 (genusSpineCx q) (spineBase q) :=
  MulEquiv.ofBijective
    (pi1Map (componentIncl (genusSpineCx q) (spineBase q)) (markedSpineBase q))
    ⟨markedSpine_inclusion_pi1_injective q, markedSpine_inclusion_pi1_surjective q⟩

end FiniteChains.Davis.Genus
