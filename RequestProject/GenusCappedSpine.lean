module

public import RequestProject.GenusSpinePresentation

@[expose] public section

/-! The genuine finite complex obtained by capping the marked surviving spine. -/
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb
variable (q : ℕ) [NeZero q]

noncomputable def cappedSpineCx : Complex2 where
  V := (markedSpineCx q).V
  E := (markedSpineCx q).E
  F := (markedSpineCx q).F ⊕ (Fin q × Bool)
  src := (markedSpineCx q).src
  tgt := (markedSpineCx q).tgt
  base := Sum.elim (markedSpineCx q).base (fun _ => markedSpineBase q)
  att := Sum.elim (markedSpineCx q).att (fun x => (markedSpineLoop q x).1)
  att_isLoop := by
    rintro (f | x)
    · exact (markedSpineCx q).att_isLoop f
    · exact (markedSpineLoop q x).2

instance : Finite (cappedSpineCx q).V := inferInstanceAs (Finite (markedSpineCx q).V)
instance : Finite (cappedSpineCx q).E := inferInstanceAs (Finite (markedSpineCx q).E)
instance : Finite (cappedSpineCx q).F :=
  inferInstanceAs (Finite ((markedSpineCx q).F ⊕ (Fin q × Bool)))

theorem cappedSpineCx_connected : IsConnected (cappedSpineCx q) :=
  markedSpineCx_isConnected q

noncomputable def cappedSpineTree : SpanningTree (cappedSpineCx q) where
  root := (markedSpineTree q).root
  ht := (markedSpineTree q).ht
  isTree := (markedSpineTree q).isTree
  up := (markedSpineTree q).up
  ht_root := (markedSpineTree q).ht_root
  ht_eq_zero := (markedSpineTree q).ht_eq_zero
  up_src := (markedSpineTree q).up_src
  up_ht := (markedSpineTree q).up_ht
  isTree_iff := (markedSpineTree q).isTree_iff

/-- The capped presentation is precisely the cell presentation of the capped complex. -/
theorem cappedSpineTree_rel :
    SpanningTree.treeRel (cappedSpineTree q) = cappedSpinePresentation q := by
  funext f
  cases f <;> rfl

noncomputable def cappedSpinePi1Equiv :
    Pi1 (cappedSpineCx q) (cappedSpineTree q).root ≃*
      PresGroup (cappedSpinePresentation q) := by
  rw [← cappedSpineTree_rel]
  exact SpanningTree.pi1EquivPres (cappedSpineTree q)

noncomputable def cappedSpineIncl : Hom (markedSpineCx q) (cappedSpineCx q) where
  onV := id
  onE := id
  onF := Sum.inl
  src_onE _ := rfl
  tgt_onE _ := rfl
  base_onF _ := rfl
  att_onF f := by
    change (markedSpineCx q).att f = List.map (fun eb : (markedSpineCx q).E × Bool => (eb.1, eb.2))
      ((markedSpineCx q).att f)
    simp

theorem cappedSpineMarkedLoop_nullhomotopic (x : Fin q × Bool) :
    Htpy (cappedSpineCx q) (markedSpineBase q) (markedSpineBase q)
      (mapPath (cappedSpineIncl q) (markedSpineLoop q x).1) [] := by
  apply Htpy.of_step
  refine ⟨isPath_mapPath (cappedSpineIncl q) (markedSpineLoop q x).2, rfl, Or.inr ?_⟩
  refine ⟨[], [], Sum.inr x, ?_, rfl⟩
  simp [mapPath, cappedSpineIncl, cappedSpineCx]

theorem cappedSpineMarkedLoop_class (x : Fin q × Bool) :
    pi1Map (cappedSpineIncl q) (markedSpineBase q) (Pi1.mk (markedSpineLoop q x)) = 1 :=
  Quotient.sound (cappedSpineMarkedLoop_nullhomotopic q x)

end FiniteChains.Davis.Genus
