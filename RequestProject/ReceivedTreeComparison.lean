import RequestProject.ReceivedTreeGauge
import RequestProject.CellularHomotopyChain
import RequestProject.ComponentComplex

/-! A constructed cellular comparison, including the lifted attaching paths. -/
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb.ReceivedTree
open SpanningTree
universe u
variable {K Y : Complex2.{u}} (T : SpanningTree K) (f : Hom K Y)
  {G : Type u} [Group G] (φ : PresGroup (treeRel T) →* G)
  (ψ : G →* Pi1 Y (f.onV T.root))
  (hψ : ψ.comp φ = (pi1Map f T.root).comp (SpanningTree.presToPi1 T))

noncomputable def receiverGerm (e : (G × K.E) × Bool) : UE Y (f.onV T.root) × Bool :=
  (receiverEdge T f ψ e.1.1 e.1.2, e.2)

include hψ in
theorem comparison_liftGerm (g : G) (e : K.E × Bool) :
    receiverGerm T f ψ (liftGerm T φ g e) =
      Comb.liftGerm (receiverVertex T f ψ g (germSrc K.src K.tgt e))
        (f.onE e.1, e.2) (by rw [receiverVertex_end, germSrc_onE]) := by
  obtain ⟨e, b⟩ := e
  cases b with
  | true => rfl
  | false =>
    have h := receiverVertex_path T f φ ψ hψ g (isPath_single (X := K) (e, false))
    have he : extend (f.onE e, false) (receiverVertex T f ψ g (K.tgt e)) =
        receiverVertex T f ψ (g * germValue T φ (e, false)) (K.src e) := by
      simpa only [mapPath, List.map_cons, List.map_nil, extendList_cons, extendList_nil,
        wordValue_cons, wordValue_nil, mul_one, germSrc, germTgt, Bool.false_eq_true, if_false] using h
    apply Prod.ext
    · apply Subtype.ext
      apply Prod.ext
      · exact he.symm
      · rfl
    · rfl

include hψ in
/-- Every actual lifted edge path has the claimed geometric image. -/
theorem comparison_liftPath (g : G) {a b : K.V} {p : List (K.E × Bool)}
    (hp : IsPath K.src K.tgt p a b) :
    (liftPath T φ p g).map (receiverGerm T f ψ) =
      uLiftPath (mapPath f p) (receiverVertex T f ψ g a) := by
  induction p generalizing a g with
  | nil => rfl
  | cons e p ih =>
    obtain ⟨ha, hp⟩ := hp
    subst a
    have hs : endV (receiverVertex T f ψ g (germSrc K.src K.tgt e)) =
        germSrc Y.src Y.tgt (f.onE e.1, e.2) := by
      rw [receiverVertex_end, germSrc_onE]
    have he : extend (f.onE e.1, e.2)
        (receiverVertex T f ψ g (germSrc K.src K.tgt e)) =
        receiverVertex T f ψ (g * germValue T φ e) (germTgt K.src K.tgt e) := by
      have h := receiverVertex_path T f φ ψ hψ g (isPath_single (X := K) e)
      simpa only [mapPath, List.map_cons, List.map_nil, extendList_cons, extendList_nil,
        wordValue_cons, wordValue_nil, mul_one, germSrc, germTgt, Bool.false_eq_true, if_false] using h
    rw [liftPath_cons, List.map_cons]
    change receiverGerm T f ψ (liftGerm T φ g e) :: _ =
      uLiftPath ((f.onE e.1, e.2) :: mapPath f p) _
    rw [uLiftPath_cons hs, he]
    apply congrArg₂ List.cons
    · exact comparison_liftGerm T f φ ψ hψ g e
    · exact ih _ hp

/-- The comparison is an actual cellular map, not a postulated chain map. -/
noncomputable def comparison : Hom (cover T φ) (uCover Y (f.onV T.root)) where
  onV x := receiverVertex T f ψ x.1 x.2
  onE x := receiverEdge T f ψ x.1 x.2
  onF x := receiverFace T f ψ x.1 x.2
  src_onE _ := rfl
  tgt_onE x := receiverEdge_tgt T f φ ψ hψ x.1 x.2
  base_onF _ := rfl
  att_onF x := by
    change uLiftPath (Y.att (f.onF x.2)) (receiverVertex T f ψ x.1 (K.base x.2)) =
      (liftPath T φ (K.att x.2) x.1).map (receiverGerm T f ψ)
    rw [f.att_onF]
    exact (comparison_liftPath T f φ ψ hψ x.1 (K.att_isLoop x.2)).symm

theorem comparison_bdry2 (c : (G × K.F) →₀ ℤ) :
    bdry2 (uCover Y (f.onV T.root)) (chain2 (comparison T f φ ψ hψ) c) =
      chain1 (comparison T f φ ψ hψ) (bdry2 (cover T φ) c) :=
  bdry2_chain2 (comparison T f φ ψ hψ) c

theorem comparison_projects :
    (univProj Y (f.onV T.root)).comp (comparison T f φ ψ hψ) =
      f.comp (projection T φ) := by
  apply Hom.ext'
  · funext x
    exact receiverVertex_end T f ψ x.1 x.2
  · rfl
  · rfl

/-- For the receiving group pi1(Y), the compatibility triangle is an identity.
This gives the genuine comparison without an extra mathematical assumption. -/
noncomputable def canonicalReceiver : PresGroup (treeRel T) →* Pi1 Y (f.onV T.root) :=
  (pi1Map f T.root).comp (SpanningTree.presToPi1 T)

noncomputable def canonicalComparison :
    Hom (cover T (canonicalReceiver T f)) (uCover Y (f.onV T.root)) :=
  comparison T f (canonicalReceiver T f) (MonoidHom.id _) rfl

theorem canonicalComparison_bdry2 (c : (Pi1 Y (f.onV T.root) × K.F) →₀ ℤ) :
    bdry2 _ (chain2 (canonicalComparison T f) c) =
      chain1 (canonicalComparison T f) (bdry2 (cover T (canonicalReceiver T f)) c) :=
  bdry2_chain2 (canonicalComparison T f) c

end FiniteChains.Comb.ReceivedTree
