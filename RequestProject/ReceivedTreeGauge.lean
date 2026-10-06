module

public import RequestProject.ReceivedTreeCover
public import RequestProject.UniversalTreeGauge

@[expose] public section

/-! Exact geometric reference paths for the cover over a receiving group. -/
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb.ReceivedTree
open SpanningTree
universe u
variable {K Y : Complex2.{u}} (T : SpanningTree K) (f : Hom K Y)
  {G : Type u} [Group G] (φ : PresGroup (treeRel T) →* G)
  (ψ : G →* Pi1 Y (f.onV T.root))

noncomputable def receiverVertex (g : G) (a : K.V) : UV Y (f.onV T.root) :=
  deckV (ψ g) (mappedTreeReference T f a)

theorem receiverVertex_end (g : G) (a : K.V) :
    endV (receiverVertex T f ψ g a) = f.onV a := by
  rw [receiverVertex, endV_deckV, mappedTreeReference_end]

variable (hψ : ψ.comp φ = (pi1Map f T.root).comp (SpanningTree.presToPi1 T))

include hψ in
theorem receiver_word (w : FreeGroup (NonTree T)) :
    ψ (φ (QuotientGroup.mk w)) = pi1Map f T.root (SpanningTree.freeToPi1 T w) :=
  DFunLike.congr_fun hψ (QuotientGroup.mk w)

include hψ in
/-- The actual geometric endpoint changes by exactly the received tree word. -/
theorem receiverVertex_path (g : G) {a b : K.V} {p : List (K.E × Bool)}
    (hp : IsPath K.src K.tgt p a b) :
    extendList (mapPath f p) (receiverVertex T f ψ g a) =
      receiverVertex T f ψ (g * wordValue T φ p) b := by
  unfold receiverVertex
  rw [extendList_deckV, mappedTreeReference_path T f hp, map_mul,
    deckV_mul, wordValue, receiver_word T f φ ψ hψ]

noncomputable def receiverEdge (g : G) (e : K.E) : UE Y (f.onV T.root) :=
  ⟨(receiverVertex T f ψ g (K.src e), f.onE e), by
    rw [receiverVertex_end, f.src_onE]⟩

theorem receiverEdge_src (g : G) (e : K.E) :
    uSrc (receiverEdge T f ψ g e) = receiverVertex T f ψ g (K.src e) := rfl

include hψ in
theorem receiverEdge_tgt (g : G) (e : K.E) :
    uTgt (receiverEdge T f ψ g e) =
      receiverVertex T f ψ (g * germValue T φ (e, true)) (K.tgt e) := by
  have h := receiverVertex_path T f φ ψ hψ g (isPath_single (X := K) (e, true))
  simpa only [mapPath, List.map_cons, List.map_nil, extendList_cons, extendList_nil,
    wordValue_cons, wordValue_nil, mul_one, receiverEdge, uTgt, germSrc, germTgt, if_true] using h

noncomputable def receiverFace (g : G) (t : K.F) : UF Y (f.onV T.root) :=
  ⟨(receiverVertex T f ψ g (K.base t), f.onF t), by
    rw [receiverVertex_end, f.base_onF]⟩

end FiniteChains.Comb.ReceivedTree
