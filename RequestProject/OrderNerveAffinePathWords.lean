import RequestProject.OrderNerveAffineEdgePath
import RequestProject.ContinuousEdgeWordHomotopies
import RequestProject.CombPi1

/-! Actual affine realization of composable order-edge words, with exact
monotone-map naturality. Pending Lean verification. -/

noncomputable section
open scoped Classical unitInterval Topology
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb
open ContinuousEdgeWords CategoryTheory Simplicial

variable {P : Type} [PartialOrder P]

def affineOrderWordPath (l : List ((orderCx P).E × Bool)) {a b : P}
    (hl : IsPath (orderCx P).src (orderCx P).tgt l a b) :
    Path (orderNerveRealizationVertex a) (orderNerveRealizationVertex b) :=
  realize (orderCx P).src (orderCx P).tgt (orderNerveRealizationVertex (P := P))
    (fun e => orderNerveAffineEdgePath (P := P) e.property) l hl

theorem affineGermPath_coordinates (g : (orderCx P).E × Bool) (t : I) (p : P) :
    orderNerveRealizationCoordinates P
      (germPath (orderCx P).src (orderCx P).tgt (orderNerveRealizationVertex (P := P))
        (fun e => orderNerveAffineEdgePath (P := P) e.property) g t) p =
      (1 - (t : ℝ)) * (if germSrc (orderCx P).src (orderCx P).tgt g = p then 1 else 0) +
        (t : ℝ) * (if germTgt (orderCx P).src (orderCx P).tgt g = p then 1 else 0) := by
  rcases g with ⟨e, b⟩
  cases b
  · simp only [germPath, Path.symm_apply, Function.comp_apply, orderNerveAffineEdgePath_coordinates,
      unitInterval.coe_symm_eq, germSrc_false, germTgt_false]
    ring
  · exact orderNerveAffineEdgePath_coordinates e.property t p

theorem comparablePath_homotopic_single {a b : P} (h : a ≤ b ∨ b ≤ a)
    (g : (orderCx P).E × Bool)
    (hs : a = germSrc (orderCx P).src (orderCx P).tgt g)
    (ht : germTgt (orderCx P).src (orderCx P).tgt g = b) :
    (orderNerveComparablePath h).Homotopic (affineOrderWordPath [g] ⟨hs, ht⟩) := by
  subst a
  subst b
  have he : orderNerveComparablePath h =
      germPath (orderCx P).src (orderCx P).tgt (orderNerveRealizationVertex (P := P))
        (fun e => orderNerveAffineEdgePath (P := P) e.property) g := by
    apply Path.ext
    funext t
    apply orderNerveRealizationCoordinates_injective P
    funext p
    rw (config := { transparency := .default }) [orderNerveComparablePath_coordinates, affineGermPath_coordinates]
  rw (config := { transparency := .default }) [he]
  exact (Path.Homotopic.trans_refl _).symm

private theorem affineWord_map_vertex {Q : Type} [PartialOrder Q]
    (f : P → Q) (hf : Monotone f) (p : P) :
    orderNerveRealizationMap f hf (orderNerveRealizationVertex p) =
      orderNerveRealizationVertex (f p) := by
  exact congrArg (fun k : TopCat.of (SimplexCategory.toTop.obj ⦋0⦌) ⟶
      orderNerveRealization Q => k default)
    (orderNerveRealizationSimplex_natural f hf (ComposableArrows.mk₀ p))

theorem affineGermPath_map {Q : Type} [PartialOrder Q]
    (f : P → Q) (hf : Monotone f) (g : (orderCx P).E × Bool) (t : I) :
    orderNerveRealizationMap f hf
      (germPath (orderCx P).src (orderCx P).tgt (orderNerveRealizationVertex (P := P))
        (fun e => orderNerveAffineEdgePath (P := P) e.property) g t) =
      germPath (orderCx Q).src (orderCx Q).tgt (orderNerveRealizationVertex (P := Q))
        (fun e => orderNerveAffineEdgePath (P := Q) e.property)
        ((orderCxMap f hf).onE g.1, g.2) t := by
  rcases g with ⟨e, b⟩
  cases b
  · change orderNerveRealizationMap f hf
      (orderNerveAffineEdgePath e.property (unitInterval.symm t)) =
        orderNerveAffineEdgePath (hf e.property) (unitInterval.symm t)
    simpa only [orderNerveComparablePath, dif_pos e.property, dif_pos (hf e.property)] using
      orderNerveComparablePath_natural f hf (Or.inl e.property)
        (Or.inl (hf e.property)) (unitInterval.symm t)
  · change orderNerveRealizationMap f hf (orderNerveAffineEdgePath e.property t) =
      orderNerveAffineEdgePath (hf e.property) t
    simpa only [orderNerveComparablePath, dif_pos e.property, dif_pos (hf e.property)] using
      orderNerveComparablePath_natural f hf (Or.inl e.property) (Or.inl (hf e.property)) t

theorem affineOrderWordPath_map {Q : Type} [PartialOrder Q]
    (f : P → Q) (hf : Monotone f) (l : List ((orderCx P).E × Bool)) {a b : P}
    (hl : IsPath (orderCx P).src (orderCx P).tgt l a b) (t : I) :
    orderNerveRealizationMap f hf (affineOrderWordPath l hl t) =
      affineOrderWordPath (mapPath (orderCxMap f hf) l)
        (isPath_mapPath (orderCxMap f hf) hl) t := by
  induction l generalizing a t with
  | nil =>
    cases hl
    exact affineWord_map_vertex f hf b
  | cons g l ih =>
    obtain ⟨rfl, ht⟩ := hl
    simp only [affineOrderWordPath, realize, mapPath, List.map_cons, Path.trans_apply, Path.cast_coe]
    split_ifs with hhalf
    · exact affineGermPath_map f hf g _
    · rcases g with ⟨e, direction⟩
      cases direction <;> simpa only [affineOrderWordPath, mapPath] using
        ih ht ⟨2 * (t : ℝ) - 1, by constructor <;> linarith [t.property.1, t.property.2]⟩

end FiniteChains.Comb
