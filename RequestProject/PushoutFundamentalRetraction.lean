module

public import RequestProject.CombEdgeLabels
public import RequestProject.CombPushout

@[expose] public section

/-! The upstairs fundamental group embeds in the actual cellular pushout.
The retraction is read from actual edge labels and path homotopies. Thus
copies used in spherical descent really are universal covers of L.
No van Kampen or factor-injection hypothesis is introduced. Unverified. -/

noncomputable section
open scoped Classical

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb
universe u
variable {D K L : Complex2.{u}}

namespace RootPaths
def relative (i : Hom D L) (hi : Function.Injective i.onV)
    (hD : IsConnected D) (hL : IsConnected L) (d₀ : D.V) : RootPaths L (i.onV d₀) where
  path v := if h : ∃ d, i.onV d = v then
    mapPath i ((choose hD d₀).path h.choose) else (choose hL (i.onV d₀)).path v
  valid v := by
    split
    · rename_i h
      simpa only [h.choose_spec] using isPath_mapPath i ((choose hD d₀).valid h.choose)
    · exact (choose hL (i.onV d₀)).valid v
  at_root := by
    have h : ∃ d, i.onV d = i.onV d₀ := ⟨d₀, rfl⟩
    rw [dif_pos h, hi h.choose_spec, (choose hD d₀).at_root, mapPath_nil]

theorem relative_path (i : Hom D L) (hi : Function.Injective i.onV)
    (hD : IsConnected D) (hL : IsConnected L) (d₀ d : D.V) :
    (relative i hi hD hL d₀).path (i.onV d) = mapPath i ((choose hD d₀).path d) := by
  have h : ∃ d', i.onV d' = i.onV d := ⟨d, rfl⟩
  simp only [relative, dif_pos h, hi h.choose_spec]

theorem relative_edge_core (i : Hom D L) (hi : Function.Injective i.onV)
    (hD : IsConnected D) (hL : IsConnected L) (d₀ : D.V) (ht : Pi1Trivial i) (e : D.E) :
    (relative i hi hD hL d₀).edge (i.onE e) = 1 := by
  apply Quotient.sound
  change Htpy L (i.onV d₀) (i.onV d₀)
    ((relative i hi hD hL d₀).path (L.src (i.onE e)) ++ [(i.onE e, true)] ++
      revPath ((relative i hi hD hL d₀).path (L.tgt (i.onE e)))) []
  rw [i.src_onE, i.tgt_onE, relative_path, relative_path]
  have h := ht d₀ ((choose hD d₀).conjugate [(e, true)] (D.src e) (D.tgt e))
    ((choose hD d₀).conjugate_valid (isPath_single (e, true)))
  simpa [conjugate, mapPath, revPath, revGerm, List.map_map, Function.comp_def] using h
end RootPaths

namespace PushoutFundamental
variable (p : Hom D K) (i : Hom D L)
  (hiV : Function.Injective i.onV) (hiE : Function.Injective i.onE)
  (hiF : Function.Injective i.onF) (hD : IsConnected D) (hL : IsConnected L)
  (d₀ : D.V) (ht : Pi1Trivial i)

def labels : (pushoutComplex p i hiV hiE).E → Pi1 L (i.onV d₀)
  | Sum.inl _ => 1
  | Sum.inr e => (RootPaths.relative i hiV hD hL d₀).edge e.val

include ht in
theorem labels_pushE (e : L.E) : labels p i hiV hiE hD hL d₀ (pushE p i e) =
    (RootPaths.relative i hiV hD hL d₀).edge e := by
  by_cases h : ∃ d, i.onE d = e
  · obtain ⟨d, rfl⟩ := h
    rw [pushE_of_mem p hiE]
    exact (RootPaths.relative_edge_core i hiV hD hL d₀ ht d).symm
  · rw [pushE_of_off p i ⟨e, fun d hd => h ⟨d, hd⟩⟩]
    rfl

include ht in
theorem read_pushPath (l : List (L.E × Bool)) :
    EdgeLabels.read (labels p i hiV hiE hD hL d₀)
      (l.map (fun e => (pushE p i e.1, e.2))) =
      EdgeLabels.read (RootPaths.relative i hiV hD hL d₀).edge l := by
  induction l with
  | nil => rfl
  | cons e l ih =>
      simp only [List.map_cons, EdgeLabels.read_cons, ih]
      congr 1
      rcases e with ⟨e, b⟩
      cases b <;> simp [EdgeLabels.germ, labels_pushE p i hiV hiE hD hL d₀ ht]

include ht in
theorem labels_rel (f : (pushoutComplex p i hiV hiE).F) :
    EdgeLabels.read (labels p i hiV hiE hD hL d₀) ((pushoutComplex p i hiV hiE).att f) = 1 := by
  cases f with
  | inl f =>
      change EdgeLabels.read (labels p i hiV hiE hD hL d₀)
        ((K.att f).map (fun e => (Sum.inl e.1, e.2))) = 1
      have h : ∀ l : List (K.E × Bool), EdgeLabels.read (labels p i hiV hiE hD hL d₀)
          (l.map (fun e => (Sum.inl e.1, e.2))) = 1 := by
        intro l
        induction l with
        | nil => rfl
        | cons e l ih => simp [EdgeLabels.read_cons, EdgeLabels.germ, labels, ih]
      exact h _
  | inr f =>
      change EdgeLabels.read (labels p i hiV hiE hD hL d₀)
        ((L.att f.val).map (fun e => (pushE p i e.1, e.2))) = 1
      rw [read_pushPath p i hiV hiE hD hL d₀ ht]
      exact (RootPaths.relative i hiV hD hL d₀).edge_rel f.val

/-- The actual pushout group retracts onto the group of L. -/
def retraction :
    Pi1 (pushoutComplex p i hiV hiE) ((pushoutMap p i hiV hiE hiF).onV (i.onV d₀)) →*
      Pi1 L (i.onV d₀) :=
  EdgeLabels.monodromy (labels p i hiV hiE hD hL d₀)
    (labels_rel p i hiV hiE hD hL d₀ ht) _

theorem retraction_leftInverse : Function.LeftInverse
    (retraction p i hiV hiE hiF hD hL d₀ ht)
    (pi1Map (pushoutMap p i hiV hiE hiF) (i.onV d₀)) := by
  intro z
  induction z using Quotient.inductionOn with
  | h l =>
      change EdgeLabels.read (labels p i hiV hiE hD hL d₀)
        (l.val.map (fun e => (pushE p i e.1, e.2))) = Pi1.mk l
      rw [read_pushPath p i hiV hiE hD hL d₀ ht]
      exact (RootPaths.relative i hiV hD hL d₀).read_loop l

include hD hL ht in
/-- The factor map is injective for the genuine cellular pushout. -/
theorem pi1_pushoutMap_injective : Function.Injective
    (pi1Map (pushoutMap p i hiV hiE hiF) (i.onV d₀)) :=
  (retraction_leftInverse p i hiV hiE hiF hD hL d₀ ht).injective

end PushoutFundamental
end FiniteChains.Comb
