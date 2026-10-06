import RequestProject.UniversalCoverCopyLabels
import RequestProject.SupportedLabelChains
import RequestProject.CombPushout

/-! Outside K every lifted cell has exactly one L-cell label.  The labels
below make the relative boundary block diagonal over the actual lifted
copies of L. No cycle-generation statement is assumed. Unverified source. -/

noncomputable section
open scoped Classical
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb.PushoutRelativeCopies
universe u
variable {D K L : Complex2.{u}} (p : Hom D K) (i : Hom D L)
  (hiV : Function.Injective i.onV) (hiE : Function.Injective i.onE)
  (hiF : Function.Injective i.onF) (a : L.V)

abbrev target := pushoutComplex p i hiV hiE
abbrev root := (pushoutMap p i hiV hiE hiF).onV a

def oldEdge (e : UE (target p i hiV hiE) (root p i hiV hiE hiF a)) : Prop :=
  ∃ k : K.E, e.val.2 = Sum.inl k
def oldFace (t : UF (target p i hiV hiE) (root p i hiV hiE hiF a)) : Prop :=
  ∃ k : K.F, t.val.2 = Sum.inl k

def edgeLabel (e : UE (target p i hiV hiE) (root p i hiV hiE hiF a)) :
    Set (UV (target p i hiV hiE) (root p i hiV hiE hiF a) × L.V) :=
  match e.val.2 with
  | Sum.inl _ => ∅
  | Sum.inr l => UniversalCopy.label (pushoutMap p i hiV hiE hiF) a (e.val.1, L.src l.val)

def faceLabel (t : UF (target p i hiV hiE) (root p i hiV hiE hiF a)) :
    Set (UV (target p i hiV hiE) (root p i hiV hiE hiF a) × L.V) :=
  match t.val.2 with
  | Sum.inl _ => ∅
  | Sum.inr l => UniversalCopy.label (pushoutMap p i hiV hiE hiF) a (t.val.1, L.base l.val)

theorem oldEdge_map_iff (g : Pi1 (target p i hiV hiE) (root p i hiV hiE hiF a)) (e : UE L a) :
    oldEdge p i hiV hiE hiF a ((UniversalCopy.map (pushoutMap p i hiV hiE hiF) a g).onE e) ↔
      e.val.2 ∈ Set.range i.onE := by
  by_cases h : ∃ d, i.onE d = e.val.2
  · obtain ⟨d, hd⟩ := h
    have hp' : ((UniversalCopy.map (pushoutMap p i hiV hiE hiF) a g).onE e).val.2 =
        Sum.inl (p.onE d) := by
      change pushE p i e.val.2 = _
      rw [← hd, pushE_of_mem p hiE]
    exact ⟨fun _ => ⟨d, hd⟩, fun _ => ⟨p.onE d, hp'⟩⟩
  · have hp' : ((UniversalCopy.map (pushoutMap p i hiV hiE hiF) a g).onE e).val.2 =
        Sum.inr (⟨e.val.2, fun d hd => h ⟨d, hd⟩⟩ : OffE i) := by
      change pushE p i e.val.2 = _
      exact pushE_of_off p i ⟨e.val.2, fun d hd => h ⟨d, hd⟩⟩
    constructor
    · rintro ⟨k, hk⟩
      rw [hp'] at hk
      exact (Sum.inr_ne_inl hk).elim
    · exact fun he => False.elim (h he)

theorem oldFace_map_iff (g : Pi1 (target p i hiV hiE) (root p i hiV hiE hiF a)) (t : UF L a) :
    oldFace p i hiV hiE hiF a ((UniversalCopy.map (pushoutMap p i hiV hiE hiF) a g).onF t) ↔
      t.val.2 ∈ Set.range i.onF := by
  by_cases h : ∃ d, i.onF d = t.val.2
  · obtain ⟨d, hd⟩ := h
    have hp' : ((UniversalCopy.map (pushoutMap p i hiV hiE hiF) a g).onF t).val.2 =
        Sum.inl (p.onF d) := by
      change pushF p i t.val.2 = _
      rw [← hd, pushF_of_mem p hiF]
    exact ⟨fun _ => ⟨d, hd⟩, fun _ => ⟨p.onF d, hp'⟩⟩
  · have hp' : ((UniversalCopy.map (pushoutMap p i hiV hiE hiF) a g).onF t).val.2 =
        Sum.inr (⟨t.val.2, fun d hd => h ⟨d, hd⟩⟩ : OffF i) := by
      change pushF p i t.val.2 = _
      exact pushF_of_off p i ⟨t.val.2, fun d hd => h ⟨d, hd⟩⟩
    constructor
    · rintro ⟨k, hk⟩
      rw [hp'] at hk
      exact (Sum.inr_ne_inl hk).elim
    · exact fun ht => False.elim (h ht)

theorem edgeLabel_on_copy (hT : IsConnected (target p i hiV hiE))
    (g : Pi1 (target p i hiV hiE) (root p i hiV hiE hiF a)) (e : UE L a)
    (he : ¬ oldEdge p i hiV hiE hiF a
      ((UniversalCopy.map (pushoutMap p i hiV hiE hiF) a g).onE e)) :
    edgeLabel p i hiV hiE hiF a
      ((UniversalCopy.map (pushoutMap p i hiV hiE hiF) a g).onE e) =
        UniversalCopy.vertices (pushoutMap p i hiV hiE hiF) a g := by
  have hn : ∀ d, i.onE d ≠ e.val.2 := fun d hd =>
    he ((oldEdge_map_iff p i hiV hiE hiF a g e).mpr ⟨d, hd⟩)
  have hp' : ((UniversalCopy.map (pushoutMap p i hiV hiE hiF) a g).onE e).val.2 =
      Sum.inr (⟨e.val.2, hn⟩ : OffE i) := by
    change pushE p i e.val.2 = _
    exact pushE_of_off p i ⟨e.val.2, hn⟩
  unfold edgeLabel
  rw [hp']
  change UniversalCopy.label _ a
    ((UniversalCopy.map _ a g).onV e.val.1, L.src e.val.2) = _
  rw [← e.property]
  exact UniversalCopy.label_on_pair _ a hT g e.val.1

theorem faceLabel_on_copy (hT : IsConnected (target p i hiV hiE))
    (g : Pi1 (target p i hiV hiE) (root p i hiV hiE hiF a)) (t : UF L a)
    (ht : ¬ oldFace p i hiV hiE hiF a
      ((UniversalCopy.map (pushoutMap p i hiV hiE hiF) a g).onF t)) :
    faceLabel p i hiV hiE hiF a
      ((UniversalCopy.map (pushoutMap p i hiV hiE hiF) a g).onF t) =
        UniversalCopy.vertices (pushoutMap p i hiV hiE hiF) a g := by
  have hn : ∀ d, i.onF d ≠ t.val.2 := fun d hd =>
    ht ((oldFace_map_iff p i hiV hiE hiF a g t).mpr ⟨d, hd⟩)
  have hp' : ((UniversalCopy.map (pushoutMap p i hiV hiE hiF) a g).onF t).val.2 =
      Sum.inr (⟨t.val.2, hn⟩ : OffF i) := by
    change pushF p i t.val.2 = _
    exact pushF_of_off p i ⟨t.val.2, hn⟩
  unfold faceLabel
  rw [hp']
  change UniversalCopy.label _ a
    ((UniversalCopy.map _ a g).onV t.val.1, L.base t.val.2) = _
  rw [← t.property]
  exact UniversalCopy.label_on_pair _ a hT g t.val.1

theorem old_face_boundary_old (t : UF (target p i hiV hiE) (root p i hiV hiE hiF a))
    (ht : oldFace p i hiV hiE hiF a t)
    (e : UE (target p i hiV hiE) (root p i hiV hiE hiF a))
    (he : ¬ oldEdge p i hiV hiE hiF a e) :
    bdry2 (uCover (target p i hiV hiE) (root p i hiV hiE hiF a)) (Finsupp.single t 1) e = 0 := by
  obtain ⟨k, hk⟩ := ht
  have hb : endV t.val.1 = (pushoutInl p i hiV hiE).onV (K.base k) := by
    rw [t.property, hk]
    rfl
  obtain ⟨φ, hV, hE, hF, hbase⟩ :=
    exists_lift_univCover (pushoutInl p i hiV hiE) (K.base k) t.val.1 hb
  let k' : UF K (K.base k) := ⟨(UV.base K (K.base k), k), rfl⟩
  have hkt : φ.onF k' = t := by
    apply Subtype.ext
    apply Prod.ext
    · exact (φ.base_onF k').trans hbase
    · exact (hF k').trans hk.symm
  have hnot : e ∉ Set.range φ.onE := by
    rintro ⟨d, rfl⟩
    exact he ⟨d.val.2, hE d⟩
  have hb' := bdry2_chain2 φ (Finsupp.single k' 1)
  have hs : chain2 φ (Finsupp.single k' 1) = Finsupp.single t 1 := by
    change Finsupp.mapDomain φ.onF (Finsupp.single k' 1) = _
    rw [Finsupp.mapDomain_single, hkt]
  rw [← hs, hb']
  exact Finsupp.mapDomain_notin_range _ e hnot

def relativeBoundary :
    (UF (target p i hiV hiE) (root p i hiV hiE hiF a) →₀ ℤ) →ₗ[ℤ]
      (UE (target p i hiV hiE) (root p i hiV hiE hiF a) →₀ ℤ) where
  toFun c := (bdry2 (uCover (target p i hiV hiE) (root p i hiV hiE hiF a)) c).filter
    (fun e => ¬ oldEdge p i hiV hiE hiF a e)
  map_add' c d := by rw [map_add, Finsupp.filter_add]
  map_smul' n c := by rw [map_smul, Finsupp.filter_smul]; rfl

theorem relative_boundary_label (hT : IsConnected (target p i hiV hiE)) (hL : IsConnected L)
    (t : UF (target p i hiV hiE) (root p i hiV hiE hiF a))
    (e : UE (target p i hiV hiE) (root p i hiV hiE hiF a))
    (he : relativeBoundary p i hiV hiE hiF a (Finsupp.single t 1) e ≠ 0) :
    edgeLabel p i hiV hiE hiF a e = faceLabel p i hiV hiE hiF a t := by
  have heoff : ¬ oldEdge p i hiV hiE hiF a e := by
    intro heold
    apply he
    simp [relativeBoundary, heold]
  have hb : bdry2 (uCover (target p i hiV hiE) (root p i hiV hiE hiF a))
      (Finsupp.single t 1) e ≠ 0 := by
    change ((bdry2 (uCover (target p i hiV hiE) (root p i hiV hiE hiF a))
      (Finsupp.single t 1)).filter (fun e => ¬ oldEdge p i hiV hiE hiF a e)) e ≠ 0 at he
    rw [Finsupp.filter_apply, if_pos heoff] at he
    exact he
  have htoff : ¬ oldFace p i hiV hiE hiF a t := fun ht =>
    hb (old_face_boundary_old p i hiV hiE hiF a t ht e heoff)
  obtain ⟨l, hl⟩ : ∃ l : OffF i, t.val.2 = Sum.inr l := by
    cases hh : t.val.2 with
    | inl k => exact False.elim (htoff ⟨k, hh⟩)
    | inr l => exact ⟨l, rfl⟩
  have hlf : t.val.2 = (pushoutMap p i hiV hiE hiF).onF l.val := by
    rw [hl]
    exact (pushF_of_off p i l).symm
  obtain ⟨g, x, hx, _⟩ := UniversalCopy.faces_covered (pushoutMap p i hiV hiE hiF) a hL t l.val hlf
  have hmem : e ∈ Set.range (UniversalCopy.map (pushoutMap p i hiV hiE hiF) a g).onE := by
    by_contra hn
    apply hb
    rw [← hx, bdry2_single, one_smul,
      (UniversalCopy.map (pushoutMap p i hiV hiE hiF) a g).att_onF, pathChain_map]
    exact Finsupp.mapDomain_notin_range _ e hn
  obtain ⟨y, hy⟩ := hmem
  have hyoff : ¬ oldEdge p i hiV hiE hiF a
      ((UniversalCopy.map (pushoutMap p i hiV hiE hiF) a g).onE y) := by rwa [hy]
  have hxoff : ¬ oldFace p i hiV hiE hiF a
      ((UniversalCopy.map (pushoutMap p i hiV hiE hiF) a g).onF x) := by rwa [hx]
  rw [← hy, edgeLabel_on_copy p i hiV hiE hiF a hT g y hyoff,
    ← hx, faceLabel_on_copy p i hiV hiE hiF a hT g x hxoff]

theorem relative_boundary_filter (hT : IsConnected (target p i hiV hiE)) (hL : IsConnected L)
    (c : UF (target p i hiV hiE) (root p i hiV hiE hiF a) →₀ ℤ)
    (s : Set (UV (target p i hiV hiE) (root p i hiV hiE hiF a) × L.V)) :
    relativeBoundary p i hiV hiE hiF a
      (c.filter (fun t => faceLabel p i hiV hiE hiF a t = s)) =
    (relativeBoundary p i hiV hiE hiF a c).filter
      (fun e => edgeLabel p i hiV hiE hiF a e = s) :=
  supported_label_boundary (relativeBoundary p i hiV hiE hiF a)
    (faceLabel p i hiV hiE hiF a) (edgeLabel p i hiV hiE hiF a) (fun _ => True)
    (fun t _ e => relative_boundary_label p i hiV hiE hiF a hT hL t e) c (fun _ _ => trivial) s

theorem faceLabel_empty_of_old
    (t : UF (target p i hiV hiE) (root p i hiV hiE hiF a))
    (ht : oldFace p i hiV hiE hiF a t) : faceLabel p i hiV hiE hiF a t = ∅ := by
  obtain ⟨k, hk⟩ := ht
  simp only [faceLabel, hk]

theorem faceLabel_of_not_old (hT : IsConnected (target p i hiV hiE)) (hL : IsConnected L)
    (t : UF (target p i hiV hiE) (root p i hiV hiE hiF a))
    (ht : ¬ oldFace p i hiV hiE hiF a t) :
    ∃ g, faceLabel p i hiV hiE hiF a t =
      UniversalCopy.vertices (pushoutMap p i hiV hiE hiF) a g := by
  obtain ⟨l, hl⟩ : ∃ l : OffF i, t.val.2 = Sum.inr l := by
    cases hh : t.val.2 with
    | inl k => exact False.elim (ht ⟨k, hh⟩)
    | inr l => exact ⟨l, rfl⟩
  have hlf : t.val.2 = (pushoutMap p i hiV hiE hiF).onF l.val :=
    hl.trans (pushF_of_off p i l).symm
  obtain ⟨g, x, hx, _⟩ := UniversalCopy.faces_covered (pushoutMap p i hiV hiE hiF) a hL t l.val hlf
  refine ⟨g, ?_⟩
  rw [← hx]
  apply faceLabel_on_copy p i hiV hiE hiF a hT
  rwa [hx]

theorem faceLabel_empty_iff (hT : IsConnected (target p i hiV hiE)) (hL : IsConnected L)
    (t : UF (target p i hiV hiE) (root p i hiV hiE hiF a)) :
    faceLabel p i hiV hiE hiF a t = ∅ ↔ oldFace p i hiV hiE hiF a t := by
  constructor
  · intro he
    by_contra hn
    obtain ⟨g, hg⟩ := faceLabel_of_not_old p i hiV hiE hiF a hT hL t hn
    have hn' := UniversalCopy.vertices_nonempty (pushoutMap p i hiV hiE hiF) a g
    rw [← hg, he] at hn'
    exact Set.not_nonempty_empty hn'
  · exact faceLabel_empty_of_old p i hiV hiE hiF a t

theorem face_range_of_label (hT : IsConnected (target p i hiV hiE)) (hL : IsConnected L)
    (g : Pi1 (target p i hiV hiE) (root p i hiV hiE hiF a))
    (t : UF (target p i hiV hiE) (root p i hiV hiE hiF a))
    (hl : faceLabel p i hiV hiE hiF a t =
      UniversalCopy.vertices (pushoutMap p i hiV hiE hiF) a g) :
    t ∈ Set.range (UniversalCopy.map (pushoutMap p i hiV hiE hiF) a g).onF := by
  have htoff : ¬ oldFace p i hiV hiE hiF a t := by
    intro ht
    have hh := faceLabel_empty_of_old p i hiV hiE hiF a t ht
    rw [hl] at hh
    have hn := UniversalCopy.vertices_nonempty (pushoutMap p i hiV hiE hiF) a g
    rw [hh] at hn
    exact Set.not_nonempty_empty hn
  obtain ⟨l, he⟩ : ∃ l : OffF i, t.val.2 = Sum.inr l := by
    cases hh : t.val.2 with
    | inl k => exact False.elim (htoff ⟨k, hh⟩)
    | inr l => exact ⟨l, rfl⟩
  apply UniversalCopy.face_range_of_label (pushoutMap p i hiV hiE hiF) a hT hL g t l.val
  · exact he.trans (pushF_of_off p i l).symm
  · simpa only [faceLabel, he] using hl

end FiniteChains.Comb.PushoutRelativeCopies
