import RequestProject.TruncatedCellDimension
import RequestProject.SpineCollapse

/-! Read actual codimension-one face incidences in the collapse's coordinate indices. -/
namespace FiniteChains.Davis
open RACG Mirror
variable {V : Type} [Fintype V] [DecidableEq V] {A : CommRel V}

theorem mem_cofaces_of_coordinateFace {L : ASC V} {c d : Cube V}
    (hface : CoordinateFace c d) (hc : (freeSet c).card = 2)
    (hd : (freeSet d).card = 3) (hL : freeSet d ∈ L.faces) : d ∈ cofaces L c := by
  classical
  have hsub : freeSet c ⊆ freeSet d := by
    intro v hv
    have hvf := mem_freeSet.mp hv
    rcases hface v with h | h
    · exact mem_freeSet.mpr h
    · exact mem_freeSet.mpr (h.symm.trans hvf)
  have hcard : (freeSet d \ freeSet c).card = 1 := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hsub, hc, hd]
  obtain ⟨j, hj⟩ := Finset.card_eq_one.mp hcard
  have hjd : j ∈ freeSet d := (Finset.mem_sdiff.mp
    (hj ▸ Finset.mem_singleton_self j)).1
  have hjc : j ∉ freeSet c := (Finset.mem_sdiff.mp
    (hj ▸ Finset.mem_singleton_self j)).2
  have hset : freeSet d = insert j (freeSet c) := by
    ext v
    constructor
    · intro hv
      by_cases hvc : v ∈ freeSet c
      · exact Finset.mem_insert_of_mem hvc
      · have hm : v ∈ freeSet d \ freeSet c := Finset.mem_sdiff.mpr ⟨hv, hvc⟩
        rw [hj] at hm
        exact Finset.mem_insert.mpr (Or.inl (Finset.mem_singleton.mp hm))
    · intro hv
      rcases Finset.mem_insert.mp hv with rfl | hv
      · exact hjd
      · exact hsub hv
  apply mem_cofaces.mpr
  refine ⟨j, (fun h => hjc (mem_freeSet.mpr h)), hset ▸ hL, ?_⟩
  funext v
  by_cases hvj : v = j
  · subst v
    simpa using mem_freeSet.mp hjd
  · rw [Function.update_of_ne hvj]
    by_cases hvd : v ∈ freeSet d
    · have hvc : v ∈ freeSet c := by
        rw [hset] at hvd
        exact (Finset.mem_insert.mp hvd).resolve_left hvj
      exact (mem_freeSet.mp hvd).trans (mem_freeSet.mp hvc).symm
    · exact ((hface v).resolve_left (fun h => hvd (mem_freeSet.mpr h))).symm

theorem truncatedCell_inc_of_le {L : ASC V} (c : TruncatedCell A) (d : QOld A)
    (hcd : c ≤ Sum.inl d) (hc : truncatedCellDimension c = 2)
    (hd : d.1.spx.card = 3) (hL : d.1.spx ∈ L.faces) :
    qCubeToCoordinate d.1 ∈ spineInc L (truncatedFaceIndex c) := by
  classical
  cases c with
  | inl c =>
    have hf := (qCubeToCoordinate_face_iff c.1 d.1).mp hcd
    have hdim : (freeSet (qCubeToCoordinate c.1)).card = 2 := by
      simpa [truncatedCellDimension] using hc
    have hc' : c.1.spx.card = 2 := hc
    simpa [spineInc, truncatedFaceIndex, hc'] using
      mem_cofaces_of_coordinateFace hf hdim
        (by simpa using hd) (by simpa using hL)
  | inr σ =>
    have hsub : σ.1 ⊆ d.1.spx := hcd.1
    have hσ : σ.1.card = 3 := by
      have hp := Finset.card_pos.mpr σ.2.1
      change σ.1.card - 1 = 2 at hc
      omega
    have he : σ.1 = d.1.spx :=
      Finset.eq_of_subset_of_card_le hsub (by omega)
    have ht : IsTri L σ.1 := ⟨he ▸ hL, hσ⟩
    have ht' : IsTri L d.1.spx := he ▸ ht
    have hz := qCubeToCoordinate_sgn_zero d.1 hcd.2
    simp [spineInc, truncatedFaceIndex, ht', hz, he]

theorem truncatedCell_le_of_inc {L : ASC V} (c : TruncatedCell A) (d : QOld A)
    (hi : qCubeToCoordinate d.1 ∈ spineInc L (truncatedFaceIndex c)) :
    c ≤ Sum.inl d := by
  classical
  cases c with
  | inl c =>
    have hm : qCubeToCoordinate d.1 ∈ cofaces L (qCubeToCoordinate c.1) := by
      simp only [spineInc, truncatedFaceIndex] at hi
      split at hi
      · exact hi
      · simp at hi
    obtain ⟨j, _, _, he⟩ := mem_cofaces.mp hm
    apply (qCubeToCoordinate_face_iff c.1 d.1).mpr
    intro v
    rw [he]
    by_cases hv : v = j
    · left
      subst v
      exact Function.update_self _ _ _
    · right
      simp [hv]
  | inr σ =>
    have he : qCubeToCoordinate d.1 = posCube σ.1 := by
      simp only [spineInc, truncatedFaceIndex] at hi
      split at hi
      · exact Finset.mem_singleton.mp hi
      · simp at hi
    have hs : d.1.spx = σ.1 := by
      have hh := congrArg freeSet he
      simpa using hh
    apply (cut_le_old_coordinate_iff σ d).mpr
    exact ⟨by simp [hs], by simpa [hs] using he⟩

end FiniteChains.Davis
