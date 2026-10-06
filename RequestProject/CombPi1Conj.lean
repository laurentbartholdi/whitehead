module

public import RequestProject.CombPi1

@[expose] public section

/-!
# Change of base point in the edge-path fundamental group

The loops of the block of the substitution are read at a vertex of the block, whereas the
comparison homomorphism of the substitution is based at the base point of the copy of the base
complex.  The two are joined by a fixed edge path, and the dictionary between the two base
points is the conjugation by that path.  This file provides it:

* `FiniteChains.Comb.conjLoop` — the loop `c · p · c⁻¹` at `a` obtained from a loop `p` at `b`
  and a path `c` from `a` to `b`;
* `FiniteChains.Comb.pi1Conj` — the induced group homomorphism `π₁(X, b) →* π₁(X, a)`
  (an isomorphism, but only the homomorphism is needed here);
* `FiniteChains.Comb.pi1Conj_mk` — its value on the class of a loop is the class of the
  conjugated loop, by definition.
-/

namespace FiniteChains
namespace Comb

universe u

variable {X : Complex2.{u}} {a b : X.V} {c : List (X.E × Bool)}

/-- The loop `c · p · c⁻¹` at `a`, for a loop `p` at `b` and a path `c` from `a` to `b`. -/
def conjLoop (hc : IsPath X.src X.tgt c a b) (p : Loop X b) : Loop X a :=
  ⟨c ++ p.1 ++ revPath c,
    isPath_append_iff.mpr ⟨b, isPath_append_iff.mpr ⟨b, hc, p.2⟩, isPath_revPath hc⟩⟩

/-- **Change of base point**: conjugation by a path `c` from `a` to `b` is a homomorphism
`π₁(X, b) →* π₁(X, a)`. -/
def pi1Conj (hc : IsPath X.src X.tgt c a b) : Pi1 X b →* Pi1 X a where
  toFun := Quotient.map (conjLoop hc) (fun _ _ h => (h.congr_append hc (isPath_revPath hc)))
  map_one' := by
    refine Quotient.sound ?_
    show Htpy X a a (c ++ [] ++ revPath c) []
    simpa using htpy_append_revPath hc
  map_mul' := by
    rintro ⟨p⟩ ⟨q⟩
    refine Quotient.sound ?_
    show Htpy X a a (c ++ (p.1 ++ q.1) ++ revPath c)
      ((c ++ p.1 ++ revPath c) ++ (c ++ q.1 ++ revPath c))
    have hcancel : Htpy X b b (revPath c ++ c) [] := htpy_revPath_append hc
    have hleft : IsPath X.src X.tgt (c ++ p.1) a b := isPath_append_iff.mpr ⟨b, hc, p.2⟩
    have hright : IsPath X.src X.tgt (q.1 ++ revPath c) b a :=
      isPath_append_iff.mpr ⟨b, q.2, isPath_revPath hc⟩
    have hmain := hcancel.congr_append hleft hright
    have hrw₁ : (c ++ p.1) ++ (revPath c ++ c) ++ (q.1 ++ revPath c)
        = (c ++ p.1 ++ revPath c) ++ (c ++ q.1 ++ revPath c) := by
      simp [List.append_assoc]
    have hrw₂ : (c ++ p.1) ++ ([] : List (X.E × Bool)) ++ (q.1 ++ revPath c)
        = c ++ (p.1 ++ q.1) ++ revPath c := by
      simp [List.append_assoc]
    rw [hrw₁, hrw₂] at hmain
    exact hmain.symm

@[simp] theorem pi1Conj_mk (hc : IsPath X.src X.tgt c a b) (p : Loop X b) :
    pi1Conj hc (Pi1.mk p) = Pi1.mk (conjLoop hc p) := rfl

/-- Conjugation only depends on the homotopy class of the conjugating path. -/
theorem pi1Conj_congr {c' : List (X.E × Bool)} (hc : IsPath X.src X.tgt c a b)
    (hc' : IsPath X.src X.tgt c' a b) (h : Htpy X a b c c') (x : Pi1 X b) :
    pi1Conj hc x = pi1Conj hc' x := by
  induction x using Quotient.inductionOn with
  | _ p =>
      refine Quotient.sound ?_
      show Htpy X a a (c ++ p.1 ++ revPath c) (c' ++ p.1 ++ revPath c')
      have h1 : Htpy X a a (c ++ (p.1 ++ revPath c)) (c' ++ (p.1 ++ revPath c)) :=
        Htpy.append_congr hc (isPath_append_iff.mpr ⟨b, p.2, isPath_revPath hc⟩) h (Htpy.refl _)
      have h2 : Htpy X b a (p.1 ++ revPath c) (p.1 ++ revPath c') :=
        Htpy.append_congr p.2 (isPath_revPath hc) (Htpy.refl _) (htpy_revPath hc h)
      have h3 : Htpy X a a (c' ++ (p.1 ++ revPath c)) (c' ++ (p.1 ++ revPath c')) :=
        Htpy.append_congr (h.isPath hc) (isPath_append_iff.mpr ⟨b, p.2, isPath_revPath hc⟩)
          (Htpy.refl _) h2
      simpa [List.append_assoc] using h1.trans h3

/-- Conjugating twice is conjugating by the concatenated path. -/
theorem pi1Conj_pi1Conj {d : List (X.E × Bool)} {e : X.V} (hc : IsPath X.src X.tgt c a b)
    (hd : IsPath X.src X.tgt d b e) (x : Pi1 X e) :
    pi1Conj hc (pi1Conj hd x) = pi1Conj (hc.append hd) x := by
  induction x using Quotient.inductionOn with
  | _ p =>
      refine Quotient.sound ?_
      show Htpy X a a (conjLoop hc (conjLoop hd p)).1 (conjLoop (hc.append hd) p).1
      have hlist : (conjLoop hc (conjLoop hd p)).1 = (conjLoop (hc.append hd) p).1 := by
        simp [conjLoop, revPath_append, List.append_assoc]
      rw [hlist]
      exact Htpy.refl _

/-- Conjugation is natural: the image of a conjugated class is the class conjugated by the
image of the path. -/
theorem pi1Map_pi1Conj {Y : Complex2.{u}} (h : Hom X Y) (hc : IsPath X.src X.tgt c a b)
    (x : Pi1 X b) :
    pi1Map h a (pi1Conj hc x) = pi1Conj (isPath_mapPath h hc) (pi1Map h b x) := by
  induction x using Quotient.inductionOn with
  | _ p =>
      refine Quotient.sound ?_
      show Htpy Y (h.onV a) (h.onV a) (mapPath h (conjLoop hc p).1)
        (conjLoop (isPath_mapPath h hc) ⟨mapPath h p.1, isPath_mapPath h p.2⟩).1
      have hrev : mapPath h (revPath c) = revPath (mapPath h c) := by
        simp [mapPath, revPath, revGerm, List.map_map, Function.comp_def, List.map_reverse]
      have hlist : mapPath h (conjLoop hc p).1
          = (conjLoop (isPath_mapPath h hc) ⟨mapPath h p.1, isPath_mapPath h p.2⟩).1 := by
        simp [conjLoop, hrev]
      rw [hlist]
      exact Htpy.refl _

end Comb
end FiniteChains
