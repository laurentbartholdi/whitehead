import RequestProject.QCubeSquareFlagIndex

/-! The four actual corners of a square, with their faithful coordinate index. -/
namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V : Type} [DecidableEq V] {A : CommRel V}

def squareCorner (c : QCube A) (a b : V) (s t : ZMod 2) : QCube A :=
  qCubeFacet (qCubeFacet c a s) b t

@[simp] theorem squareCorner_sgn_left (c : QCube A) (a b : V) (hne : a ≠ b)
    (s t : ZMod 2) : (squareCorner c a b s t).sgn a = s := by
  simp [squareCorner, qCubeFacet, hne]

@[simp] theorem squareCorner_sgn_right (c : QCube A) (a b : V)
    (s t : ZMod 2) : (squareCorner c a b s t).sgn b = t := by
  simp [squareCorner]

theorem squareCorner_spx (c : QCube A) (a b : V) (hne : a ≠ b)
    (hs : c.spx = {a, b}) (s t : ZMod 2) : (squareCorner c a b s t).spx = ∅ := by
  change (c.spx.erase a).erase b = ∅
  simp [hs, hne]

theorem squareCorner_lt (c : QCube A) (a b : V) (hne : a ≠ b)
    (hs : c.spx = {a, b}) (s t : ZMod 2) : squareCorner c a b s t < c :=
  (qCubeFacet_lt _ b t (by rw [squareFacet_w_spx c hne hs s]; simp)).trans
    (qCubeFacet_lt c a s (by rw [hs]; simp))

theorem squareCorner_injective (c : QCube A) (a b : V) (hne : a ≠ b) :
    Function.Injective (fun i : ZMod 2 × ZMod 2 => squareCorner c a b i.1 i.2) := by
  intro ⟨s, t⟩ ⟨u, v⟩ h
  have hl := congrArg (fun x : QCube A => x.sgn a) h
  have hr := congrArg (fun x : QCube A => x.sgn b) h
  simp only [squareCorner_sgn_left _ _ _ hne] at hl
  simp only [squareCorner_sgn_right] at hr
  exact Prod.ext hl hr

theorem squareCorner_positive (c : QCube A) (a b : V) (hne : a ≠ b)
    (hs : c.spx = {a, b}) (s : ZMod 2) :
    squareCorner c a b s 0 = cubePositiveVertex (qCubeFacet c a s) :=
  qCubeFacet_zero_of_singleton _ b (squareFacet_w_spx c hne hs s)

theorem squareCorner_negative (c : QCube A) (a b : V) (hne : a ≠ b)
    (hs : c.spx = {a, b}) (s : ZMod 2) :
    squareCorner c a b s 1 = cubeNegativeVertex (qCubeFacet c a s) b :=
  qCubeFacet_one_of_singleton _ b (squareFacet_w_spx c hne hs s)

theorem squareCorner_swap (c : QCube A) (a b : V) (hne : a ≠ b) (s t : ZMod 2) :
    squareCorner c a b s t = squareCorner c b a t s :=
  qCubeFacet_comm c hne s t

end FiniteChains.Davis
