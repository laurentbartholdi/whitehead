import RequestProject.CellularHomotopyChain
import RequestProject.GenusFiniteMarking

/-! Cellular filling chains of the actual marked surface words. -/

namespace FiniteChains.Davis
open Comb
universe u
variable {X : Complex2.{u}} {a : X.V} {ι : Type u}

/-- The edge path spelling a product of commutators of marked loops. -/
def surfacePath (f : ι → Loop X a) : List (ι × ι) → List (X.E × Bool)
  | [] => []
  | p :: ps => (f p.1).1 ++ (f p.2).1 ++ revPath (f p.1).1 ++
      revPath (f p.2).1 ++ surfacePath f ps

theorem surfacePath_isLoop (f : ι → Loop X a) (ps : List (ι × ι)) :
    IsPath X.src X.tgt (surfacePath f ps) a a := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    exact ((((f p.1).2.append (f p.2).2).append (isPath_revPath (f p.1).2)).append
      (isPath_revPath (f p.2).2)).append ih

theorem surfacePath_class (f : ι → Loop X a) (ps : List (ι × ι)) :
    Pi1.mk ⟨surfacePath f ps, surfacePath_isLoop f ps⟩ =
      commWord (fun i => Pi1.mk (f i)) ps := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    rw [commWord_cons, ← ih]
    rfl

/-- The signed edge chain of a surface word vanishes before quotienting by boundaries. -/
theorem surfacePath_chain (f : ι → Loop X a) (ps : List (ι × ι)) :
    pathChain (surfacePath f ps) = 0 := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    simp only [surfacePath, pathChain_append, pathChain_revPath, ih]
    abel

/-- The canonical surface word bounds by its proved edge-path relation. -/
theorem surfacePath_nullhomotopic (f : ι → Loop X a) (ps : List (ι × ι))
    (hf : commWord (fun i => Pi1.mk (f i)) ps = 1) :
    Htpy X a a (surfacePath f ps) [] := by
  have he : Pi1.mk ⟨surfacePath f ps, surfacePath_isLoop f ps⟩ =
      Pi1.mk (⟨[], rfl⟩ : Loop X a) := (surfacePath_class f ps).trans hf
  exact Quotient.exact he

namespace Genus
variable (q : ℕ) [NeZero q]

noncomputable def finiteMarkedLoops (x : Fin q × Bool) :
    Loop (sdCx (gc q)) (gBase q) :=
  ⟨finiteSig q x, isPath_gSig q (x.1.val, x.2)⟩

theorem finiteSurfacePath_nullhomotopic :
    Htpy (sdCx (gc q)) (gBase q) (gBase q)
      (surfacePath (finiteMarkedLoops q) (finitePairs q)) [] :=
  surfacePath_nullhomotopic _ _ (finite_hfilling q)

theorem finiteSurfacePath_chain_zero :
    pathChain (surfacePath (finiteMarkedLoops q) (finitePairs q)) = 0 :=
  surfacePath_chain _ _

end Genus
end FiniteChains.Davis
