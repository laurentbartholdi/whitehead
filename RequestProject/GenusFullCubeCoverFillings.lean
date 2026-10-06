import RequestProject.GenusFullCubeMarking
import RequestProject.CombUniversalCover
import RequestProject.CellularHomotopyChain

/-! Genuine cap fillings in the path-class universal cover of the full cube quotient. -/
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb
universe u
variable {X : Complex2.{u}} {a : X.V}

/-- A null-homotopic loop has a finite chain filling after lifting at any cover vertex. -/
theorem exists_lifted_boundary_of_null {v : UV X a}
    {p : List (X.E × Bool)}
    (hp : IsPath X.src X.tgt p (endV v) (endV v))
    (hn : Htpy X (endV v) (endV v) p []) :
    ∃ c : (uCover X a).F →₀ ℤ,
      bdry2 (uCover X a) c = pathChain (uLiftPath p v) := by
  have he : extendList p v = v := by
    simpa using extendList_htpy hp hn
  have hl : IsPath (uCover X a).src (uCover X a).tgt (uLiftPath p v) v v := by
    have h := isPath_uLiftPath p v (endV v) hp
    rwa [he] at h
  simpa using (simplyConnected_univCover v _ hl).exists_boundary

end FiniteChains.Comb

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb
variable (q : ℕ) [NeZero q]

/-- Every exact marked cap loop has a filling at every vertex over its base point. -/
theorem fullCubeCover_cap_filling {a : QCube (cmpRel (GenusVertex q))}
    (x : Fin q × Bool) (v : UV (orderCx (QCube (cmpRel (GenusVertex q)))) a)
    (hv : endV v = (markedSpineToFullCube q).onV (markedSpineBase q)) :
    ∃ c : (uCover (orderCx (QCube (cmpRel (GenusVertex q)))) a).F →₀ ℤ,
      Comb.bdry2 _ c = pathChain
        (uLiftPath (mapPath (markedSpineToFullCube q) (markedSpineLoop q x).1) v) := by
  apply exists_lifted_boundary_of_null
  · rw [hv]
    exact isPath_mapPath (markedSpineToFullCube q) (markedSpineLoop q x).2
  · rw [hv]
    exact markedSpineToFullCube_mark_null q x

/-- A chosen filling uses actual universal-cover faces and their actual cellular boundary. -/
noncomputable def fullCubeCoverCapChain {a : QCube (cmpRel (GenusVertex q))}
    (x : Fin q × Bool) (v : UV (orderCx (QCube (cmpRel (GenusVertex q)))) a)
    (hv : endV v = (markedSpineToFullCube q).onV (markedSpineBase q)) :
    (uCover (orderCx (QCube (cmpRel (GenusVertex q)))) a).F →₀ ℤ :=
  Classical.choose (fullCubeCover_cap_filling q x v hv)

theorem fullCubeCoverCapChain_boundary {a : QCube (cmpRel (GenusVertex q))}
    (x : Fin q × Bool) (v : UV (orderCx (QCube (cmpRel (GenusVertex q)))) a)
    (hv : endV v = (markedSpineToFullCube q).onV (markedSpineBase q)) :
    Comb.bdry2 _ (fullCubeCoverCapChain q x v hv) = pathChain
      (uLiftPath (mapPath (markedSpineToFullCube q) (markedSpineLoop q x).1) v) :=
  Classical.choose_spec (fullCubeCover_cap_filling q x v hv)

end FiniteChains.Davis.Genus
