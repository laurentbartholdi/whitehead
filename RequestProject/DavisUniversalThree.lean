import RequestProject.DavisNerveCover
import RequestProject.DavisCellularAcyclic
import RequestProject.OrderUniversalThree

/-! Full-nerve degree-two exactness for the actual path-class universal cover of the cube quotient. -/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Davis
open RACG Mirror Comb
universe u
variable {V : Type u} [DecidableEq V] [Fintype V]

/-- The Davis covering comparison on vertices is an actual equivalence. -/
noncomputable def davisUniversalVertexEquiv (A : CommRel V) (a : Sph A) :
    UV (orderCx (QCube A)) (qProjCube a) ≃ Sph A :=
  @simplyConnectedCoverVertexEquiv (orderCx (Sph A)) (orderCx (QCube A))
    (orderCxMap qProjCube qProjCube_monotone) a isCovering_orderCxMap_qProjCube
    (isConnected_davis A) (simplyConnected_davis A)

noncomputable def davisUniversalFaceEquiv (A : CommRel V) (a : Sph A) :
    UF (orderCx (QCube A)) (qProjCube a) ≃ OrdTri (Sph A) :=
  @simplyConnectedCoverFaceEquiv (orderCx (Sph A)) (orderCx (QCube A))
    (orderCxMap qProjCube qProjCube_monotone) a isCovering_orderCxMap_qProjCube
    (isConnected_davis A) (simplyConnected_davis A)

/-- Degree-two exactness in the actual path-class universal cover, retaining its full
 three-cell boundary. No desired asphericity or homology premise is assumed. -/
theorem exists_universal_bdry3_of_cycle_davis (A : CommRel V) (a : Sph A)
    (z : UF (orderCx (QCube A)) (qProjCube a) →₀ ℤ)
    (hz : Comb.bdry2 (uCover (orderCx (QCube A)) (qProjCube a)) z = 0) :
    ∃ y : UOrdTet (QCube A) (qProjCube a) →₀ ℤ, uOrdBoundary3 y = z :=
  exists_uOrdBoundary3_of_cover_exact qProjCube_isPosetCover a
    (isConnected_davis A) (simplyConnected_davis A)
    (exists_cellular_bdry3_of_cycle_davis A) z hz

/-- The same exactness at every base vertex of the quotient. -/
theorem exists_universal_bdry3_of_cycle_qCube (A : CommRel V) (b : QCube A)
    (z : UF (orderCx (QCube A)) b →₀ ℤ)
    (hz : Comb.bdry2 (uCover (orderCx (QCube A)) b) z = 0) :
    ∃ y : UOrdTet (QCube A) b →₀ ℤ, uOrdBoundary3 y = z := by
  obtain ⟨a, rfl⟩ := qProjCube_isPosetCover.surj b
  exact exists_universal_bdry3_of_cycle_davis A a z hz

/-- The constructed lifted three-boundary squares to zero at every quotient base vertex. -/
theorem bdry2_uOrdBoundary3_qCube (A : CommRel V) (b : QCube A)
    (c : UOrdTet (QCube A) b →₀ ℤ) :
    Comb.bdry2 (uCover (orderCx (QCube A)) b) (uOrdBoundary3 c) = 0 := by
  obtain ⟨a, rfl⟩ := qProjCube_isPosetCover.surj b
  exact bdry2_uOrdBoundary3_of_scCover qProjCube_isPosetCover a (simplyConnected_davis A) c

/-- Full degree-two exactness for the actual universal-cover cells and boundary maps.
 The two-skeleton is not substituted for the full nerve in this statement. -/
theorem ker_bdry2_eq_range_uOrdBoundary3_qCube (A : CommRel V) (b : QCube A) :
    LinearMap.ker (Comb.bdry2 (uCover (orderCx (QCube A)) b)) =
      LinearMap.range (uOrdBoundary3 (P := QCube A) (a := b)) := by
  ext z
  rw [LinearMap.mem_ker, LinearMap.mem_range]
  constructor
  · exact exists_universal_bdry3_of_cycle_qCube A b z
  · rintro ⟨c, rfl⟩
    exact bdry2_uOrdBoundary3_qCube A b c

end FiniteChains.Davis
