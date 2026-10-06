module

public import RequestProject.CombPi2
public import RequestProject.CombData

@[expose] public section

namespace FiniteChains.Comb
universe u
variable {K : Complex2.{u}} {x y : K.V}

/-- Transport of the genuine universal cover along equality of base points. -/
noncomputable def uCoverBaseTransport (h : x = y) : Hom (uCover K x) (uCover K y) := by
  cases h
  exact Hom.id _

theorem uCoverBaseTransport_base (h : x = y) :
    (uCoverBaseTransport h).onV (UV.base K x) = UV.base K y := by
  cases h
  rfl

theorem uCoverBaseTransport_edge (h : x = y) (e : UE K x) :
    ((uCoverBaseTransport h).onE e).1.2 = e.1.2 := by
  cases h
  rfl

theorem uCoverBaseTransport_face (h : x = y) (t : UF K x) :
    ((uCoverBaseTransport h).onF t).1.2 = t.1.2 := by
  cases h
  rfl

end FiniteChains.Comb
