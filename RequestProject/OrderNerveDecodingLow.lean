module

public import RequestProject.OrderNerveOneDecoding

@[expose] public section

namespace FiniteChains.Comb
open FreeAbelianGroup
universe u
variable {P : Type u}

@[simp] theorem decodeOrdNerve0_of (l : List P) :
    decodeOrdNerve0 (of l) = decodeOrdVertexList l := lift_apply_of _ _

theorem ordNerveChain0_decode (c : Nerve.Ch P) :
    ordNerveChain0 (decodeOrdNerve0 c) = Nerve.lengthProjection 1 c := by
  classical
  apply Nerve.ext_apply
    (F := ordNerveChain0.toAddMonoidHom.comp decodeOrdNerve0) (G := Nerve.lengthProjection 1)
  intro l
  cases l with
  | nil => simp [decodeOrdVertexList]
  | cons a l =>
    cases l with
    | nil => simp [decodeOrdVertexList, ordNerveChain0]
    | cons b l => simp [decodeOrdVertexList]

end FiniteChains.Comb
