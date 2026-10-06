import RequestProject.PosetCoverUpTransform
import RequestProject.StrictOrderComplex

namespace FiniteChains.Comb.IsPosetCover
universe u
variable {P Q : Type u} [PartialOrder P] [PartialOrder Q] {f : P → Q}
  (hf : IsPosetCover f)

/-- The actual unique lift of a strict edge from a specified actual source vertex. -/
noncomputable def strictEdgeLiftFrom (e : StrictOrdEdge Q) (v : P) (hv : f v = e.1.1) :
    StrictOrdEdge P := by
  let h : f v ≤ e.1.2 := hv.symm ▸ e.2.le
  let q := Classical.choose (hf.up v e.1.2 h)
  have hq : v ≤ q ∧ f q = e.1.2 := (Classical.choose_spec (hf.up v e.1.2 h)).1
  exact ⟨(v, q), lt_of_le_of_ne hq.1 (by
    intro he
    exact e.2.ne (hv.symm.trans ((congrArg f he).trans hq.2)))⟩

theorem strictEdgeLiftFrom_source (e : StrictOrdEdge Q) (v : P) (hv : f v = e.1.1) :
    (hf.strictEdgeLiftFrom e v hv).1.1 = v := rfl

theorem strictEdgeLiftFrom_projection (e : StrictOrdEdge Q) (v : P) (hv : f v = e.1.1) :
    (strictOrderCxMap f hf.strictMono).onE (hf.strictEdgeLiftFrom e v hv) = e := by
  apply Subtype.ext
  apply Prod.ext hv
  exact (Classical.choose_spec (hf.up v e.1.2 (hv.symm ▸ e.2.le))).1.2

theorem strictEdgeLiftFrom_unique (e : StrictOrdEdge Q) (v : P) (hv : f v = e.1.1)
    (r : StrictOrdEdge P) (hr : (strictOrderCxMap f hf.strictMono).onE r = e)
    (hs : r.1.1 = v) : r = hf.strictEdgeLiftFrom e v hv := by
  apply Subtype.ext
  apply Prod.ext hs
  have hp := congrArg (fun s : StrictOrdEdge Q => s.1.2)
    (hr.trans (hf.strictEdgeLiftFrom_projection e v hv).symm)
  exact hf.up_inj (a := v) (hs ▸ r.2.le) (hf.strictEdgeLiftFrom e v hv).2.le hp

/-- The actual unique lift of a strict edge to a specified actual target vertex. -/
noncomputable def strictEdgeLiftTo (e : StrictOrdEdge Q) (v : P) (hv : f v = e.1.2) :
    StrictOrdEdge P := by
  let h : e.1.1 ≤ f v := hv.symm ▸ e.2.le
  let q := Classical.choose (hf.down v e.1.1 h)
  have hq : q ≤ v ∧ f q = e.1.1 := (Classical.choose_spec (hf.down v e.1.1 h)).1
  exact ⟨(q, v), lt_of_le_of_ne hq.1 (by
    intro he
    exact e.2.ne (hq.2.symm.trans ((congrArg f he).trans hv)))⟩

theorem strictEdgeLiftTo_target (e : StrictOrdEdge Q) (v : P) (hv : f v = e.1.2) :
    (hf.strictEdgeLiftTo e v hv).1.2 = v := rfl

theorem strictEdgeLiftTo_projection (e : StrictOrdEdge Q) (v : P) (hv : f v = e.1.2) :
    (strictOrderCxMap f hf.strictMono).onE (hf.strictEdgeLiftTo e v hv) = e := by
  apply Subtype.ext
  apply Prod.ext
  · exact (Classical.choose_spec (hf.down v e.1.1 (hv.symm ▸ e.2.le))).1.2
  · exact hv

theorem strictEdgeLiftTo_unique (e : StrictOrdEdge Q) (v : P) (hv : f v = e.1.2)
    (r : StrictOrdEdge P) (hr : (strictOrderCxMap f hf.strictMono).onE r = e)
    (ht : r.1.2 = v) : r = hf.strictEdgeLiftTo e v hv := by
  apply Subtype.ext
  apply Prod.ext
  · have hp := congrArg (fun s : StrictOrdEdge Q => s.1.1)
      (hr.trans (hf.strictEdgeLiftTo_projection e v hv).symm)
    exact hf.down_inj (a := v) (ht ▸ r.2.le) (hf.strictEdgeLiftTo e v hv).2.le hp
  · exact ht

end FiniteChains.Comb.IsPosetCover
