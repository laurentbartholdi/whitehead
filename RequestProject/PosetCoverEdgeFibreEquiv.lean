import RequestProject.PosetCoverStrictEdgeLift

namespace FiniteChains.Comb.IsPosetCover
universe u
variable {P Q : Type u} [PartialOrder P] [PartialOrder Q] {f : P → Q}
  (hf : IsPosetCover f)

/-- Transport along an actual strict edge sends its source fibre to its target fibre. -/
noncomputable def strictEdgeFibreTransport (e : StrictOrdEdge Q)
    (v : {p : P // f p = e.val.1}) : {p : P // f p = e.val.2} :=
  ⟨(hf.strictEdgeLiftFrom e v.val v.property).val.2,
    congrArg (fun r : StrictOrdEdge Q => r.val.2)
      (hf.strictEdgeLiftFrom_projection e v.val v.property)⟩

theorem strictEdgeFibreTransport_injective (e : StrictOrdEdge Q) :
    Function.Injective (hf.strictEdgeFibreTransport e) := by
  intro v w h
  apply Subtype.ext
  have ht := congrArg Subtype.val h
  change (hf.strictEdgeLiftFrom e v.val v.property).val.2 =
    (hf.strictEdgeLiftFrom e w.val w.property).val.2 at ht
  exact hf.down_inj
    (hf.strictEdgeLiftFrom e v.val v.property).property.le
    (ht.symm ▸ (hf.strictEdgeLiftFrom e w.val w.property).property.le)
    (v.property.trans w.property.symm)

theorem strictEdgeFibreTransport_surjective (e : StrictOrdEdge Q) :
    Function.Surjective (hf.strictEdgeFibreTransport e) := by
  intro q
  let r := hf.strictEdgeLiftTo e q.val q.property
  have hr : (strictOrderCxMap f hf.strictMono).onE r = e :=
    hf.strictEdgeLiftTo_projection e q.val q.property
  have hv : f r.val.1 = e.val.1 :=
    congrArg (fun s : StrictOrdEdge Q => s.val.1) hr
  refine ⟨⟨r.val.1, hv⟩, ?_⟩
  apply Subtype.ext
  have he := hf.strictEdgeLiftFrom_unique e r.val.1 hv r hr rfl
  exact (congrArg (fun s : StrictOrdEdge P => s.val.2) he).symm

/-- Actual source and target fibres of a strict edge are equivalent by unique edge lifting. -/
noncomputable def strictEdgeFibreEquiv (e : StrictOrdEdge Q) :
    {p : P // f p = e.val.1} ≃ {p : P // f p = e.val.2} :=
  Equiv.ofBijective (hf.strictEdgeFibreTransport e)
    ⟨hf.strictEdgeFibreTransport_injective e, hf.strictEdgeFibreTransport_surjective e⟩

end FiniteChains.Comb.IsPosetCover
