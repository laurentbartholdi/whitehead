import RequestProject.PosetCoverUpTransform
import RequestProject.StrictOrderChains

namespace FiniteChains.Comb
universe u
variable {P Q : Type u} [PartialOrder P] [PartialOrder Q] {f : P → Q}
namespace IsPosetCover
variable (hf : IsPosetCover f)
include hf

/-- A genuine strict triangle lifts uniquely after its top vertex is specified. -/
theorem exists_unique_top_triangle (t : StrictOrdTri Q) (v : P) (hv : f v = t.1.2.2) :
    ∃! s : StrictOrdTri P,
      (strictOrderCxMap f hf.strictMono).onF s = t ∧ s.1.2.2 = v := by
  obtain ⟨b, ⟨hbv, hfb⟩, _⟩ := hf.down v t.1.2.1 (by rw [hv]; exact t.2.2.le)
  obtain ⟨a, ⟨hab, hfa⟩, _⟩ := hf.down b t.1.1 (by rw [hfb]; exact t.2.1.le)
  have hab' : a < b := lt_of_le_of_ne hab (by
    intro he
    exact (ne_of_lt t.2.1) (hfa.symm.trans ((congrArg f he).trans hfb)))
  have hbv' : b < v := lt_of_le_of_ne hbv (by
    intro he
    exact (ne_of_lt t.2.2) (hfb.symm.trans ((congrArg f he).trans hv)))
  let s : StrictOrdTri P := ⟨(a, b, v), hab', hbv'⟩
  refine ⟨s, ⟨?_, rfl⟩, ?_⟩
  · apply Subtype.ext
    exact Prod.ext hfa (Prod.ext hfb hv)
  · intro r hr
    have hfa' : f r.1.1 = t.1.1 := congrArg (fun t : StrictOrdTri Q => t.1.1) hr.1
    have hfb' : f r.1.2.1 = t.1.2.1 := congrArg (fun t : StrictOrdTri Q => t.1.2.1) hr.1
    have hra : r.1.1 ≤ v := hr.2 ▸ (r.2.1.le.trans r.2.2.le)
    have hrb : r.1.2.1 ≤ v := hr.2 ▸ r.2.2.le
    have ha : r.1.1 = a := hf.down_inj hra (hab.trans hbv) (hfa'.trans hfa.symm)
    have hb : r.1.2.1 = b := hf.down_inj hrb hbv (hfb'.trans hfb.symm)
    exact Subtype.ext (Prod.ext ha (Prod.ext hb hr.2))

end IsPosetCover
end FiniteChains.Comb
