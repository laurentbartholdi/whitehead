import RequestProject.OrderPosetCovering
import RequestProject.PosetCoverUpTransform
import RequestProject.StrictOrderComplex

/-! A poset covering restricts to the genuine nondegenerate cellular
two-skeleton. This is the cover used with strict cellular acyclicity.
Unverified source. -/

namespace FiniteChains.Comb.IsPosetCover
universe u
variable {P Q : Type u} [PartialOrder P] [PartialOrder Q] {f : P → Q}
  (hf : IsPosetCover f)

def strictMap : Hom (strictOrderCx P) (strictOrderCx Q) := strictOrderCxMap f hf.strictMono

theorem strictMap_isCovering : IsCovering hf.strictMap := by
  refine ⟨hf.surj, ?_, ?_⟩
  · intro a
    change P at a
    constructor
    · rintro ⟨⟨e, b⟩, he⟩ ⟨⟨e', b'⟩, he'⟩ hEq
      have hb : b = b' := congrArg (fun g : Germ (strictOrderCx Q) _ => g.val.2) hEq
      subst b'
      have hpair : (f e.val.1, f e.val.2) = (f e'.val.1, f e'.val.2) :=
        congrArg (fun g : Germ (strictOrderCx Q) _ => g.val.1.val) hEq
      have h₁ := congrArg Prod.fst hpair
      have h₂ := congrArg Prod.snd hpair
      apply Subtype.ext
      refine Prod.ext ?_ rfl
      cases b with
      | false =>
          have hea : e.val.2 = a := he
          have hea' : e'.val.2 = a := he'
          have hfst := hf.down_inj (a := a)
            (by rw [← hea]; exact e.property.le)
            (by rw [← hea']; exact e'.property.le) h₁
          exact Subtype.ext (Prod.ext hfst (hea.trans hea'.symm))
      | true =>
          have hea : e.val.1 = a := he
          have hea' : e'.val.1 = a := he'
          have hsnd := hf.up_inj (a := a)
            (by rw [← hea]; exact e.property.le)
            (by rw [← hea']; exact e'.property.le) h₂
          exact Subtype.ext (Prod.ext (hea.trans hea'.symm) hsnd)
    · rintro ⟨⟨d, b⟩, hd⟩
      cases b with
      | true =>
          have hfa : f a = d.val.1 := hd.symm
          obtain ⟨c, ⟨hac, hfc⟩, _⟩ := hf.up a d.val.2 (by rw [hfa]; exact d.property.le)
          have hac' : a < c := lt_of_le_of_ne hac (fun he =>
            d.property.ne (hfa.symm.trans ((congrArg f he).trans hfc)))
          refine ⟨⟨(⟨(a, c), hac'⟩, true), rfl⟩, ?_⟩
          exact Subtype.ext (Prod.ext (Subtype.ext (Prod.ext hfa hfc)) rfl)
      | false =>
          have hfa : f a = d.val.2 := hd.symm
          obtain ⟨c, ⟨hca, hfc⟩, _⟩ := hf.down a d.val.1 (by rw [hfa]; exact d.property.le)
          have hca' : c < a := lt_of_le_of_ne hca (fun he =>
            d.property.ne (hfc.symm.trans ((congrArg f he).trans hfa)))
          refine ⟨⟨(⟨(c, a), hca'⟩, false), rfl⟩, ?_⟩
          exact Subtype.ext (Prod.ext (Subtype.ext (Prod.ext hfc hfa)) rfl)
  · constructor
    · intro t t' hEq
      have hbase : t.val.1 = t'.val.1 := congrArg (fun z => z.val.2) hEq
      have htri : (f t.val.1, f t.val.2.1, f t.val.2.2) =
          (f t'.val.1, f t'.val.2.1, f t'.val.2.2) := congrArg (fun z => z.val.1.val) hEq
      have hmid := hf.up_inj t.property.1.le
        (by rw [hbase]; exact t'.property.1.le)
        (congrArg (fun z : Q × Q × Q => z.2.1) htri)
      have htop := hf.up_inj (t.property.1.trans t.property.2).le
        (by rw [hbase]; exact (t'.property.1.trans t'.property.2).le)
        (congrArg (fun z : Q × Q × Q => z.2.2) htri)
      exact Subtype.ext (Prod.ext hbase (Prod.ext hmid htop))
    · rintro ⟨⟨s, a⟩, hs⟩
      change P at a
      have hfa : f a = s.val.1 := hs.symm
      obtain ⟨b, ⟨hab, hfb⟩, _⟩ := hf.up a s.val.2.1 (by rw [hfa]; exact s.property.1.le)
      obtain ⟨c, ⟨hbc, hfc⟩, _⟩ := hf.up b s.val.2.2 (by rw [hfb]; exact s.property.2.le)
      have hab' : a < b := lt_of_le_of_ne hab (fun he =>
        s.property.1.ne (hfa.symm.trans ((congrArg f he).trans hfb)))
      have hbc' : b < c := lt_of_le_of_ne hbc (fun he =>
        s.property.2.ne (hfb.symm.trans ((congrArg f he).trans hfc)))
      refine ⟨⟨(a, b, c), hab', hbc'⟩, ?_⟩
      exact Subtype.ext (Prod.ext (Subtype.ext (Prod.ext hfa (Prod.ext hfb hfc))) rfl)

end FiniteChains.Comb.IsPosetCover
