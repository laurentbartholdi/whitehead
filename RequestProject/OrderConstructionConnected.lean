import RequestProject.OrderComponentLabels
import RequestProject.ConeAdjPoset
import RequestProject.CylinderPoset

namespace FiniteChains.Comb
universe u

 theorem cylP_isConnected {X S : Type u} [Preorder X] [Preorder S]
    (a : S →o X) (hc : IsConnected (orderCx X)) : IsConnected (orderCx (CylP a)) := by
  intro p q
  obtain ⟨l, hl⟩ := hc (cylRetr (X := X) a p) (cylRetr (X := X) a q)
  have hm : Reach (orderCx (CylP a)) (cylCollapse a p) (cylCollapse a q) :=
    ⟨_, isPath_mapPath (orderCxMap (cylIn a) (cylIn_monotone a)) hl⟩
  exact (orderComponentLabel_eq_iff _ _).mp
    ((orderComponentLabel_eq_of_le (le_cylIn_cylRetr (X := X) a p)).trans
      (((orderComponentLabel_eq_iff _ _).mpr hm).trans
        (orderComponentLabel_eq_of_le (le_cylIn_cylRetr (X := X) a q)).symm))

theorem coneAdj_isConnected {P T : Type u} [Preorder P] (S : T → P → Prop)
    (hc : IsConnected (orderCx P)) (hs : ∀ t, ∃ p, S t p) :
    IsConnected (orderCx (ConeAdj S)) := by
  have hv : ∀ v : ConeAdj S, ∃ p : P,
      orderComponentLabel _ v = orderComponentLabel _ (ConeAdj.inc (S := S) p) := by
    intro v
    cases v with
    | inl p => exact ⟨p, rfl⟩
    | inr t =>
      obtain ⟨p, hp⟩ := hs t
      exact ⟨p, (orderComponentLabel_eq_of_le (ConeAdj.inc_le_apex_of_mem hp)).symm⟩
  intro v w
  obtain ⟨p, hp⟩ := hv v
  obtain ⟨q, hq⟩ := hv w
  obtain ⟨l, hl⟩ := hc p q
  have hm : Reach (orderCx (ConeAdj S)) (ConeAdj.inc (S := S) p) (ConeAdj.inc (S := S) q) :=
    ⟨_, isPath_mapPath (orderCxMap (ConeAdj.inc (S := S)) (ConeAdj.inc_monotone (S := S))) hl⟩
  exact (orderComponentLabel_eq_iff _ _).mp
    (hp.trans (((orderComponentLabel_eq_iff _ _).mpr hm).trans hq.symm))

end FiniteChains.Comb
