import RequestProject.OrderCxNatHtpy
import RequestProject.OrderCxConeNull

/-! Null homotopies transfer through an actual order homotopy, including changing bases. -/
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb

theorem htpy_nil_of_conjugate {X : Complex2} {a b : X.V}
    {e p : List (X.E × Bool)} (he : IsPath X.src X.tgt e a b)
    (hp : IsPath X.src X.tgt p a a)
    (h : Htpy X b b (revPath e ++ p ++ e) []) : Htpy X a a p [] := by
  have hc := htpy_append_revPath he
  have hA := hc.congr_append (show IsPath X.src X.tgt [] a a from rfl)
    (hp.append (he.append (isPath_revPath he)))
  have hB := hc.congr_append hp (show IsPath X.src X.tgt [] a a from rfl)
  have hstrip : Htpy X a a (e ++ (revPath e ++ p ++ e) ++ revPath e) p := by
    simpa [List.append_assoc] using hA.trans (by simpa using hB)
  have hstep := h.congr_append he (isPath_revPath he)
  have hkill : Htpy X a a (e ++ (revPath e ++ p ++ e) ++ revPath e) [] :=
    hstep.trans (by simpa using hc)
  exact hstrip.symm.trans hkill

variable {P Q : Type} [Preorder P] [Preorder Q]

/-- Pointwise comparable monotone maps preserve and reflect null homotopy of their images.
The proof uses the connecting edge at the base and cancels it, so fixed bases are unnecessary. -/
theorem htpy_nil_mapPath_le_iff {f g : P → Q} (hf : Monotone f) (hg : Monotone g)
    (hfg : ∀ x, f x ≤ g x) {a : P} {p : List ((orderCx P).E × Bool)}
    (hp : IsPath (orderCx P).src (orderCx P).tgt p a a) :
    Htpy (orderCx Q) (f a) (f a) (mapPath (orderCxMap f hf) p) [] ↔
      Htpy (orderCx Q) (g a) (g a) (mapPath (orderCxMap g hg) p) [] := by
  have hnat := htpy_loop_mapPath_le hf hg hfg hp
  constructor
  · intro h
    have hh := h.congr_append (isPath_ordNeg (hfg a)) (isPath_ordPos (hfg a))
    exact hnat.trans (hh.trans (by simpa using htpy_ordNeg_ordPos (hfg a)))
  · intro h
    apply htpy_nil_of_conjugate (isPath_ordPos (hfg a))
      (isPath_mapPath (orderCxMap f hf) hp)
    simpa [revPath, revGerm, ordPos, ordNeg, Bool.not] using hnat.symm.trans h

/-- An explicit three-step order contraction gives simple connectedness. -/
theorem simplyConnected_orderCx_of_zigzag {f g : P → P}
    (hf : Monotone f) (hg : Monotone g) (hig : ∀ x, x ≤ g x)
    (hfg : ∀ x, f x ≤ g x) (d : P) (hfd : ∀ x, f x ≤ d) :
    SimplyConnected (orderCx P) := by
  intro a p hp
  have hc := htpy_nil_mapPath_const d hp
  have hfnil := (htpy_nil_mapPath_le_iff hf monotone_const hfd hp).mpr hc
  have hgnil := (htpy_nil_mapPath_le_iff hf hg hfg hp).mp hfnil
  have hinil := (htpy_nil_mapPath_le_iff monotone_id hg hig hp).mpr hgnil
  simpa [mapPath, orderCxMap] using hinil

/-- The same contraction supplies paths to the common point, hence connectedness. -/
theorem isConnected_orderCx_of_zigzag {f g : P → P}
    (hig : ∀ x, x ≤ g x) (hfg : ∀ x, f x ≤ g x)
    (d : P) (hfd : ∀ x, f x ≤ d) : IsConnected (orderCx P) := by
  let p (a : P) : List ((orderCx P).E × Bool) :=
    [ordPos (hig a), ordNeg (hfg a), ordPos (hfd a)]
  have hp (a : P) : IsPath (orderCx P).src (orderCx P).tgt (p a) a d :=
    ⟨rfl, rfl, rfl, rfl⟩
  intro a b
  exact ⟨p a ++ revPath (p b), (hp a).append (isPath_revPath (hp b))⟩

end FiniteChains.Comb
