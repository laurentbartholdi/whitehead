module

public import RequestProject.OrderComplexFreeFace
public import RequestProject.OrderCxNatHtpy

@[expose] public section

/-! Constructed loop representatives under the first elementary collapse deletion. -/
namespace FiniteChains.Comb
variable {P : Type} [PartialOrder P]

/-- Every loop based in `B` has a representative in `B` under an increasing order map
from `C` to `B`. The connecting germs at its base are included explicitly. -/
theorem loop_representative_of_monotone_map {C B : P → Prop}
    (hBC : ∀ x, B x → C x) (r : {x : P // C x} → P) (hr : Monotone r)
    (hrB : ∀ x, B (r x)) (hle : ∀ x, x.1 ≤ r x)
    {a : P} {p : List ((orderCx P).E × Bool)} (ha : B a)
    (hp : IsPath (orderCx P).src (orderCx P).tgt p a a) (hC : PathIn C p) :
    ∃ l, IsPath (orderCx P).src (orderCx P).tgt l a a ∧ PathIn B l ∧
      Htpy (orderCx P) a a p l := by
  let aC : {x : P // C x} := ⟨a, hBC a ha⟩
  let l := mapPath (orderCxMap r hr) (liftPathIn p hC)
  have hl : IsPath (orderCx P).src (orderCx P).tgt l (r aC) (r aC) :=
    isPath_mapPath (orderCxMap r hr) (isPath_liftPathIn p hC aC.2 aC.2 hp)
  have hlB : PathIn B l := by
    intro e he
    obtain ⟨eb, _, rfl⟩ := List.mem_map.mp he
    exact ⟨hrB eb.1.1.1, hrB eb.1.1.2⟩
  let e := [ordPos (hle aC)]
  let en := [ordNeg (hle aC)]
  have he : IsPath (orderCx P).src (orderCx P).tgt e a (r aC) := isPath_ordPos _
  have hen : IsPath (orderCx P).src (orderCx P).tgt en (r aC) a := isPath_ordNeg _
  have heB : PathIn B e := pathIn_cons ⟨ha, hrB aC⟩ (pathIn_nil B)
  have henB : PathIn B en := pathIn_cons ⟨ha, hrB aC⟩ (pathIn_nil B)
  have hnat := htpy_mapPath_le monotone_subtypeVal hr hle
    (liftPathIn p hC) (isPath_liftPathIn p hC aC.2 aC.2 hp)
  change Htpy (orderCx P) a (r aC)
    (mapPath (subposetHom C) (liftPathIn p hC) ++ e) (e ++ l) at hnat
  rw [mapPath_liftPathIn] at hnat
  have hpush := hnat.congr_append (show IsPath (orderCx P).src (orderCx P).tgt [] a a from rfl) hen
  have hkill := (htpy_ordPos_ordNeg (hle aC)).congr_append hp
    (show IsPath (orderCx P).src (orderCx P).tgt [] a a from rfl)
  refine ⟨e ++ l ++ en, (he.append hl).append hen,
    pathIn_append (pathIn_append heB hlB) henB, ?_⟩
  have hstrip : Htpy (orderCx P) a a p ((p ++ e) ++ en) := by
    simpa [e, en, List.append_assoc] using hkill.symm
  exact hstrip.trans (by simpa only [List.nil_append] using hpush)

/-- Deleting an actual free face preserves representatives of all loops based away from it. -/
theorem loop_representative_delete_free_face {C : P → Prop} {f t a : P}
    (ht : C t) (hft : f ≤ t) (hne : t ≠ f)
    (hunique : ∀ x, C x → f ≤ x → x ≠ f → x = t)
    {p : List ((orderCx P).E × Bool)} (ha : C a ∧ a ≠ f)
    (hp : IsPath (orderCx P).src (orderCx P).tgt p a a) (hC : PathIn C p) :
    ∃ l, IsPath (orderCx P).src (orderCx P).tgt l a a ∧
      PathIn (fun x => C x ∧ x ≠ f) l ∧ Htpy (orderCx P) a a p l := by
  classical
  let r : {x : P // C x} → P := fun x => if x.1 = f then t else x.1
  have hr : Monotone r := by
    intro x y hxy
    by_cases hx : x.1 = f
    · by_cases hy : y.1 = f
      · simp [r, hx, hy]
      · have hyt : y.1 = t := hunique y.1 y.2 (hx ▸ hxy) hy
        simp [r, hx, hyt]
    · by_cases hy : y.1 = f
      · have hxf : x.1 ≤ f := hy ▸ hxy
        simpa [r, hx, hy] using hxf.trans hft
      · simpa [r, hx, hy] using hxy
  apply loop_representative_of_monotone_map (fun _ h => h.1) r hr ?_ ?_ ha hp hC
  · intro x
    by_cases hx : x.1 = f
    · simpa [r, hx] using And.intro ht hne
    · simpa [r, hx] using And.intro x.2 hx
  · intro x
    by_cases hx : x.1 = f
    · simpa [r, hx] using hft
    · simp [r, hx]

end FiniteChains.Comb
