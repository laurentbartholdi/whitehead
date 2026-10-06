import RequestProject.CombPi1

namespace FiniteChains.Comb
universe u

section Inverse

/-- The two-sided inverse supplied by `Function.surjInv` for a bijection. -/
private theorem surjInv_apply_apply {α β : Type u} {f : α → β} (hf : Function.Bijective f)
    (x : α) : Function.surjInv hf.2 (f x) = x :=
  hf.1 (Function.surjInv_eq hf.2 (f x))

variable {L E : Complex2.{u}} (ι : Hom L E)
variable (hV : Function.Bijective ι.onV) (hE : Function.Bijective ι.onE)
  (hF : Function.Bijective ι.onF)

private theorem map_surjInv_map (q : List (L.E × Bool)) :
    ((q.map fun eb => (ι.onE eb.1, eb.2)).map
      fun eb => (Function.surjInv hE.2 eb.1, eb.2)) = q := by
  induction q with
  | nil => rfl
  | cons a t ih => simp [ih, surjInv_apply_apply hE]

private theorem map_map_surjInv (q : List (E.E × Bool)) :
    ((q.map fun eb => (Function.surjInv hE.2 eb.1, eb.2)).map
      fun eb => (ι.onE eb.1, eb.2)) = q := by
  induction q with
  | nil => rfl
  | cons a t ih => simp [ih, Function.surjInv_eq hE.2]

/-- The inverse of a cellular map which is bijective on cells. -/
noncomputable def homInv : Hom E L where
  onV := Function.surjInv hV.2
  onE := Function.surjInv hE.2
  onF := Function.surjInv hF.2
  src_onE := by
    intro e
    obtain ⟨e', rfl⟩ := hE.2 e
    rw [surjInv_apply_apply hE, ι.src_onE, surjInv_apply_apply hV]
  tgt_onE := by
    intro e
    obtain ⟨e', rfl⟩ := hE.2 e
    rw [surjInv_apply_apply hE, ι.tgt_onE, surjInv_apply_apply hV]
  base_onF := by
    intro f
    obtain ⟨f', rfl⟩ := hF.2 f
    rw [surjInv_apply_apply hF, ι.base_onF, surjInv_apply_apply hV]
  att_onF := by
    intro f
    obtain ⟨f', rfl⟩ := hF.2 f
    rw [surjInv_apply_apply hF, ι.att_onF]
    exact (map_surjInv_map ι hE (L.att f')).symm

@[simp] theorem homInv_onV_apply (y : E.V) : ι.onV ((homInv ι hV hE hF).onV y) = y :=
  Function.surjInv_eq hV.2 y

@[simp] theorem homInv_onE_apply (e : E.E) : ι.onE ((homInv ι hV hE hF).onE e) = e :=
  Function.surjInv_eq hE.2 e

@[simp] theorem homInv_onF_apply (f : E.F) : ι.onF ((homInv ι hV hE hF).onF f) = f :=
  Function.surjInv_eq hF.2 f

@[simp] theorem homInv_onV_comp (x : L.V) : (homInv ι hV hE hF).onV (ι.onV x) = x :=
  surjInv_apply_apply hV x

@[simp] theorem homInv_onE_comp (e : L.E) : (homInv ι hV hE hF).onE (ι.onE e) = e :=
  surjInv_apply_apply hE e

@[simp] theorem homInv_onF_comp (f : L.F) : (homInv ι hV hE hF).onF (ι.onF f) = f :=
  surjInv_apply_apply hF f

theorem mapPath_homInv (q : List (L.E × Bool)) :
    mapPath (homInv ι hV hE hF) (mapPath ι q) = q :=
  map_surjInv_map ι hE q

theorem mapPath_homInv' (q : List (E.E × Bool)) :
    mapPath ι (mapPath (homInv ι hV hE hF) q) = q :=
  map_map_surjInv ι hE q

end Inverse

end FiniteChains.Comb
