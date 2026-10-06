import RequestProject.OrderConePathReplacement
import RequestProject.RelatorCircleConnected
import RequestProject.RelatorConeFundamentalChain
import RequestProject.ConeAdjBaseCover

namespace FiniteChains.PresModel
open Comb
universe u
variable {α J : Type u} (w : J → List (α × Bool)) (j : J)

/-- Actual mapped circle paths remain below their actual presentation apex. -/
theorem relatorCirclePath_below_apex (l : List ((orderCx (RelatorCircle w j)).E × Bool)) :
    PathIn (fun p => p ≤ apexOf w j)
      (mapPath (orderCxMap (relatorCirclePresInclusion w j)
        (relatorCirclePresInclusion_strictMono w j).monotone) l) := by
  intro e he
  obtain ⟨r, _, rfl⟩ := List.mem_map.mp he
  exact ⟨(relatorCirclePresInclusion_lt_apex w j r.1.val.1).le,
    (relatorCirclePresInclusion_lt_apex w j r.1.val.2).le⟩

/-- Actual mapped circle paths stay in the actual cylinder part of the presentation poset. -/
theorem relatorCirclePath_in_cylinder (l : List ((orderCx (RelatorCircle w j)).E × Bool)) :
    PathIn (fun p => p ∈ coneAdjBaseSet (S := circSet w))
      (mapPath (orderCxMap (relatorCirclePresInclusion w j)
        (relatorCirclePresInclusion_strictMono w j).monotone) l) := by
  intro e he
  obtain ⟨r, _, rfl⟩ := List.mem_map.mp he
  exact ⟨⟨cylOuter (aHom w) r.1.val.1.val, rfl⟩,
    ⟨cylOuter (aHom w) r.1.val.2.val, rfl⟩⟩

/-- An actual two-edge apex excursion can be replaced by an actual path in the cylinder. -/
theorem exists_presCone_excursion_replacement (hpos : 0 < (w j).length)
    (x y : RelatorCircle w j) :
    ∃ l : List ((orderCx (PresPos w)).E × Bool),
      IsPath (orderCx (PresPos w)).src (orderCx (PresPos w)).tgt l (iCirc w x.val) (iCirc w y.val) ∧
      PathIn (fun p => p ∈ coneAdjBaseSet (S := circSet w)) l ∧
      Htpy (orderCx (PresPos w)) (iCirc w x.val) (iCirc w y.val)
        [ordPos (relatorCirclePresInclusion_lt_apex w j x).le,
          ordNeg (relatorCirclePresInclusion_lt_apex w j y).le] l := by
  obtain ⟨l, hl⟩ := relatorCircle_isConnected w j hpos x y
  let I := orderCxMap (relatorCirclePresInclusion w j)
    (relatorCirclePresInclusion_strictMono w j).monotone
  refine ⟨mapPath I l, isPath_mapPath I hl, relatorCirclePath_in_cylinder w j l, ?_⟩
  exact (htpy_path_through_upper_bound (apexOf w j)
    (relatorCirclePresInclusion_lt_apex w j x).le
    (relatorCirclePresInclusion_lt_apex w j y).le
    (isPath_mapPath I hl) (relatorCirclePath_below_apex w j l)).symm

/-- Every genuine apex excursion, with arbitrary actual strict lower endpoints, has a cylinder replacement. -/
theorem exists_presCone_strict_excursion_replacement (hpos : 0 < (w j).length)
    (x y : PresPos w) (hx : x < apexOf w j) (hy : y < apexOf w j) :
    ∃ l : List ((orderCx (PresPos w)).E × Bool),
      IsPath (orderCx (PresPos w)).src (orderCx (PresPos w)).tgt l x y ∧
      PathIn (fun p => p ∈ coneAdjBaseSet (S := circSet w)) l ∧
      Htpy (orderCx (PresPos w)) x y [ordPos hx.le, ordNeg hy.le] l := by
  obtain ⟨a, ha⟩ := relatorCircleToBelow_surjective w j ⟨x, hx⟩
  obtain ⟨b, hb⟩ := relatorCircleToBelow_surjective w j ⟨y, hy⟩
  have hax : iCirc w a.val = x := congrArg Subtype.val ha
  have hby : iCirc w b.val = y := congrArg Subtype.val hb
  subst x
  subst y
  exact exists_presCone_excursion_replacement w j hpos a b

/-- Actual apex-excursion substitution preserves endpoints inside an arbitrary surrounding path. -/
theorem exists_presCone_excursion_substitution (hpos : 0 < (w j).length)
    {a b x y : PresPos w} (hx : x < apexOf w j) (hy : y < apexOf w j)
    (r s : List ((orderCx (PresPos w)).E × Bool))
    (hr : IsPath (orderCx (PresPos w)).src (orderCx (PresPos w)).tgt r a x)
    (hs : IsPath (orderCx (PresPos w)).src (orderCx (PresPos w)).tgt s y b) :
    ∃ l : List ((orderCx (PresPos w)).E × Bool),
      IsPath (orderCx (PresPos w)).src (orderCx (PresPos w)).tgt l x y ∧
      PathIn (fun p => p ∈ coneAdjBaseSet (S := circSet w)) l ∧
      Htpy (orderCx (PresPos w)) a b
        (r ++ [ordPos hx.le, ordNeg hy.le] ++ s) (r ++ l ++ s) := by
  obtain ⟨l, hl, hc, hh⟩ := exists_presCone_strict_excursion_replacement w j hpos x y hx hy
  exact ⟨l, hl, hc, hh.congr_append hr hs⟩

end FiniteChains.PresModel
