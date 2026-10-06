module

public import RequestProject.RoseStrictEdges
public import RequestProject.RelatorCircleEdges

@[expose] public section

namespace FiniteChains.PresModel
open Comb
universe u
variable {α J : Type u} (w : J → List (α × Bool)) (j : J)

/-- The actual attaching map preserves strict comparability on each valid relator circle. -/
theorem relatorCircleAttaching_strictMono :
    StrictMono (fun x : RelatorCircle w j => aFun w x.val) := by
  have he : ∀ e : StrictOrdEdge (RelatorCircle w j),
      aFun w e.val.1.val < aFun w e.val.2.val := by
    intro e
    obtain ⟨k, he⟩ := relatorCircle_edge_cases w j e
    obtain ⟨a, ha⟩ := exists_get_of_lt w k.isLt
    rcases he with rfl | rfl | rfl | rfl
    · change aFun w (TCirc.pt w j k.val CPos.cor) <
        aFun w (TCirc.pt w j k.val CPos.cedgL)
      rw [aFun_pt_cor, aFun_pt_cedgL_of_get w ha]
      exact (roseBaseEdge a.1 (!a.2)).property
    · change aFun w (TCirc.pt w j k.val CPos.cmid) <
        aFun w (TCirc.pt w j k.val CPos.cedgL)
      rw [aFun_pt_cmid_of_get w ha, aFun_pt_cedgL_of_get w ha]
      exact (roseMidEdge a.1 (!a.2)).property
    · change aFun w (TCirc.pt w j k.val CPos.cmid) <
        aFun w (TCirc.pt w j k.val CPos.cedgR)
      rw [aFun_pt_cmid_of_get w ha, aFun_pt_cedgR_of_get w ha]
      exact (roseMidEdge a.1 a.2).property
    · change aFun w (TCirc.pt w j (relatorCircleNext w j k).val CPos.cor) <
        aFun w (TCirc.pt w j k.val CPos.cedgR)
      rw [aFun_pt_cor, aFun_pt_cedgR_of_get w ha]
      exact (roseBaseEdge a.1 a.2).property
  intro x y h
  exact he ⟨(x, y), h⟩

end FiniteChains.PresModel
