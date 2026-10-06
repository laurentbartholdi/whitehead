import RequestProject.PresConeLinkOrderIso
import RequestProject.PresValidFinite

namespace FiniteChains.PresModel
open scoped Classical
universe u
variable {α J : Type u} (w : J → List (α × Bool)) (j : J)

instance relatorCircle_finite : Finite (RelatorCircle w j) := by
  let f : RelatorCircle w j → Fin (w j).length × CPos :=
    fun x => (⟨x.val.2.1, x.property.2⟩, x.val.2.2)
  apply Finite.of_injective f
  intro x y h
  apply Subtype.ext
  apply Prod.ext
  · exact x.property.1.trans y.property.1.symm
  · exact Prod.ext (congrArg (fun z => z.1.val) h)
      (congrArg (fun z : Fin (w j).length × CPos => z.2) h)

theorem relatorCircle_nonempty (hw : w j ≠ []) : Nonempty (RelatorCircle w j) := by
  have hn : 0 < (w j).length := List.length_pos_of_ne_nil hw
  exact ⟨⟨TCirc.pt w j 0 CPos.cor, rfl, hn⟩⟩

end FiniteChains.PresModel
