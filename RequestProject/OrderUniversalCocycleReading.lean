import RequestProject.OrderCxMonodromy
import RequestProject.CombUniversalCover

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb.OrdCocycle
universe u v
variable {P : Type u} [Preorder P] {G : Type v} [Group G]
  (c : OrdCocycle P G) (a : P)

/-- Read an actual universal-cover vertex from its actual path class. -/
def readVertex : UV (orderCx P) a → G :=
  Quotient.lift (fun p : PathFrom (orderCx P) a => c.readPath p.val)
    (fun _ _ h => c.readPath_htpy h)

@[simp] theorem readVertex_mk (p : PathFrom (orderCx P) a) :
    c.readVertex a (UV.mk p) = c.readPath p.val := rfl

@[simp] theorem readVertex_base : c.readVertex a (UV.base (orderCx P) a) = 1 := rfl

/-- The actual vertex reading is equivariant for the actual path-class deck action. -/
theorem readVertex_deck (g : Pi1 (orderCx P) a) (p : UV (orderCx P) a) :
    c.readVertex a (deckV g p) = c.monodromy a g * c.readVertex a p := by
  induction g using Quotient.inductionOn with
  | h g =>
    induction p using Quotient.inductionOn with
    | h p => exact c.readPath_append g.val p.val

/-- Appending an actual oriented edge multiplies the actual vertex reading by its cocycle value. -/
theorem readVertex_extend (e : (orderCx P).E × Bool) (p : UV (orderCx P) a)
    (h : endV p = germSrc (orderCx P).src (orderCx P).tgt e) :
    c.readVertex a (extend e p) = c.readVertex a p * c.readGerm e := by
  induction p using Quotient.inductionOn with
  | h p =>
    change c.readPath (extendP e p).val = c.readPath p.val * c.readGerm e
    rw [extendP_pos h, c.readPath_append]
    simp only [c.readPath_cons, c.readPath_nil, mul_one]

/-- Faithful monodromy makes actual vertex reading injective on each actual endpoint fibre. -/
theorem readVertex_fibre_injective (hc : Function.Injective (c.monodromy a))
    (p q : UV (orderCx P) a) (he : endV p = endV q)
    (hr : c.readVertex a p = c.readVertex a q) : p = q := by
  obtain ⟨g, hg, _⟩ := (isRegular_univProj (X := orderCx P) (x₀ := a)).simply_transitive p q he
  change deckV g p = q at hg
  have hm := c.readVertex_deck a g p
  rw [hg, ← hr] at hm
  have hone : c.monodromy a g = 1 := mul_right_cancel
    (hm.symm.trans (one_mul (c.readVertex a p)).symm)
  have hg1 : g = 1 := hc (hone.trans (map_one (c.monodromy a)).symm)
  rw [hg1, deckV_one] at hg
  exact hg

/-- Surjective monodromy makes vertex reading surjective on every inhabited actual endpoint fibre. -/
theorem readVertex_fibre_surjective (hc : Function.Surjective (c.monodromy a))
    (p : UV (orderCx P) a) (z : G) :
    ∃ q : UV (orderCx P) a, endV q = endV p ∧ c.readVertex a q = z := by
  obtain ⟨g, hg⟩ := hc (z * (c.readVertex a p)⁻¹)
  refine ⟨deckV g p, endV_deckV g p, ?_⟩
  rw [c.readVertex_deck, hg]
  simp [mul_assoc]

/-- Actual endpoint-fibre coordinates obtained from a proved bijective cocycle monodromy. -/
noncomputable def readVertexFibreEquiv (hc : Function.Bijective (c.monodromy a))
    (p : UV (orderCx P) a) : {q : UV (orderCx P) a // endV q = endV p} ≃ G :=
  Equiv.ofBijective (fun q => c.readVertex a q.val) ⟨by
    intro q r h
    apply Subtype.ext
    exact c.readVertex_fibre_injective a hc.1 q.val r.val
      (q.property.trans r.property.symm) h, by
    intro z
    obtain ⟨q, he, hr⟩ := c.readVertex_fibre_surjective a hc.2 p z
    exact ⟨⟨q, he⟩, hr⟩⟩

end FiniteChains.Comb.OrdCocycle
