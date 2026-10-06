module

public import RequestProject.StrictChamberInjection
public import RequestProject.OrderNerveEmbeddingCells
public import RequestProject.ChamberQuotientFunctor
public import RequestProject.ChamberQuotientFinite
public import RequestProject.OrderNerveRealizationFinite

@[expose] public section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Davis
open RACG Mirror Comb CategoryTheory Topology
variable {V : Type} [DecidableEq V] {A : CommRel V}
variable {X : Type} [PartialOrder X] (att : NeSpx A →o X)

/-- The original base is embedded as an induced subposet of the chamber quotient. -/
def qNewOrderEmbedding : X ↪o Qpos A X att where
  toFun := qNew
  inj' := Sum.inr_injective
  map_rel_iff' := Iff.rfl

/-- The original realized base is a genuine CW subcomplex of the chamber space. -/
noncomputable def qNewRealizationHomeomorph :
    orderNerveRealization X ≃ₜ
      (orderNerveRealizationSubcomplex (Qpos A X att) (Set.range (qNew (att := att))) :
        Set (orderNerveRealization (Qpos A X att))) :=
  orderNerveRealizationEmbeddingHomeomorph (qNewOrderEmbedding att)

theorem qNewRealizationHomeomorph_openCell (n : ℕ) (s : (nerve X).nonDegenerate n) :
    (fun x => (qNewRealizationHomeomorph att x).val) ''
        CWComplex.openCell (C := (Set.univ : Set (orderNerveRealization X))) n s =
      CWComplex.openCell (C := (Set.univ : Set (orderNerveRealization (Qpos A X att)))) n
        (orderNerveEmbeddingCellEquiv (qNewOrderEmbedding att) n s).val :=
  orderNerveRealizationEmbeddingHomeomorph_openCell (qNewOrderEmbedding att) n s

omit [DecidableEq V] in
/-- Every Coxeter generator supplies an actual old vertex outside the original base. -/
theorem exists_qpos_outside_base (v : V) :
    ∃ p : Qpos A X att, p ∉ Set.range (qNew (att := att)) := by
  let c : QCube A := ⟨{v}, 0, isSimplex_singleton v, fun _ _ => rfl⟩
  have hc : ¬ (c.spx = ∅ ∧ c.sgn = 0) := by
    intro h
    have hn : v ∈ c.spx := Finset.mem_singleton_self v
    rw [h.1] at hn
    exact Finset.notMem_empty v hn
  refine ⟨qOld c hc, ?_⟩
  rintro ⟨x, hx⟩
  change (Sum.inr x : QOld A ⊕ X) = Sum.inl ⟨c, hc⟩ at hx
  cases hx

/-- The actual base carrier is a proper subcomplex when a generator is present. -/
theorem qNewRealizationSubcomplex_ne_univ (v : V) :
    (orderNerveRealizationSubcomplex (Qpos A X att) (Set.range (qNew (att := att))) :
      Set (orderNerveRealization (Qpos A X att))) ≠ Set.univ := by
  obtain ⟨p, hp⟩ := exists_qpos_outside_base att v
  intro h
  have hm : orderNerveRealizationVertex p ∈
      (orderNerveRealizationSubcomplex (Qpos A X att) (Set.range (qNew (att := att))) :
        Set (orderNerveRealization (Qpos A X att))) := by
    rw [h]
    exact Set.mem_univ _
  exact hp ((orderNerveRealizationVertex_mem_subcomplex _ p).mp hm)

instance qpos_finite [Finite V] [Finite X] : Finite (Qpos A X att) :=
  inferInstanceAs (Finite (QOld A ⊕ X))

/-- Finiteness here is for the actual CW cells of the chamber realization;
it does not assert the missing two-dimensional bound. -/
theorem qposRealization_cells_finite [Finite V] [Finite X] :
    Finite (Σ n, RelCWComplex.cell
      (Set.univ : Set (orderNerveRealization (Qpos A X att))) n) :=
  orderNerveRealization_cells_finite (Qpos A X att)

end FiniteChains.Davis
