module

public import RequestProject.ConeModel

@[expose] public section

/-!
# The cone model is not an empty notion

`RequestProject/ConeModel.lean` derives property (B3) from a `FiniteChains.ConeModel`, that
is, from a three-dimensional combinatorial model of `C_q` over the presentation of its spine.
This file checks that the notion is non-vacuous, by exhibiting a model with a genuine
collapse: the presentation `⟨x | x⟩` of the trivial group, a two-cell outside the spine
attached along the empty word, and two three-cells — the cone cell and one three-cell which
the collapse removes across that extra two-cell.  Every hypothesis of
`FiniteChains.ConeModel.isCockcroft` is verified, including the vanishing of the second
homology of the universal cover, and the conclusion is the Cockcroft property of the
presentation.
-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains
namespace ConeModelExample

/-- The single generator. -/
abbrev Gen : Type := Unit

/-- The cells of the block: one. -/
abbrev Blk : Type := Unit

/-- The capping disks: none. -/
abbrev Cap : Type := Empty

/-- The presentation `⟨x | x⟩` of the trivial group, in the shape "block cells together with
capping disks" of property (B3). -/
def Rel : Blk ⊕ Cap → FreeGroup Gen := fun _ => FreeGroup.of ()

/-- The boundaries of the two three-cells: they meet only the two-cell outside the spine, with
opposite incidence numbers, so the model is closed. -/
noncomputable def bdry3 : Bool → ((Blk ⊕ Cap) ⊕ Unit) → MonoidAlgebra ℤ (PresGroup Rel) :=
  fun b => Sum.elim (fun _ => 0) (fun _ => if b then -1 else 1)

@[simp] theorem bdry3_inl (b : Bool) (j : Blk ⊕ Cap) : bdry3 b (Sum.inl j) = 0 := rfl

@[simp] theorem bdry3_inr_false (c : Unit) : bdry3 false (Sum.inr c) = 1 := rfl

@[simp] theorem bdry3_inr_true (c : Unit) : bdry3 true (Sum.inr c) = -1 := rfl

/-- The cone model: one two-cell outside the spine, one collapsing three-cell and the cone
cell. -/
noncomputable def model : ConeModel Rel where
  Coll := Unit
  Three := Bool
  word := fun _ => 1
  word_mem := fun _ => Subgroup.one_mem _
  bdry := bdry3
  cone := true
  steps := [(false, Sum.inr ())]
  isCollapse := by
    refine ⟨?_, ?_, trivial⟩
    · rw [bdry3_inr_false]
      exact isUnit_one
    · intro p hp
      exact absurd hp List.not_mem_nil
  collapsed := by
    intro t ht
    refine ⟨Sum.inr (), ?_⟩
    have : t = false := by cases t <;> simp_all
    rw [this]
    exact List.mem_cons_self
  steps_faces := by
    intro p hp
    rcases List.mem_cons.1 hp with rfl | hp'
    · exact ⟨(), rfl⟩
    · exact absurd hp' List.not_mem_nil
  closed := by
    intro f
    cases f with
    | inl j => simp
    | inr c => simp

theorem foxCoord_rel (j : Blk ⊕ Cap) (i : Gen) :
    foxCoordPres Rel (model.attach (Sum.inl j)) i = 1 := by
  show foxCoordPres Rel (Rel j) i = 1
  rw [foxCoordPres, Rel]
  simp

theorem foxCoord_coll (c : Unit) (i : Gen) :
    foxCoordPres Rel (model.attach (Sum.inr c)) i = 0 := by
  show foxCoordPres Rel 1 i = 0
  rw [foxCoordPres]
  simp

/-- A two-cycle of the model vanishes on the cells of the spine. -/
theorem cycle_inl {x : (Blk ⊕ Cap) ⊕ Unit → MonoidAlgebra ℤ (PresGroup Rel)}
    (hx : model.IsCycle2 x) (j : Blk ⊕ Cap) : x (Sum.inl j) = 0 := by
  have h := hx ()
  rw [ConeModel.bdry2, Fintype.sum_sum_type] at h
  simp only [foxCoord_rel, foxCoord_coll, mul_one, mul_zero, Finset.sum_const_zero,
    add_zero] at h
  have hj : j = Sum.inl () := by
    cases j with
    | inl u => cases u; rfl
    | inr e => exact e.elim
  subst hj
  simpa using h

/-- **The second homology of the universal cover of the model vanishes**: every two-cycle is
the boundary of a three-chain. -/
theorem h2_vanishes (x : (Blk ⊕ Cap) ⊕ Unit → MonoidAlgebra ℤ (PresGroup Rel))
    (hx : model.IsCycle2 x) :
    ∃ (s : Finset Bool) (c : Bool → MonoidAlgebra ℤ (PresGroup Rel)),
      ∀ g, x g = ∑ t ∈ s, c t * bdry3 t g := by
  refine ⟨{false}, fun _ => x (Sum.inr ()), fun g => ?_⟩
  rw [Finset.sum_singleton]
  cases g with
  | inl j => rw [cycle_inl hx j, bdry3_inl, mul_zero]
  | inr c => cases c; rw [bdry3_inr_false, mul_one]

/-- The hypotheses of `FiniteChains.ConeModel.isCockcroft` are satisfiable: the presentation
of this example carries a cone model with vanishing second homology, and is therefore
Cockcroft. -/
theorem isCockcroft_example : IsCockcroft Rel :=
  model.isCockcroft h2_vanishes

end ConeModelExample
end FiniteChains
