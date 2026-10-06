module

public import RequestProject.GenusData

@[expose] public section

/-!
# The cell structure of the polygon with identified boundary, counted

The face poset of `RequestProject/SurfacePoset.lean` is a regular cell decomposition of the
closed surface obtained from an `M`-gon by identifying its sides.  This file counts its cells in
each dimension:

* `FiniteChains.Davis.card_cellsRk_zero`, `card_cellsRk_one`, `card_cellsRk_two` — the number of
  cells of dimension `0`, `1`, `2`;
* `FiniteChains.Davis.genus_euler_characteristic` — for the data of
  `RequestProject/GenusData.lean` the alternating sum is `2 - 2q`: **the surface built there is
  indeed the closed orientable surface of genus `q`.**
-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains
namespace Davis

open Cell Finset

universe u

section Count

variable (κ ι : Type u) [Fintype κ] [Fintype ι] [DecidableEq κ] [DecidableEq ι] (M : ℕ)

/-- The cells of dimension `k` of the polygon with identified boundary. -/
def cellsRk (k : ℕ) : Finset (Cell κ ι M) := Finset.univ.filter (fun x => x.rk = k)

theorem cellsRk_zero :
    cellsRk κ ι M 0 = ((univ.image (vtx : κ → Cell κ ι M))
      ∪ (univ.image (cvx : Fin M → Cell κ ι M))) ∪ {ctr} := by
  ext x
  cases x <;> simp [cellsRk, rk]

/-- **The vertices**: one for each vertex of the identified boundary, one for each position of
the collar, and the centre. -/
theorem card_cellsRk_zero : (cellsRk κ ι M 0).card = Fintype.card κ + M + 1 := by
  rw [cellsRk_zero]
  rw [Finset.card_union_of_disjoint
        (by simp [Finset.disjoint_left]; rintro x (⟨y, rfl⟩ | ⟨y, rfl⟩) <;> simp),
      Finset.card_union_of_disjoint (by simp [Finset.disjoint_left])]
  rw [Finset.card_image_of_injective _ (fun x y h => by cases h; rfl),
      Finset.card_image_of_injective _ (fun x y h => by cases h; rfl)]
  simp

theorem cellsRk_one :
    cellsRk κ ι M 1 = ((((univ.image (bed : ι → Cell κ ι M))
      ∪ (univ.image (ced : Fin M → Cell κ ι M)))
      ∪ (univ.image (dia : Fin M → Cell κ ι M))) ∪ (univ.image (gdi : Fin M → Cell κ ι M)))
      ∪ (univ.image (rad : Fin M → Cell κ ι M)) := by
  ext x
  cases x <;> simp [cellsRk, rk]

/-- **The edges**: the edges of the identified boundary, and four edges for each position of the
collar. -/
theorem card_cellsRk_one : (cellsRk κ ι M 1).card = Fintype.card ι + 4 * M := by
  rw [cellsRk_one]
  rw [Finset.card_union_of_disjoint
        (by
          simp [Finset.disjoint_left]
          rintro x (⟨y, rfl⟩ | ⟨y, rfl⟩ | ⟨y, rfl⟩ | ⟨y, rfl⟩) <;> simp),
      Finset.card_union_of_disjoint
        (by simp [Finset.disjoint_left]; rintro x (⟨y, rfl⟩ | ⟨y, rfl⟩ | ⟨y, rfl⟩) <;> simp),
      Finset.card_union_of_disjoint
        (by simp [Finset.disjoint_left]; rintro x (⟨y, rfl⟩ | ⟨y, rfl⟩) <;> simp),
      Finset.card_union_of_disjoint (by simp [Finset.disjoint_left])]
  rw [Finset.card_image_of_injective _ (fun x y h => by cases h; rfl),
      Finset.card_image_of_injective _ (fun x y h => by cases h; rfl),
      Finset.card_image_of_injective _ (fun x y h => by cases h; rfl),
      Finset.card_image_of_injective _ (fun x y h => by cases h; rfl),
      Finset.card_image_of_injective _ (fun x y h => by cases h; rfl)]
  simp
  ring

theorem cellsRk_two :
    cellsRk κ ι M 2 = ((univ.image (tr1 : Fin M → Cell κ ι M))
      ∪ (univ.image (tr2 : Fin M → Cell κ ι M))) ∪ (univ.image (inn : Fin M → Cell κ ι M)) := by
  ext x
  cases x <;> simp [cellsRk, rk]

/-- **The triangles**: three for each position of the boundary. -/
theorem card_cellsRk_two : (cellsRk κ ι M 2).card = 3 * M := by
  rw [cellsRk_two]
  rw [Finset.card_union_of_disjoint
        (by simp [Finset.disjoint_left]; rintro x (⟨y, rfl⟩ | ⟨y, rfl⟩) <;> simp),
      Finset.card_union_of_disjoint (by simp [Finset.disjoint_left])]
  rw [Finset.card_image_of_injective _ (fun x y h => by cases h; rfl),
      Finset.card_image_of_injective _ (fun x y h => by cases h; rfl),
      Finset.card_image_of_injective _ (fun x y h => by cases h; rfl)]
  simp
  ring

end Count

section Genus

variable (q : ℕ)

theorem card_KVtx : Fintype.card (KVtx q) = 2 * q + 1 := by
  simp [KVtx]
  ring

theorem card_IEdg : Fintype.card (IEdg q) = 4 * q := by
  simp [IEdg]
  ring

/-- **The surface built in `RequestProject/GenusData.lean` is the closed orientable surface of
genus `q`**: its cell decomposition has Euler characteristic `2 - 2q`. -/
theorem genus_euler_characteristic :
    ((cellsRk (KVtx q) (IEdg q) (8 * q) 0).card : ℤ) - (cellsRk (KVtx q) (IEdg q) (8 * q) 1).card
      + (cellsRk (KVtx q) (IEdg q) (8 * q) 2).card = 2 - 2 * q := by
  rw [card_cellsRk_zero, card_cellsRk_one, card_cellsRk_two, card_KVtx, card_IEdg]
  push_cast
  ring

end Genus

end Davis
end FiniteChains
