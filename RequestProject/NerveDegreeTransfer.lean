module

public import RequestProject.NerveDegreeGluing

@[expose] public section

/-! Homogeneous positive-degree fillings transfer from an actual induced subposet. -/
namespace FiniteChains.Nerve
universe u
variable {P Q : Type u}

theorem lengthProjection_cmap (f : P → Q) (n : ℕ) (c : Ch P) :
    lengthProjection n (cmap f c) = cmap f (lengthProjection n c) := by
  classical
  refine ext_apply
    (F := (lengthProjection n).comp (cmap f))
    (G := (cmap f).comp (lengthProjection n)) ?_ c
  intro l
  simp only [AddMonoidHom.coe_comp, Function.comp_apply, cmap_of, lengthProjection_of,
    List.length_map]
  split_ifs <;> simp

variable [Preorder P]

theorem fillsDegreeIn_of_subtype {A : P → Prop} {n : ℕ} (hne : ∃ p, A p)
    (hfill : ∀ c ∈ Inc {p : P // A p}, lengthProjection n c = c → bdry c = 0 →
      ∃ y ∈ Inc {p : P // A p}, bdry y = c) : FillsDegreeIn A n := by
  intro c hc hd hcyc
  obtain ⟨c', hc', he⟩ := exists_preimage_of_mem_incOn A hc
  have hd' : lengthProjection n c' = c' := by
    apply cmap_val_injective A hne
    rw [← lengthProjection_cmap, he, hd]
  have hcyc' : bdry c' = 0 := by
    apply cmap_val_injective A hne
    rw [cmap_bdry, he, hcyc, map_zero]
  obtain ⟨y, hy, hdy⟩ := hfill c' hc' hd' hcyc'
  exact ⟨cmap Subtype.val y, cmap_val_mem_incOn A hy, by rw [← cmap_bdry, hdy, he]⟩

theorem fillsDegreeIn_congr {A B : P → Prop} {n : ℕ}
    (he : ∀ p, A p ↔ B p) (h : FillsDegreeIn A n) : FillsDegreeIn B n := by
  rw [show B = A from funext fun p => propext (he p).symm]
  exact h

theorem generatesDegreeIn_congr {A B Base : P → Prop} {n : ℕ}
    (he : ∀ p, A p ↔ B p) (h : GeneratesDegreeIn A Base n) :
    GeneratesDegreeIn B Base n := by
  rw [show B = A from funext fun p => propext (he p).symm]
  exact h

end FiniteChains.Nerve
