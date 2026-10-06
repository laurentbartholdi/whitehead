module

public import RequestProject.OrderPosetCoverThree
public import RequestProject.SimplyConnectedCoverEquiv

@[expose] public section

/-! The actual lifted three-simplices of the path-class universal cover of an order nerve. -/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb
universe u
variable {P Q : Type u} [PartialOrder P] [PartialOrder Q]

/-- A lifted three-simplex is a simplex and a path class at its first vertex. -/
def UOrdTet (P : Type u) [PartialOrder P] (a : P) :=
  {vt : UV (orderCx P) a × OrdTet P // endV vt.1 = vt.2.1.1}

variable {a : P}

/-- The lifted first face starts at the next vertex of the simplex. -/
noncomputable def uOrdTetFace0 (t : UOrdTet P a) : UF (orderCx P) a :=
  ⟨(extend (ordPos t.1.2.2.1) t.1.1,
    ⟨(t.1.2.1.2.1, t.1.2.1.2.2.1, t.1.2.1.2.2.2), t.1.2.2.2⟩),
    endV_extend (eb := ordPos t.1.2.2.1) t.2⟩

def uOrdTetFace1 (t : UOrdTet P a) : UF (orderCx P) a :=
  ⟨(t.1.1, ⟨(t.1.2.1.1, t.1.2.1.2.2.1, t.1.2.1.2.2.2),
    t.1.2.2.1.trans t.1.2.2.2.1, t.1.2.2.2.2⟩), t.2⟩

def uOrdTetFace2 (t : UOrdTet P a) : UF (orderCx P) a :=
  ⟨(t.1.1, ⟨(t.1.2.1.1, t.1.2.1.2.1, t.1.2.1.2.2.2),
    t.1.2.2.1, t.1.2.2.2.1.trans t.1.2.2.2.2⟩), t.2⟩

def uOrdTetFace3 (t : UOrdTet P a) : UF (orderCx P) a :=
  ⟨(t.1.1, ⟨(t.1.2.1.1, t.1.2.1.2.1, t.1.2.1.2.2.1),
    t.1.2.2.1, t.1.2.2.2.1⟩), t.2⟩

noncomputable def uOrdTetBoundary (t : UOrdTet P a) : UF (orderCx P) a →₀ ℤ :=
  Finsupp.single (uOrdTetFace0 t) 1 - Finsupp.single (uOrdTetFace1 t) 1 +
    Finsupp.single (uOrdTetFace2 t) 1 - Finsupp.single (uOrdTetFace3 t) 1

noncomputable def uOrdBoundary3 : (UOrdTet P a →₀ ℤ) →ₗ[ℤ] (UF (orderCx P) a →₀ ℤ) :=
  Finsupp.linearCombination ℤ uOrdTetBoundary

variable {f : P → Q} (hf : IsPosetCover f) (d₀ : P)

/-- The three-cell lift into a simply connected poset covering, extending the canonical
 path-class covering map on vertices and faces. -/
noncomputable def coveredOrdTet (t : UOrdTet Q (f d₀)) : OrdTet P :=
  Classical.choose (hf.existsUnique_tetLift t.1.2
    (@coverV (orderCx P) (orderCx Q) (orderCxMap f hf.mono)
      (f d₀) d₀ (isCovering_orderCxMap hf) rfl t.1.1)
    (by
      have h := @onV_coverV (orderCx P) (orderCx Q) (orderCxMap f hf.mono)
        (f d₀) d₀ (isCovering_orderCxMap hf) rfl t.1.1
      exact h.trans t.2))

theorem coveredOrdTet_spec (t : UOrdTet Q (f d₀)) :
    (coveredOrdTet hf d₀ t).1.1 =
      @coverV (orderCx P) (orderCx Q) (orderCxMap f hf.mono)
        (f d₀) d₀ (isCovering_orderCxMap hf) rfl t.1.1 ∧
    ordTetMap f hf.mono (coveredOrdTet hf d₀ t) = t.1.2 := by
  unfold coveredOrdTet
  exact (Classical.choose_spec (hf.existsUnique_tetLift t.1.2
    (@coverV (orderCx P) (orderCx Q) (orderCxMap f hf.mono)
      (f d₀) d₀ (isCovering_orderCxMap hf) rfl t.1.1)
    (by exact (@onV_coverV (orderCx P) (orderCx Q) (orderCxMap f hf.mono)
      (f d₀) d₀ (isCovering_orderCxMap hf) rfl t.1.1).trans t.2))).1

theorem coveredOrdTet_injective (hsc : SimplyConnected (orderCx P)) :
    Function.Injective (coveredOrdTet hf d₀) := by
  intro t s h
  apply Subtype.ext
  apply Prod.ext
  · apply coverV_injective (isCovering_orderCxMap hf) hsc
    rw [← (coveredOrdTet_spec hf d₀ t).1, ← (coveredOrdTet_spec hf d₀ s).1, h]
  · rw [← (coveredOrdTet_spec hf d₀ t).2, ← (coveredOrdTet_spec hf d₀ s).2, h]

theorem coveredOrdTet_surjective (hconn : IsConnected (orderCx P)) :
    Function.Surjective (coveredOrdTet hf d₀) := by
  intro t
  obtain ⟨v, hv⟩ := coverV_surjective (d₀ := d₀) (isCovering_orderCxMap hf) hconn t.1.1
  have he : endV v = f t.1.1 := by
    rw [← onV_coverV (isCovering_orderCxMap hf) (d₀ := d₀) (x₀ := f d₀) rfl v, hv]
    rfl
  let s : UOrdTet Q (f d₀) := ⟨(v, ordTetMap f hf.mono t), he⟩
  refine ⟨s, ?_⟩
  obtain ⟨w, -, hw⟩ := hf.existsUnique_tetLift (ordTetMap f hf.mono t) t.1.1 rfl
  exact (hw _ ⟨(coveredOrdTet_spec hf d₀ s).1.trans hv,
      (coveredOrdTet_spec hf d₀ s).2⟩).trans (hw t ⟨rfl, rfl⟩).symm

/-- The four actual two-faces of a weak three-simplex. -/
def ordTetFace0 (t : OrdTet P) : OrdTri P :=
  ⟨(t.1.2.1, t.1.2.2.1, t.1.2.2.2), t.2.2⟩
def ordTetFace1 (t : OrdTet P) : OrdTri P :=
  ⟨(t.1.1, t.1.2.2.1, t.1.2.2.2), t.2.1.trans t.2.2.1, t.2.2.2⟩
def ordTetFace2 (t : OrdTet P) : OrdTri P :=
  ⟨(t.1.1, t.1.2.1, t.1.2.2.2), t.2.1, t.2.2.1.trans t.2.2.2⟩
def ordTetFace3 (t : OrdTet P) : OrdTri P :=
  ⟨(t.1.1, t.1.2.1, t.1.2.2.1), t.2.1, t.2.2.1⟩

theorem coverF_uOrdTetFace1 (t : UOrdTet Q (f d₀)) :
    coverF (isCovering_orderCxMap hf) (d₀ := d₀) (x₀ := f d₀) rfl (uOrdTetFace1 t) =
      ordTetFace1 (coveredOrdTet hf d₀ t) := by
  apply coverF_eq_of_base_and_image (isCovering_orderCxMap hf)
  · change (orderCxMap f hf.mono).onF (ordTetFace1 (coveredOrdTet hf d₀ t)) =
      ordTetFace1 t.1.2
    rw [← (coveredOrdTet_spec hf d₀ t).2]
    rfl
  · exact (coveredOrdTet_spec hf d₀ t).1

theorem coverF_uOrdTetFace2 (t : UOrdTet Q (f d₀)) :
    coverF (isCovering_orderCxMap hf) (d₀ := d₀) (x₀ := f d₀) rfl (uOrdTetFace2 t) =
      ordTetFace2 (coveredOrdTet hf d₀ t) := by
  apply coverF_eq_of_base_and_image (isCovering_orderCxMap hf)
  · change (orderCxMap f hf.mono).onF (ordTetFace2 (coveredOrdTet hf d₀ t)) =
      ordTetFace2 t.1.2
    rw [← (coveredOrdTet_spec hf d₀ t).2]
    rfl
  · exact (coveredOrdTet_spec hf d₀ t).1

theorem coverF_uOrdTetFace3 (t : UOrdTet Q (f d₀)) :
    coverF (isCovering_orderCxMap hf) (d₀ := d₀) (x₀ := f d₀) rfl (uOrdTetFace3 t) =
      ordTetFace3 (coveredOrdTet hf d₀ t) := by
  apply coverF_eq_of_base_and_image (isCovering_orderCxMap hf)
  · change (orderCxMap f hf.mono).onF (ordTetFace3 (coveredOrdTet hf d₀ t)) =
      ordTetFace3 t.1.2
    rw [← (coveredOrdTet_spec hf d₀ t).2]
    rfl
  · exact (coveredOrdTet_spec hf d₀ t).1

theorem coverF_uOrdTetFace0 (t : UOrdTet Q (f d₀)) :
    coverF (isCovering_orderCxMap hf) (d₀ := d₀) (x₀ := f d₀) rfl (uOrdTetFace0 t) =
      ordTetFace0 (coveredOrdTet hf d₀ t) := by
  apply coverF_eq_of_base_and_image (isCovering_orderCxMap hf)
  · change (orderCxMap f hf.mono).onF (ordTetFace0 (coveredOrdTet hf d₀ t)) =
      ordTetFace0 t.1.2
    rw [← (coveredOrdTet_spec hf d₀ t).2]
    rfl
  · have hm := coverV_extend (isCovering_orderCxMap hf) (d₀ := d₀) (x₀ := f d₀) rfl
      (c := t.1.1) (eb := ordPos t.1.2.2.1) t.2
      (x := ordPos (coveredOrdTet hf d₀ t).2.1)
      (by exact (coveredOrdTet_spec hf d₀ t).1) (by
        rw [← (coveredOrdTet_spec hf d₀ t).2]
        rfl)
    exact hm.symm

/-- The canonical cover map carries the full lifted three-boundary to the actual
 three-boundary upstairs, face by face. -/
theorem coverF_uOrdTetBoundary (t : UOrdTet Q (f d₀)) :
    Finsupp.mapDomain (coverF (isCovering_orderCxMap hf) (d₀ := d₀) (x₀ := f d₀) rfl)
      (uOrdTetBoundary t) = ordTetBoundary (coveredOrdTet hf d₀ t) := by
  have hsub (x y : UF (orderCx Q) (f d₀) →₀ ℤ) :
      Finsupp.mapDomain (coverF (isCovering_orderCxMap hf) (d₀ := d₀) (x₀ := f d₀) rfl) (x - y) =
        Finsupp.mapDomain (coverF (isCovering_orderCxMap hf) (d₀ := d₀) (x₀ := f d₀) rfl) x -
          Finsupp.mapDomain (coverF (isCovering_orderCxMap hf) (d₀ := d₀) (x₀ := f d₀) rfl) y :=
    (Finsupp.lmapDomain ℤ ℤ (coverF (isCovering_orderCxMap hf) (d₀ := d₀) (x₀ := f d₀) rfl)).map_sub x y
  simp only [uOrdTetBoundary, hsub, Finsupp.mapDomain_add, Finsupp.mapDomain_single,
    coverF_uOrdTetFace0 hf d₀ t, coverF_uOrdTetFace1 hf d₀ t,
    coverF_uOrdTetFace2 hf d₀ t, coverF_uOrdTetFace3 hf d₀ t]
  rfl

/-- The canonical covering comparison is a chain map also in degree three. -/
theorem coverHom_uOrdBoundary3 (c : UOrdTet Q (f d₀) →₀ ℤ) :
    chain2 (coverHom (isCovering_orderCxMap hf) (d₀ := d₀) (x₀ := f d₀) rfl)
      (uOrdBoundary3 c) =
    ordBoundary3 (Finsupp.mapDomain (coveredOrdTet hf d₀) c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, Finsupp.mapDomain_add, hc, hd]
  | single t n =>
    change Finsupp.mapDomain
      (coverF (isCovering_orderCxMap hf) (d₀ := d₀) (x₀ := f d₀) rfl)
      (uOrdBoundary3 (Finsupp.single t n)) = _
    simp only [uOrdBoundary3, Finsupp.linearCombination_single, Finsupp.mapDomain_smul,
      coverF_uOrdTetBoundary hf d₀ t, Finsupp.mapDomain_single, ordBoundary3]

include hf in
/-- Actual full-nerve degree-two exactness transports to the path-class universal cover
 through the constructed covering comparison. -/
theorem exists_uOrdBoundary3_of_cover_exact (hconn : IsConnected (orderCx P))
    (hsc : SimplyConnected (orderCx P))
    (hfill : ∀ z : OrdTri P →₀ ℤ, bdry2 (orderCx P) z = 0 →
      ∃ y : OrdTet P →₀ ℤ, ordBoundary3 y = z)
    (z : UF (orderCx Q) (f d₀) →₀ ℤ)
    (hz : bdry2 (uCover (orderCx Q) (f d₀)) z = 0) :
    ∃ y : UOrdTet Q (f d₀) →₀ ℤ, uOrdBoundary3 y = z := by
  let p := coverHom (isCovering_orderCxMap hf) (d₀ := d₀) (x₀ := f d₀) rfl
  have hz' : bdry2 (orderCx P) (chain2 p z) = 0 := by
    rw [bdry2_chain2, hz, map_zero]
  obtain ⟨w, hw⟩ := hfill (chain2 p z) hz'
  obtain ⟨y, hy⟩ := Finsupp.mapDomain_surjective (coveredOrdTet_surjective hf d₀ hconn) w
  refine ⟨y, ?_⟩
  apply Finsupp.mapDomain_injective
    (coverF_injective (d₀ := d₀) (isCovering_orderCxMap hf) hsc)
  change chain2 p (uOrdBoundary3 y) = chain2 p z
  rw [coverHom_uOrdBoundary3 hf d₀ y, hy, hw]

include hf in
/-- The lifted three-boundary has zero cellular two-boundary. -/
theorem bdry2_uOrdBoundary3_of_scCover (hsc : SimplyConnected (orderCx P))
    (c : UOrdTet Q (f d₀) →₀ ℤ) :
    bdry2 (uCover (orderCx Q) (f d₀)) (uOrdBoundary3 c) = 0 := by
  let p := coverHom (isCovering_orderCxMap hf) (d₀ := d₀) (x₀ := f d₀) rfl
  have hinj : Function.Injective (chain1 p) := by
    apply Finsupp.mapDomain_injective
    exact @coverE_injective (orderCx P) (orderCx Q) (orderCxMap f hf.mono)
      d₀ (isCovering_orderCxMap hf) hsc
  apply hinj
  rw [map_zero, ← bdry2_chain2 p, coverHom_uOrdBoundary3 hf d₀ c,
    bdry2_ordBoundary3]

end FiniteChains.Comb
