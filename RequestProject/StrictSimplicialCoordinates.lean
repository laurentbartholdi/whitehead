import RequestProject.FiniteSetBoundary
import RequestProject.StrictOrderChains

/-! Coordinate simplices and nondegenerate cellular order chains have the same boundary. -/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb
variable {P V : Type} [PartialOrder P] [DecidableEq V] [LinearOrder V]

def strictTriangleCoordinates (f : P → V) (t : StrictOrdTri P) : Finset V :=
  {f t.1.1, f t.1.2.1, f t.1.2.2}

def strictEdgeCoordinates (f : P → V) (e : StrictOrdEdge P) : Finset V :=
  {f e.1.1, f e.1.2}

noncomputable def strictTriangleCoordinateChain (f : P → V) :
    (StrictOrdTri P →₀ ℤ) →ₗ[ℤ] (Finset V →₀ ℤ) :=
  Finsupp.lmapDomain ℤ ℤ (strictTriangleCoordinates f)

noncomputable def strictEdgeCoordinateChain (f : P → V) :
    (StrictOrdEdge P →₀ ℤ) →ₗ[ℤ] (Finset V →₀ ℤ) :=
  Finsupp.lmapDomain ℤ ℤ (strictEdgeCoordinates f)

theorem sort_strictTriangleCoordinates (f : P → V) (hf : StrictMono f) (t : StrictOrdTri P) :
    (strictTriangleCoordinates f t).sort (· ≤ ·) = [f t.1.1, f t.1.2.1, f t.1.2.2] := by
  have hab := hf t.2.1
  have hbc := hf t.2.2
  have hac := hab.trans hbc
  unfold strictTriangleCoordinates
  rw [Finset.sort_insert (r := (· ≤ ·)) (s := {f t.1.2.1, f t.1.2.2}) (a := f t.1.1) (by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact hab.le
    · exact hac.le) (by simp [hab.ne, hac.ne])]
  rw [Finset.sort_insert (r := (· ≤ ·)) (s := {f t.1.2.2}) (a := f t.1.2.1) (by
    intro x hx
    have hx' : x = f t.1.2.2 := Finset.mem_singleton.mp hx
    simpa only [hx'] using hbc.le) (by simp [hbc.ne]), Finset.sort_singleton]

/-- Distinct nondegenerate order cells retain distinct coordinate simplices. -/
theorem strictTriangleCoordinates_injective (f : P → V) (hf : StrictMono f)
    (hfi : Function.Injective f) :
    Function.Injective (strictTriangleCoordinates f) := by
  intro t u he
  have hs := congrArg (fun σ : Finset V => σ.sort (· ≤ ·)) he
  change (strictTriangleCoordinates f t).sort (· ≤ ·) =
    (strictTriangleCoordinates f u).sort (· ≤ ·) at hs
  rw [sort_strictTriangleCoordinates f hf, sort_strictTriangleCoordinates f hf] at hs
  simp only [List.cons.injEq, and_true] at hs
  apply Subtype.ext
  exact Prod.ext (hfi hs.1) (Prod.ext (hfi hs.2.1) (hfi hs.2.2))

theorem strictTriangleCoordinateChain_injective (f : P → V) (hf : StrictMono f)
    (hfi : Function.Injective f) :
    Function.Injective (strictTriangleCoordinateChain f) :=
  Finsupp.mapDomain_injective (strictTriangleCoordinates_injective f hf hfi)

theorem strictTriangleCoordinates_card (f : P → V) (hf : StrictMono f) (t : StrictOrdTri P) :
    (strictTriangleCoordinates f t).card = 3 := by
  have hab := (hf t.2.1).ne
  have hbc := (hf t.2.2).ne
  have hac := (hf (t.2.1.trans t.2.2)).ne
  simp [strictTriangleCoordinates, hab, hbc, hac]

theorem strictTriangleCoordinateChain_eq_zero_of_card (f : P → V) (hf : StrictMono f)
    (c : StrictOrdTri P →₀ ℤ) (σ : Finset V) (hσ : σ.card ≠ 3) :
    strictTriangleCoordinateChain f c σ = 0 := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, Finsupp.add_apply, hc, hd, add_zero]
  | single t n =>
    have hne : strictTriangleCoordinates f t ≠ σ := by
      intro h
      apply hσ
      rw [← h, strictTriangleCoordinates_card f hf]
    simp [strictTriangleCoordinateChain, hne]

omit [LinearOrder V] in
theorem strictTriangleCoordinateChain_eq_zero_of_not_face (f : P → V) (L : ASC V)
    (hL : ∀ t : StrictOrdTri P, strictTriangleCoordinates f t ∈ L.faces)
    (c : StrictOrdTri P →₀ ℤ) (σ : Finset V) (hσ : σ ∉ L.faces) :
    strictTriangleCoordinateChain f c σ = 0 := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, Finsupp.add_apply, hc, hd, add_zero]
  | single t n =>
    have hne : strictTriangleCoordinates f t ≠ σ := fun h => hσ (h ▸ hL t)
    simp [strictTriangleCoordinateChain, hne]

/-- Orientation is fixed by the coordinate order, and agrees with the cellular attaching loop. -/
theorem finiteSetBoundary_strictTriangleCoordinateChain (f : P → V) (hf : StrictMono f)
    (c : StrictOrdTri P →₀ ℤ) :
    finiteSetBoundary (strictTriangleCoordinateChain f c) =
      strictEdgeCoordinateChain f (bdry2 (strictOrderCx P) c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, hc, hd]
  | single t n =>
    have hsingle : strictTriangleCoordinateChain f (Finsupp.single t n) =
        Finsupp.single (strictTriangleCoordinates f t) n := by
      simp [strictTriangleCoordinateChain]
    rw [hsingle]
    rw [show strictTriangleCoordinates f t = {f t.1.1, f t.1.2.1, f t.1.2.2} from rfl,
      finiteSetBoundary_triangle (hf t.2.1) (hf t.2.2)]
    let eab : StrictOrdEdge P := ⟨(t.1.1, t.1.2.1), t.2.1⟩
    let ebc : StrictOrdEdge P := ⟨(t.1.2.1, t.1.2.2), t.2.2⟩
    let eac : StrictOrdEdge P := ⟨(t.1.1, t.1.2.2), t.2.1.trans t.2.2⟩
    have hpath : pathChain ((strictOrderCx P).att t) =
        Finsupp.single eab 1 + (Finsupp.single ebc 1 + -Finsupp.single eac 1) := by
      simp [strictOrderCx, pathChain, eab, ebc, eac]
    rw [@bdry2_single (strictOrderCx P) t n, hpath, map_smul, map_add, map_add, map_neg]
    simp [strictEdgeCoordinateChain, strictEdgeCoordinates, eab, ebc, eac, smul_add]
    abel

variable [Fintype V]

/-- A cellular cycle supplies the coefficient-function cycle required by the cubical argument. -/
theorem simpBdry_strictTriangleCoordinateChain (f : P → V) (hf : StrictMono f)
    (c : StrictOrdTri P →₀ ℤ) (hc : bdry2 (strictOrderCx P) c = 0) :
    simpBdry (fun σ => strictTriangleCoordinateChain f c σ) = 0 := by
  apply (finiteSetBoundary_eq_zero_iff _).mp
  rw [finiteSetBoundary_strictTriangleCoordinateChain f hf, hc, map_zero]

end FiniteChains.Comb
