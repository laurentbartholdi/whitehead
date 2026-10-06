import RequestProject.OrderNerveDictionary
import RequestProject.NerveDegree

/-! Recover actual cellular two- and three-chains from homogeneous increasing nerve chains. -/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb
open FreeAbelianGroup
universe u
variable {P : Type u} [PartialOrder P]

noncomputable def decodeOrdEdgeList : List P → OrdEdge P →₀ ℤ
  | [a, b] => by
    classical
    exact if h : a ≤ b then Finsupp.single ⟨(a, b), h⟩ 1 else 0
  | _ => 0

noncomputable def decodeOrdNerve1 : Nerve.Ch P →+ (OrdEdge P →₀ ℤ) := lift decodeOrdEdgeList

@[simp] theorem decodeOrdNerve1_of (l : List P) :
    decodeOrdNerve1 (of l) = decodeOrdEdgeList l := lift_apply_of _ _

theorem decodeOrdNerve1_encode (c : OrdEdge P →₀ ℤ) :
    decodeOrdNerve1 (ordNerveChain1 c) = c := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, hc, hd]
  | single e n => simp [ordNerveChain1, decodeOrdEdgeList, e.2]

theorem ordNerveChain1_injective : Function.Injective (ordNerveChain1 (P := P)) := by
  intro c d h
  simpa only [decodeOrdNerve1_encode] using congrArg decodeOrdNerve1 h

noncomputable def decodeOrdTriList : List P → OrdTri P →₀ ℤ
  | [a, b, c] => by
    classical
    exact if h : a ≤ b ∧ b ≤ c then Finsupp.single ⟨(a, b, c), h⟩ 1 else 0
  | _ => 0

noncomputable def decodeOrdTetList : List P → OrdTet P →₀ ℤ
  | [a, b, c, d] => by
    classical
    exact if h : a ≤ b ∧ b ≤ c ∧ c ≤ d then Finsupp.single ⟨(a, b, c, d), h⟩ 1 else 0
  | _ => 0

noncomputable def decodeOrdNerve2 : Nerve.Ch P →+ (OrdTri P →₀ ℤ) := lift decodeOrdTriList
noncomputable def decodeOrdNerve3 : Nerve.Ch P →+ (OrdTet P →₀ ℤ) := lift decodeOrdTetList

@[simp] theorem decodeOrdNerve2_of (l : List P) :
    decodeOrdNerve2 (of l) = decodeOrdTriList l := lift_apply_of _ _
@[simp] theorem decodeOrdNerve3_of (l : List P) :
    decodeOrdNerve3 (of l) = decodeOrdTetList l := lift_apply_of _ _

/-- Cellular coordinates are recovered exactly, including every integer coefficient. -/
theorem decodeOrdNerve2_encode (c : OrdTri P →₀ ℤ) :
    decodeOrdNerve2 (ordNerveChain2 c) = c := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, hc, hd]
  | single t n =>
    simp [ordNerveChain2, decodeOrdTriList, t.2.1, t.2.2]

theorem decodeOrdNerve3_encode (c : OrdTet P →₀ ℤ) :
    decodeOrdNerve3 (ordNerveChain3 c) = c := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, hc, hd]
  | single t n =>
    simp [ordNerveChain3, decodeOrdTetList, t.2.1, t.2.2.1, t.2.2.2]

/-- On an increasing basis list, decoding followed by encoding retains its degree-two part. -/
theorem ordNerveChain2_decode_of {l : List P} (hl : List.IsChain (· ≤ ·) l) :
    ordNerveChain2 (decodeOrdTriList l) = Nerve.lengthProjection 3 (of l) := by
  classical
  cases l with
  | nil => simp [decodeOrdTriList]
  | cons a l =>
    cases l with
    | nil => simp [decodeOrdTriList]
    | cons b l =>
      cases l with
      | nil => simp [decodeOrdTriList]
      | cons c l =>
        cases l with
        | nil =>
          have h : a ≤ b ∧ b ≤ c := by simpa [List.isChain_cons] using hl
          simp [decodeOrdTriList, h, ordNerveChain2]
        | cons d l => simp [decodeOrdTriList]

/-- Every increasing homogeneous degree-two nerve chain is an actual cellular two-chain. -/
theorem ordNerveChain2_decode {c : Nerve.Ch P} (hc : c ∈ Nerve.Inc P) :
    ordNerveChain2 (decodeOrdNerve2 c) = Nerve.lengthProjection 3 c := by
  induction hc using AddSubgroup.closure_induction with
  | mem x hx =>
    rcases hx with ⟨l, hl, rfl⟩
    rw [decodeOrdNerve2_of]
    exact ordNerveChain2_decode_of hl
  | zero => simp
  | add x y _ _ hx hy => simp only [map_add, hx, hy]
  | neg x _ hx => simp only [map_neg, hx]

theorem ordNerveChain3_decode_of {l : List P} (hl : List.IsChain (· ≤ ·) l) :
    ordNerveChain3 (decodeOrdTetList l) = Nerve.lengthProjection 4 (of l) := by
  classical
  cases l with
  | nil => simp [decodeOrdTetList]
  | cons a l =>
    cases l with
    | nil => simp [decodeOrdTetList]
    | cons b l =>
      cases l with
      | nil => simp [decodeOrdTetList]
      | cons c l =>
        cases l with
        | nil => simp [decodeOrdTetList]
        | cons d l =>
          cases l with
          | nil =>
            have h : a ≤ b ∧ b ≤ c ∧ c ≤ d := by simpa [List.isChain_cons] using hl
            simp [decodeOrdTetList, h, ordNerveChain3]
          | cons e l => simp [decodeOrdTetList]

theorem ordNerveChain3_decode {c : Nerve.Ch P} (hc : c ∈ Nerve.Inc P) :
    ordNerveChain3 (decodeOrdNerve3 c) = Nerve.lengthProjection 4 c := by
  induction hc using AddSubgroup.closure_induction with
  | mem x hx =>
    rcases hx with ⟨l, hl, rfl⟩
    rw [decodeOrdNerve3_of]
    exact ordNerveChain3_decode_of hl
  | zero => simp
  | add x y _ _ hx hy => simp only [map_add, hx, hy]
  | neg x _ hx => simp only [map_neg, hx]

theorem ordNerveChain2_injective : Function.Injective (ordNerveChain2 (P := P)) := by
  intro c d h
  simpa only [decodeOrdNerve2_encode] using congrArg decodeOrdNerve2 h

/-- Zero nerve boundary is equivalent to the actual zero cellular boundary. -/
theorem ordNerveChain2_cycle_iff (c : OrdTri P →₀ ℤ) :
    Nerve.bdry (ordNerveChain2 c) = 0 ↔ bdry2 (orderCx P) c = 0 := by
  rw [← ordNerveChain1_bdry2]
  exact ⟨fun h => ordNerveChain1_injective (h.trans (map_zero _).symm),
    fun h => by rw [h, map_zero]⟩

theorem ordNerveChain2_lengthProjection (c : OrdTri P →₀ ℤ) :
    Nerve.lengthProjection 3 (ordNerveChain2 c) = ordNerveChain2 c := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, hc, hd]
  | single t n => simp [ordNerveChain2]

theorem ordNerveChain2_mem_inc (c : OrdTri P →₀ ℤ) :
    ordNerveChain2 c ∈ Nerve.Inc P := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simpa only [map_add] using AddSubgroup.add_mem _ hc hd
  | single t n =>
    simp only [ordNerveChain2, Finsupp.linearCombination_single]
    apply AddSubgroup.zsmul_mem
    apply Nerve.of_mem_inc
    simpa [List.isChain_cons] using t.2

/-- Triangles lying in a subposet, with all three vertices required to lie in it. -/
def ordTriOn (A : P → Prop) : Set (OrdTri P) :=
  {t | A t.1.1 ∧ A t.1.2.1 ∧ A t.1.2.2}

theorem decodeOrdTriList_supported {A : P → Prop} {l : List P}
    (hl : List.IsChain (· ≤ ·) l) (hA : ∀ x ∈ l, A x) :
    decodeOrdTriList l ∈ Finsupp.supported ℤ ℤ (ordTriOn A) := by
  classical
  cases l with
  | nil => simp [decodeOrdTriList]
  | cons a l =>
    cases l with
    | nil => simp [decodeOrdTriList]
    | cons b l =>
      cases l with
      | nil => simp [decodeOrdTriList]
      | cons c l =>
        cases l with
        | nil =>
          have h : a ≤ b ∧ b ≤ c := by simpa [List.isChain_cons] using hl
          simp only [decodeOrdTriList, dif_pos h]
          exact Finsupp.single_mem_supported ℤ 1
            ⟨hA a (by simp), hA b (by simp), hA c (by simp)⟩
        | cons d l => simp [decodeOrdTriList]

theorem decodeOrdNerve2_supported {A : P → Prop} {c : Nerve.Ch P}
    (hc : c ∈ Nerve.IncOn A) :
    decodeOrdNerve2 c ∈ Finsupp.supported ℤ ℤ (ordTriOn A) := by
  induction hc using AddSubgroup.closure_induction with
  | mem x hx =>
    rcases hx with ⟨l, hl, rfl⟩
    rw [decodeOrdNerve2_of]
    exact decodeOrdTriList_supported hl.1 hl.2
  | zero => simp
  | add x y _ _ hx hy => simpa only [map_add] using Submodule.add_mem _ hx hy
  | neg x _ hx => simpa only [map_neg] using Submodule.neg_mem _ hx

end FiniteChains.Comb
