module

public import RequestProject.PresConeLinkOrderIso

@[expose] public section

namespace FiniteChains.PresModel
open Comb
universe u
variable {α J : Type u} (w : J → List (α × Bool)) (j : J)

theorem tCirc_strict_of_lt_relation {x y : TCirc w} (h : TCirc.lt w x y) : x < y := by
  apply lt_of_le_of_ne (show x ≤ y from Or.inr h)
  intro he
  have hl := TCirc.lt_left_tag w h
  have hr := TCirc.lt_right_tag w h
  rw [he] at hl
  rcases hl with hl | hl <;> rcases hr with hr | hr <;> simp_all

def relatorCirclePoint (k : Fin (w j).length) (s : CPos) : RelatorCircle w j :=
  ⟨TCirc.pt w j k s, rfl, k.isLt⟩

def relatorCircleNext (k : Fin (w j).length) : Fin (w j).length :=
  ⟨TCirc.csucc w j k, Nat.mod_lt _ (by have := k.isLt; omega)⟩

def relatorCircleEdge0 (k : Fin (w j).length) : StrictOrdEdge (RelatorCircle w j) :=
  ⟨(relatorCirclePoint w j k CPos.cor, relatorCirclePoint w j k CPos.cedgL),
    tCirc_strict_of_lt_relation w ⟨rfl, k.isLt, Or.inl ⟨rfl, rfl, rfl⟩⟩⟩

def relatorCircleEdge1 (k : Fin (w j).length) : StrictOrdEdge (RelatorCircle w j) :=
  ⟨(relatorCirclePoint w j k CPos.cmid, relatorCirclePoint w j k CPos.cedgL),
    tCirc_strict_of_lt_relation w ⟨rfl, k.isLt, Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)⟩⟩

def relatorCircleEdge2 (k : Fin (w j).length) : StrictOrdEdge (RelatorCircle w j) :=
  ⟨(relatorCirclePoint w j k CPos.cmid, relatorCirclePoint w j k CPos.cedgR),
    tCirc_strict_of_lt_relation w ⟨rfl, k.isLt, Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))⟩⟩

def relatorCircleEdge3 (k : Fin (w j).length) : StrictOrdEdge (RelatorCircle w j) :=
  ⟨(relatorCirclePoint w j (relatorCircleNext w j k) CPos.cor,
      relatorCirclePoint w j k CPos.cedgR),
    tCirc_strict_of_lt_relation w ⟨rfl, k.isLt, Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩))⟩⟩

def relatorCircleEdgeForget (e : StrictOrdEdge (RelatorCircle w j)) : StrictOrdEdge (TCirc w) :=
  ⟨(e.1.1.1, e.1.2.1), e.2⟩

theorem relatorCircleEdgeForget_injective : Function.Injective (relatorCircleEdgeForget w j) := by
  intro e d h
  apply Subtype.ext
  apply Prod.ext <;> apply Subtype.ext
  · exact congrArg (fun e : StrictOrdEdge (TCirc w) => e.1.1) h
  · exact congrArg (fun e : StrictOrdEdge (TCirc w) => e.1.2) h

/-- The four explicit incidences exhaust the actual valid attaching-circle edges. -/
theorem relatorCircle_edge_cases (e : StrictOrdEdge (RelatorCircle w j)) :
    ∃ k : Fin (w j).length, e = relatorCircleEdge0 w j k ∨
      e = relatorCircleEdge1 w j k ∨ e = relatorCircleEdge2 w j k ∨
      e = relatorCircleEdge3 w j k := by
  let e' := relatorCircleEdgeForget w j e
  obtain ⟨j', k, hk, he⟩ := tCirc_strict_edge_cases w e'
  have hj' : e'.1.2.1 = j' := by
    rcases he with he | he | he | he <;> rw [he] <;> rfl
  have hj : j' = j := hj'.symm.trans e.1.2.2.1
  rw [hj] at hk he
  refine ⟨⟨k, hk⟩, ?_⟩
  rcases he with he | he | he | he
  · left
    apply relatorCircleEdgeForget_injective w j
    exact Subtype.ext he
  · right; left
    apply relatorCircleEdgeForget_injective w j
    exact Subtype.ext he
  · right; right; left
    apply relatorCircleEdgeForget_injective w j
    exact Subtype.ext he
  · right; right; right
    apply relatorCircleEdgeForget_injective w j
    exact Subtype.ext he

def relatorCircleEdgeEnum (p : Fin (w j).length × Fin 4) : StrictOrdEdge (RelatorCircle w j) :=
  if p.2 = 0 then relatorCircleEdge0 w j p.1 else
  if p.2 = 1 then relatorCircleEdge1 w j p.1 else
  if p.2 = 2 then relatorCircleEdge2 w j p.1 else relatorCircleEdge3 w j p.1

theorem relatorCircleEdgeEnum_surjective : Function.Surjective (relatorCircleEdgeEnum w j) := by
  intro e
  obtain ⟨k, he⟩ := relatorCircle_edge_cases w j e
  rcases he with he | he | he | he
  · exact ⟨(k, 0), by simp [relatorCircleEdgeEnum, he]⟩
  · exact ⟨(k, 1), by simp [relatorCircleEdgeEnum, he]⟩
  · exact ⟨(k, 2), by simp [relatorCircleEdgeEnum, he]⟩
  · exact ⟨(k, 3), by simp [relatorCircleEdgeEnum, he]⟩

instance : Finite (StrictOrdEdge (RelatorCircle w j)) :=
  Finite.of_surjective _ (relatorCircleEdgeEnum_surjective w j)

end FiniteChains.PresModel
