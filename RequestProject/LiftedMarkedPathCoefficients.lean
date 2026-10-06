import RequestProject.ReceivedTreeMarkedComparison

/-! Exact coefficient recovery from distinct first edges of actual lifted
marking paths. 
-/
open scoped Classical
namespace FiniteChains.Comb
universe u

theorem pathChain_apply_zero_of_edge_absent {E : Type u} (p : List (E × Bool))
    (e : E) (hp : ∀ b ∈ p, b.1 ≠ e) : pathChain p e = 0 := by
  classical
  induction p with
  | nil => simp
  | cons b p ih =>
      have hb : b.1 ≠ e := hp b (List.mem_cons_self ..)
      have ht : ∀ c ∈ p, c.1 ≠ e := fun c hc => hp c (List.mem_cons_of_mem b hc)
      rw [pathChain_cons, Finsupp.add_apply, ih ht]
      cases b.2 <;> simp [hb]

variable {X : Complex2.{u}} {a : X.V}

theorem liftedPathChain_apply_zero_of_edge_absent
    (v : UV X a) {p : List (X.E × Bool)} {b : X.V}
    (hp : IsPath X.src X.tgt p (endV v) b) (e : UE X a)
    (he : ∀ c ∈ p, c.1 ≠ e.1.2) : pathChain (uLiftPath p v) e = 0 := by
  apply pathChain_apply_zero_of_edge_absent
  intro c hc hce
  have hm : (c.1.1.2, c.2) ∈ p := by
    rw [← map_uLiftPath p v b hp]
    exact List.mem_map.mpr ⟨c, hc, rfl⟩
  exact he _ hm (congrArg (fun e : UE X a => e.1.2) hce)

section Markings
variable {I J : Type u} (b : X.V) (edge : I → X.E)
  (tail : I → List (X.E × Bool))
  (hp : ∀ i, IsPath X.src X.tgt ((edge i, true) :: tail i) b b)
  (v : J → UV X a) (hv : ∀ j, endV (v j) = b)

include hp in
theorem markedFirstEdge_src (i : I) : X.src (edge i) = b := (hp i).1.symm

noncomputable def liftedMarkedFirstEdge (j : J) (i : I) : UE X a :=
  ⟨(v j, edge i), (hv j).trans (markedFirstEdge_src b edge tail hp i).symm⟩

theorem liftedMarkedFirstEdge_injective (he : Function.Injective edge)
    (hv' : Function.Injective v) :
    Function.Injective (fun x : J × I => liftedMarkedFirstEdge b edge tail hp v hv x.1 x.2) := by
  intro x y hxy
  exact Prod.ext (hv' (congrArg (fun e : UE X a => e.1.1) hxy))
    (he (congrArg (fun e : UE X a => e.1.2) hxy))

/-- No occurrence later in any marking contributes to the distinguished
lifted first-edge coefficient, regardless of its sheet. -/
theorem liftedMarking_first_coefficient
    (he : Function.Injective edge) (hv' : Function.Injective v)
    (ht : ∀ i k c, c ∈ tail k → c.1 ≠ edge i) (j k : J) (i l : I) :
    pathChain (uLiftPath ((edge l, true) :: tail l) (v k))
      (liftedMarkedFirstEdge b edge tail hp v hv j i) =
        if (k, l) = (j, i) then 1 else 0 := by
  classical
  have hstart : endV (v k) = germSrc X.src X.tgt (edge l, true) :=
    (hv k).trans (markedFirstEdge_src b edge tail hp l).symm
  have hrest : IsPath X.src X.tgt (tail l) (endV (extend (edge l, true) (v k))) b := by
    rw [endV_extend hstart]
    exact (hp l).2
  have hzero := liftedPathChain_apply_zero_of_edge_absent (extend (edge l, true) (v k))
    hrest (liftedMarkedFirstEdge b edge tail hp v hv j i) (ht i l)
  rw [uLiftPath_cons hstart, liftGerm_true, pathChain_cons]
  simp only [↓reduceIte, Finsupp.add_apply, hzero, add_zero]
  have hinj := liftedMarkedFirstEdge_injective b edge tail hp v hv he hv'
  change Finsupp.single (liftedMarkedFirstEdge b edge tail hp v hv k l) (1 : ℤ)
    (liftedMarkedFirstEdge b edge tail hp v hv j i) = _
  have hsame :
      liftedMarkedFirstEdge b edge tail hp v hv k l =
        liftedMarkedFirstEdge b edge tail hp v hv j i ↔ (k, l) = (j, i) :=
    ⟨@hinj (k, l) (j, i),
      fun h => congrArg (fun x : J × I => liftedMarkedFirstEdge b edge tail hp v hv x.1 x.2) h⟩
  simp only [Finsupp.single_apply, hsame]

noncomputable def liftedMarkingChainMap : ((J × I) →₀ ℤ) →ₗ[ℤ] (UE X a →₀ ℤ) :=
  Finsupp.linearCombination ℤ
    (fun x => pathChain (uLiftPath ((edge x.2, true) :: tail x.2) (v x.1)))

/-- This recovers the original finite coefficient function, with no
augmentation or sum over sheets. -/
theorem liftedMarkingChainMap_coefficient
    (he : Function.Injective edge) (hv' : Function.Injective v)
    (ht : ∀ i k c, c ∈ tail k → c.1 ≠ edge i)
    (c : (J × I) →₀ ℤ) (j : J) (i : I) :
    liftedMarkingChainMap edge tail v c (liftedMarkedFirstEdge b edge tail hp v hv j i) =
      c (j, i) := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, Finsupp.add_apply, hc, hd]
  | single x n =>
      rw [liftedMarkingChainMap, Finsupp.linearCombination_single, Finsupp.smul_apply,
        liftedMarking_first_coefficient b edge tail hp v hv he hv' ht]
      by_cases h : x = (j, i) <;> simp [h]

include hp hv in
theorem liftedMarkingChainMap_injective
    (he : Function.Injective edge) (hv' : Function.Injective v)
    (ht : ∀ i k c, c ∈ tail k → c.1 ≠ edge i) :
    Function.Injective (liftedMarkingChainMap edge tail v) := by
  intro c d hcd
  ext x
  have h := congrArg (fun z : UE X a →₀ ℤ =>
    z (liftedMarkedFirstEdge b edge tail hp v hv x.1 x.2)) hcd
  simpa only [liftedMarkingChainMap_coefficient b edge tail hp v hv he hv' ht] using h

end Markings
end FiniteChains.Comb
