import Mathlib

/-!
# Combinatorial two-complexes, their chain complexes and their covers

Theorem A speaks about two-complexes, their fundamental groups, coverings and homology.
None of that is available in the library, so this file builds the part that is genuinely
needed for the implication `(1) ⇒ (2)`: a *combinatorial* two-complex, i.e. a graph
together with two-cells attached along edge loops, its cellular chain complex over `ℤ`,
its homology, combinatorial coverings, deck transformations and regular covers.

The definitions are the standard cellular ones:

* a complex has vertices `V`, oriented edges `E` with endpoints `src`, `tgt` and two-cells
  `F`, each attached along a closed edge path `att f` based at `base f`;
* `∂₁ e = tgt e - src e` and `∂₂ f = ` the signed sum of the edges of `att f`;
* `∂₁ ∘ ∂₂ = 0` because attaching paths are loops (`Comb.bdry1_bdry2`);
* `IsAcyclic X` means `H₂ = H₁ = H̃₀ = 0`, i.e. `∂₂` is injective, `ker ∂₁ = im ∂₂` and
  the image of `∂₁` is the whole augmentation kernel;
* `Hom X Y` is a cellular map, `IsCovering p` says that `p` is a covering: it is onto on
  vertices, a bijection on the edge germs at every vertex, and every two-cell of the base
  lifts uniquely once a lift of its basepoint is chosen;
* `DeckAction X Q` is an action of a group `Q` on `X` by cellular automorphisms and
  `IsRegular p A` says that the action permutes the fibres of `p` simply transitively.

`Comb.HasAcyclicRegularCover Y` is then condition (2) of Theorem A for the complex `Y`:
`Y` admits a connected acyclic regular cover.
-/

namespace FiniteChains
namespace Comb

universe u v

/-! ### Edge paths -/

variable {V E : Type*}

/-- The initial vertex of an oriented edge: `(e, true)` is `e`, `(e, false)` is `e`
reversed. -/
def germSrc (src tgt : E → V) (e : E × Bool) : V := if e.2 then src e.1 else tgt e.1

/-- The terminal vertex of an oriented edge. -/
def germTgt (src tgt : E → V) (e : E × Bool) : V := if e.2 then tgt e.1 else src e.1

@[simp] theorem germSrc_true (src tgt : E → V) (e : E) : germSrc src tgt (e, true) = src e := rfl
@[simp] theorem germSrc_false (src tgt : E → V) (e : E) : germSrc src tgt (e, false) = tgt e := rfl
@[simp] theorem germTgt_true (src tgt : E → V) (e : E) : germTgt src tgt (e, true) = tgt e := rfl
@[simp] theorem germTgt_false (src tgt : E → V) (e : E) : germTgt src tgt (e, false) = src e := rfl

/-- `IsPath src tgt p a b` : the list of oriented edges `p` is an edge path from `a`
to `b`. -/
def IsPath (src tgt : E → V) : List (E × Bool) → V → V → Prop
  | [], a, b => a = b
  | e :: p, a, b => a = germSrc src tgt e ∧ IsPath src tgt p (germTgt src tgt e) b

@[simp] theorem isPath_nil (src tgt : E → V) (a b : V) :
    IsPath src tgt [] a b ↔ a = b := Iff.rfl

@[simp] theorem isPath_cons (src tgt : E → V) (e : E × Bool) (p : List (E × Bool)) (a b : V) :
    IsPath src tgt (e :: p) a b ↔
      a = germSrc src tgt e ∧ IsPath src tgt p (germTgt src tgt e) b := Iff.rfl

theorem IsPath.append {src tgt : E → V} {p q : List (E × Bool)} {a b c : V}
    (hp : IsPath src tgt p a b) (hq : IsPath src tgt q b c) : IsPath src tgt (p ++ q) a c := by
  induction p generalizing a with
  | nil => cases hp; exact hq
  | cons e p ih => exact ⟨hp.1, ih hp.2⟩

/-! ### Combinatorial two-complexes -/

/-- A combinatorial two-complex: a graph `(V, E)` together with two-cells `F`, each
attached along a closed edge path. -/
structure Complex2 : Type (u + 1) where
  /-- Vertices. -/
  V : Type u
  /-- Oriented edges. -/
  E : Type u
  /-- Two-cells. -/
  F : Type u
  /-- Initial vertex of an edge. -/
  src : E → V
  /-- Terminal vertex of an edge. -/
  tgt : E → V
  /-- Basepoint of a two-cell. -/
  base : F → V
  /-- Attaching path of a two-cell. -/
  att : F → List (E × Bool)
  /-- The attaching path is a loop at the basepoint. -/
  att_isLoop : ∀ f, IsPath src tgt (att f) (base f) (base f)

variable (X : Complex2.{u})

/-- The complex is path connected. -/
def IsConnected : Prop := ∀ a b : X.V, ∃ p, IsPath X.src X.tgt p a b

/-! ### The cellular chain complex -/

/-- The one-chain carried by an edge path: the signed sum of its edges. -/
noncomputable def pathChain (p : List (E × Bool)) : E →₀ ℤ :=
  (p.map (fun e => if e.2 then Finsupp.single e.1 (1 : ℤ) else -Finsupp.single e.1 (1 : ℤ))).sum

@[simp] theorem pathChain_nil : pathChain ([] : List (E × Bool)) = 0 := rfl

theorem pathChain_cons (e : E × Bool) (p : List (E × Bool)) :
    pathChain (e :: p) =
      (if e.2 then Finsupp.single e.1 (1 : ℤ) else -Finsupp.single e.1 (1 : ℤ)) +
        pathChain p := by
  simp [pathChain]

/-- The first boundary `∂₁ e = tgt e - src e`. -/
noncomputable def bdry1 : (X.E →₀ ℤ) →ₗ[ℤ] (X.V →₀ ℤ) :=
  Finsupp.linearCombination ℤ (fun e => Finsupp.single (X.tgt e) (1 : ℤ)
    - Finsupp.single (X.src e) (1 : ℤ))

/-- The second boundary: the signed sum of the edges of the attaching path. -/
noncomputable def bdry2 : (X.F →₀ ℤ) →ₗ[ℤ] (X.E →₀ ℤ) :=
  Finsupp.linearCombination ℤ (fun f => pathChain (X.att f))

/-- The augmentation `C₀ → ℤ`. -/
noncomputable def augC : (X.V →₀ ℤ) →ₗ[ℤ] ℤ :=
  Finsupp.linearCombination ℤ (fun _ => (1 : ℤ))

variable {X}

@[simp] theorem bdry1_single (e : X.E) (n : ℤ) :
    bdry1 X (Finsupp.single e n) =
      n • (Finsupp.single (X.tgt e) (1 : ℤ) - Finsupp.single (X.src e) (1 : ℤ)) := by
  simp [bdry1]

@[simp] theorem bdry2_single (f : X.F) (n : ℤ) :
    bdry2 X (Finsupp.single f n) = n • pathChain (X.att f) := by
  simp [bdry2]

@[simp] theorem augC_single (a : X.V) (n : ℤ) : augC X (Finsupp.single a n) = n := by
  simp [augC]

/-- The boundary of the chain of an edge path is the difference of its endpoints. -/
theorem bdry1_pathChain_of_isPath {p : List (X.E × Bool)} {a b : X.V}
    (hp : IsPath X.src X.tgt p a b) :
    bdry1 X (pathChain p) = Finsupp.single b (1 : ℤ) - Finsupp.single a (1 : ℤ) := by
  induction p generalizing a with
  | nil =>
      cases hp
      simp
  | cons e p ih =>
      obtain ⟨ha, hrest⟩ := hp
      have h := ih hrest
      rw [pathChain_cons, map_add, h]
      cases e with
      | mk e b =>
          cases b <;> simp [ha, germSrc, germTgt]

/-- The chain complex condition `∂₁ ∘ ∂₂ = 0`. -/
theorem bdry1_bdry2 (c : X.F →₀ ℤ) : bdry1 X (bdry2 X c) = 0 := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c₁ c₂ h₁ h₂ => rw [map_add, map_add, h₁, h₂, add_zero]
  | single f n =>
      rw [bdry2_single, map_smul, bdry1_pathChain_of_isPath (X.att_isLoop f)]
      simp

/-- Boundaries have augmentation zero. -/
theorem augC_bdry1 (c : X.E →₀ ℤ) : augC X (bdry1 X c) = 0 := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c₁ c₂ h₁ h₂ => rw [map_add, map_add, h₁, h₂, add_zero]
  | single e n => simp

/-- Acyclicity of a combinatorial two-complex: `H₂ = H₁ = H̃₀ = 0`. -/
structure IsAcyclic (X : Complex2.{u}) : Prop where
  /-- `H₂ = ker ∂₂ = 0`. -/
  h2 : Function.Injective (bdry2 X)
  /-- `H₁ = 0`: every cycle is a boundary. -/
  h1 : ∀ c : X.E →₀ ℤ, bdry1 X c = 0 → ∃ u : X.F →₀ ℤ, bdry2 X u = c
  /-- `H̃₀ = 0`: every zero-chain of augmentation `0` is a boundary. -/
  h0 : ∀ c : X.V →₀ ℤ, augC X c = 0 → ∃ u : X.E →₀ ℤ, bdry1 X u = c

/-! ### Cellular maps and coverings -/

/-- A cellular map of combinatorial two-complexes. -/
structure Hom (X Y : Complex2.{u}) where
  /-- Action on vertices. -/
  onV : X.V → Y.V
  /-- Action on edges. -/
  onE : X.E → Y.E
  /-- Action on two-cells. -/
  onF : X.F → Y.F
  src_onE : ∀ e, Y.src (onE e) = onV (X.src e)
  tgt_onE : ∀ e, Y.tgt (onE e) = onV (X.tgt e)
  base_onF : ∀ f, Y.base (onF f) = onV (X.base f)
  att_onF : ∀ f, Y.att (onF f) = (X.att f).map (fun eb => (onE eb.1, eb.2))

variable {X Y : Complex2.{u}}

theorem germSrc_onE (p : Hom X Y) (eb : X.E × Bool) :
    germSrc Y.src Y.tgt (p.onE eb.1, eb.2) = p.onV (germSrc X.src X.tgt eb) := by
  obtain ⟨e, b⟩ := eb
  cases b <;> simp [germSrc, p.src_onE, p.tgt_onE]

/-- The germs of oriented edges at a vertex. -/
def Germ (X : Complex2.{u}) (a : X.V) : Type u :=
  {eb : X.E × Bool // germSrc X.src X.tgt eb = a}

/-- A cellular map sends germs at `a` to germs at the image of `a`. -/
def germMap (p : Hom X Y) (a : X.V) : Germ X a → Germ Y (p.onV a) :=
  fun eb => ⟨(p.onE eb.1.1, eb.1.2), by rw [germSrc_onE p eb.1, eb.2]⟩

/-- The two-cells of `X` mapped to a two-cell of `Y` together with a lift of its
basepoint. -/
def cellMap (p : Hom X Y) : X.F → {gv : Y.F × X.V // Y.base gv.1 = p.onV gv.2} :=
  fun f => ⟨(p.onF f, X.base f), p.base_onF f⟩

/-- A combinatorial covering map: onto on vertices, a bijection on germs at each vertex,
and unique lifting of two-cells once a lift of the basepoint is chosen. -/
structure IsCovering (p : Hom X Y) : Prop where
  surjV : Function.Surjective p.onV
  germ : ∀ a : X.V, Function.Bijective (germMap p a)
  cell : Function.Bijective (cellMap p)

/-- An action of a group `Q` on a combinatorial two-complex by cellular automorphisms. -/
structure DeckAction (X : Complex2.{u}) (Q : Type v) [Group Q] where
  /-- Action on vertices. -/
  smulV : Q → X.V → X.V
  /-- Action on edges. -/
  smulE : Q → X.E → X.E
  /-- Action on two-cells. -/
  smulF : Q → X.F → X.F
  one_smulV : ∀ a, smulV 1 a = a
  mul_smulV : ∀ q q' a, smulV (q * q') a = smulV q (smulV q' a)
  one_smulE : ∀ e, smulE 1 e = e
  mul_smulE : ∀ q q' e, smulE (q * q') e = smulE q (smulE q' e)
  one_smulF : ∀ f, smulF 1 f = f
  mul_smulF : ∀ q q' f, smulF (q * q') f = smulF q (smulF q' f)
  src_smul : ∀ q e, X.src (smulE q e) = smulV q (X.src e)
  tgt_smul : ∀ q e, X.tgt (smulE q e) = smulV q (X.tgt e)
  base_smul : ∀ q f, X.base (smulF q f) = smulV q (X.base f)
  att_smul : ∀ q f, X.att (smulF q f) = (X.att f).map (fun eb => (smulE q eb.1, eb.2))

/-- The covering `p` is regular with deck group `Q`: the action preserves the fibres of
`p` and is simply transitive on each of them. -/
structure IsRegular (p : Hom X Y) {Q : Type v} [Group Q] (A : DeckAction X Q) : Prop where
  compat : ∀ q a, p.onV (A.smulV q a) = p.onV a
  simply_transitive : ∀ a b : X.V, p.onV a = p.onV b → ∃! q : Q, A.smulV q a = b

/-- **Condition (2) of Theorem A** for a combinatorial two-complex: `Y` has a connected
acyclic regular cover. -/
def HasAcyclicRegularCover (Y : Complex2.{u}) : Prop :=
  ∃ (X : Complex2.{u}) (Q : Type u) (_ : Group Q) (p : Hom X Y) (A : DeckAction X Q),
    IsCovering p ∧ IsRegular p A ∧ IsConnected X ∧ IsAcyclic X

end Comb
end FiniteChains
