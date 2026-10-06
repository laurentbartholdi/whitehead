import RequestProject.GenusBoundaryCoordinates
import RequestProject.SurfaceCocycleExtension

/-! The actual marked loops control all nonabelian surface monodromy. -/
namespace FiniteChains.Davis.Genus
open RACG Mirror Comb Cell
universe v w
variable (q : ℕ) [NeZero q] {G : Type v} [Group G]
  {Ω : Type w} [MulAction G Ω]
  (d : OrdCocycle (SCell (gvc q) (gec q) (gc q)) G) (x₀ : Ω)

def boundaryVertexSection : KVtx q → Ω
  | none => x₀
  | some x => d.val (.vtx (some x)) (.bed (x.1, x.2, false)) •
      ((d.val (.vtx none) (.bed (x.1, x.2, false)))⁻¹ • x₀)

def boundaryEdgeSection (e : IEdg q) : Ω := (d.val (.vtx none) (.bed e))⁻¹ • x₀

theorem boundarySection_none (e : IEdg q) :
    d.val (.vtx none) (.bed e) • boundaryEdgeSection q d x₀ e =
      boundaryVertexSection q d x₀ none :=
  smul_inv_smul _ _

theorem boundarySection_midpoint
    (hm : ∀ x : Fin q × Bool, boundaryMarkValue q d x • x₀ = x₀) (e : IEdg q) :
    d.val (.vtx (some (e.1, e.2.1))) (.bed e) • boundaryEdgeSection q d x₀ e =
      boundaryVertexSection q d x₀ (some (e.1, e.2.1)) := by
  obtain ⟨h, b, t⟩ := e
  cases t with
  | false => rfl
  | true =>
    have he := congrArg (fun z => d.val (.vtx (some (h, b))) (.bed (h, b, false)) •
      ((d.val (.vtx none) (.bed (h, b, false)))⁻¹ • z)) (hm (h, b))
    simpa only [boundaryMarkValue, boundaryVertexSection, boundaryEdgeSection,
      mul_smul, inv_smul_smul, smul_inv_smul] using he

theorem boundarySection_incident
    (hm : ∀ x : Fin q × Bool, boundaryMarkValue q d x • x₀ = x₀)
    (v : KVtx q) (e : IEdg q) (hv : v = none ∨ v = some (e.1, e.2.1)) :
    d.val (.vtx v) (.bed e) • boundaryEdgeSection q d x₀ e = boundaryVertexSection q d x₀ v := by
  rcases hv with rfl | rfl
  · exact boundarySection_none q d x₀ e
  · exact boundarySection_midpoint q d x₀ hm e

theorem boundarySection_compatible
    (hm : ∀ x : Fin q × Bool, boundaryMarkValue q d x • x₀ = x₀) (p : Fin (8 * q)) :
    d.val (cV (gc q) p) (cE (gc q) p) • boundaryEdgeSection q d x₀ (gec q p) =
      boundaryVertexSection q d x₀ (gvc q p) ∧
    d.val (cV (gc q) (p + 1)) (cE (gc q) p) • boundaryEdgeSection q d x₀ (gec q p) =
      boundaryVertexSection q d x₀ (gvc q (p + 1)) :=
  ⟨boundarySection_incident q d x₀ hm _ _ (gvc_endpoint q p),
    boundarySection_incident q d x₀ hm _ _ (gvc_succ_endpoint q p)⟩

variable (c : OrdCocycle (NeSpx (cmpRel (SCell (gvc q) (gec q) (gc q)))) G)

/-- A point fixed by the actual marked loops extends to a flat section on the
actual subdivided surface. This is a statement for every group action. -/
theorem genus_exists_flat_section
    (hm : ∀ x : Fin q × Bool, c.readPath (gSig q (x.1.val, x.2)) • x₀ = x₀) :
    ∃ s : NeSpx (cmpRel (SCell (gvc q) (gec q) (gc q))) → Ω,
      c.IsFlatSection s ∧ s (gBase q) = x₀ := by
  let d := barycentricCocycle c
  have hd : ∀ x : Fin q × Bool, boundaryMarkValue q d x • x₀ = x₀ := by
    intro x
    rw [← read_gSig_boundaryMarkValue q c x]
    exact hm x
  obtain ⟨s, hs, hv, _⟩ := SurfaceSection.exists_flat_section (gc q) d
    (boundaryVertexSection q d x₀) (boundaryEdgeSection q d x₀)
    (boundarySection_compatible q d x₀ hd)
  refine ⟨barycentricSection c s, barycentricSection_flat c s hs, ?_⟩
  rw [gBase, barycentricSection_spx1]
  change s (toS (gvc q) (gec q) (gc q) (.vtx (gvc q (cyc (8 * q) 0)))) = x₀
  rw [gvc_even q (k := 0) rfl]
  exact hv none

/-- Fixing the standard marked loops is sufficient to fix every based surface
loop. No abelianization, quotient coefficient ring, or normal-generation premise. -/
theorem genus_loop_fixed_of_marked_fixed
    (hm : ∀ x : Fin q × Bool, c.readPath (gSig q (x.1.val, x.2)) • x₀ = x₀)
    (p : Loop (sdCx (gc q)) (gBase q)) : c.readPath p.1 • x₀ = x₀ := by
  obtain ⟨s, hs, hb⟩ := genus_exists_flat_section q x₀ c hm
  simpa only [hb] using OrdCocycle.IsFlatSection.readPath c hs p.2

theorem genus_monodromy_fixed_of_marked_fixed
    (hm : ∀ x : Fin q × Bool, c.readPath (gSig q (x.1.val, x.2)) • x₀ = x₀)
    (g : Pi1 (sdCx (gc q)) (gBase q)) : c.monodromy (gBase q) g • x₀ = x₀ := by
  refine Quotient.inductionOn g ?_
  intro p
  exact genus_loop_fixed_of_marked_fixed q x₀ c hm p

end FiniteChains.Davis.Genus
