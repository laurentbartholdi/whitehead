import RequestProject.OrderCxMonodromy

/-!
# Two monotone maps in the relation `f ≤ g` induce homotopic maps of order complexes

If `f, g : P → Q` are monotone and `f x ≤ g x` for every `x` — a natural transformation between
the two functors — then the maps they induce on the order complexes are homotopic, the homotopy
being the family of edges `f x → g x`.  Combinatorially:

    (image of `p` under `f`) · [f v, g v]  ≃  [f u, g u] · (image of `p` under `g`)

for every edge path `p` from `u` to `v` (`FiniteChains.Comb.htpy_mapPath_le`).

This is the only homotopy-theoretic input needed to compare the two ends of a mapping cylinder
of posets: for the cylinder `CylP a` the two maps are the inclusion of the outer end and the
inclusion of its image in the base, and the natural transformation is the defining relation
`s ≤ a s` of the cylinder.  The conjugation form
`FiniteChains.Comb.htpy_loop_mapPath_le` is what the filling of a relator uses.
-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains
namespace Comb

universe u

variable {P Q : Type u} [Preorder P] [Preorder Q]

/-- The image of a comparability under a monotone map, as an edge of the order complex. -/
theorem mapPath_ordPos {f : P → Q} (hf : Monotone f) {a b : P} (h : a ≤ b) :
    mapPath (orderCxMap f hf) [ordPos h] = [ordPos (hf h)] := rfl

theorem mapPath_ordNeg {f : P → Q} (hf : Monotone f) {a b : P} (h : a ≤ b) :
    mapPath (orderCxMap f hf) [ordNeg h] = [ordNeg (hf h)] := rfl

/-- **The naturality homotopy for a single edge, traversed forwards.** -/
theorem htpy_square_pos {f g : P → Q} (hf : Monotone f) (hg : Monotone g)
    (hfg : ∀ x, f x ≤ g x) {a b : P} (h : a ≤ b) :
    Htpy (orderCx Q) (f a) (g b) [ordPos (hf h), ordPos (hfg b)]
      [ordPos (hfg a), ordPos (hg h)] :=
  (htpy_orderCx_tri (hf h) (hfg b)).trans (htpy_orderCx_tri (hfg a) (hg h)).symm

/-- **The naturality homotopy for a single edge, traversed backwards.** -/
theorem htpy_square_neg {f g : P → Q} (hf : Monotone f) (hg : Monotone g)
    (hfg : ∀ x, f x ≤ g x) {a b : P} (h : a ≤ b) :
    Htpy (orderCx Q) (f b) (g a) [ordNeg (hf h), ordPos (hfg a)]
      [ordPos (hfg b), ordNeg (hg h)] := by
  -- multiply the forward square by the inverse edges on both sides
  have hpos := htpy_square_pos hf hg hfg h
  -- `[f b, f a]⁻¹ · ([f a, f b] [f b, g b]) · [g a, g b]⁻¹ ≃ [f b, g b] ... `
  have h1 : Htpy (orderCx Q) (f b) (g a)
      ([ordNeg (hf h)] ++ [ordPos (hf h), ordPos (hfg b)] ++ [ordNeg (hg h)])
      ([ordNeg (hf h)] ++ [ordPos (hfg a), ordPos (hg h)] ++ [ordNeg (hg h)]) :=
    hpos.congr_append (isPath_ordNeg (hf h)) (isPath_ordNeg (hg h))
  have h2 : Htpy (orderCx Q) (f b) (g a)
      ([] ++ [ordNeg (hf h), ordPos (hf h)] ++ [ordPos (hfg b), ordNeg (hg h)])
      ([] ++ [] ++ [ordPos (hfg b), ordNeg (hg h)]) :=
    (htpy_ordNeg_ordPos (hf h)).congr_append (isPath_nil' (f b))
      (show IsPath (orderCx Q).src (orderCx Q).tgt [ordPos (hfg b), ordNeg (hg h)] (f b) (g a)
        from ⟨rfl, rfl, rfl⟩)
  have h3 : Htpy (orderCx Q) (f b) (g a)
      ([ordNeg (hf h), ordPos (hfg a)] ++ [ordPos (hg h), ordNeg (hg h)] ++ [])
      ([ordNeg (hf h), ordPos (hfg a)] ++ [] ++ []) :=
    (htpy_ordPos_ordNeg (hg h)).congr_append
      (show IsPath (orderCx Q).src (orderCx Q).tgt [ordNeg (hf h), ordPos (hfg a)] (f b) (g a)
        from ⟨rfl, rfl, rfl⟩) (isPath_nil' (g a))
  simp only [List.nil_append, List.cons_append, List.append_nil] at h1 h2 h3 ⊢
  exact (h3.symm.trans h1.symm).trans h2

/-- **The naturality homotopy.**  For two monotone maps with `f ≤ g` pointwise, the image of a
path under `f` followed by the edge at its end is homotopic to the edge at its start followed by
the image under `g`. -/
theorem htpy_mapPath_le {f g : P → Q} (hf : Monotone f) (hg : Monotone g)
    (hfg : ∀ x, f x ≤ g x) :
    ∀ (p : List ((orderCx P).E × Bool)) {u v : P},
      IsPath (orderCx P).src (orderCx P).tgt p u v →
      Htpy (orderCx Q) (f u) (g v)
        (mapPath (orderCxMap f hf) p ++ [ordPos (hfg v)])
        ([ordPos (hfg u)] ++ mapPath (orderCxMap g hg) p) := by
  intro p
  induction p with
  | nil =>
      intro u v hp
      cases hp
      exact Htpy.refl _
  | cons eb p ih =>
      rintro u v ⟨hu, hrest⟩
      obtain ⟨⟨⟨a, b⟩, hab⟩, tag⟩ := eb
      cases tag with
      | true =>
          have hua : u = a := hu
          subst hua
          have hrest' : IsPath (orderCx P).src (orderCx P).tgt p b v := hrest
          have hih := ih hrest'
          -- `[f a, f b] · (image of p under f) · [f v, g v]`
          have h1 : Htpy (orderCx Q) (f u) (g v)
              ([ordPos (hf hab)] ++ (mapPath (orderCxMap f hf) p ++ [ordPos (hfg v)]))
              ([ordPos (hf hab)] ++ ([ordPos (hfg b)] ++ mapPath (orderCxMap g hg) p)) :=
            Htpy.append_congr (isPath_ordPos (hf hab))
              (isPath_append_iff.mpr ⟨f v, isPath_mapPath (orderCxMap f hf) hrest',
                isPath_ordPos (hfg v)⟩) (Htpy.refl _) hih
          have h2 : Htpy (orderCx Q) (f u) (g v)
              ([ordPos (hf hab), ordPos (hfg b)] ++ mapPath (orderCxMap g hg) p)
              ([ordPos (hfg u), ordPos (hg hab)] ++ mapPath (orderCxMap g hg) p) :=
            Htpy.append_congr
              (show IsPath (orderCx Q).src (orderCx Q).tgt
                [ordPos (hf hab), ordPos (hfg b)] (f u) (g b) from ⟨rfl, rfl, rfl⟩)
              (isPath_mapPath (orderCxMap g hg) hrest')
              (htpy_square_pos hf hg hfg hab) (Htpy.refl _)
          have hgoal := h1.trans h2
          simpa [mapPath, orderCxMap, ordPos, ordNeg, List.append_assoc] using hgoal
      | false =>
          have hub : u = b := hu
          subst hub
          have hrest' : IsPath (orderCx P).src (orderCx P).tgt p a v := hrest
          have hih := ih hrest'
          have h1 : Htpy (orderCx Q) (f u) (g v)
              ([ordNeg (hf hab)] ++ (mapPath (orderCxMap f hf) p ++ [ordPos (hfg v)]))
              ([ordNeg (hf hab)] ++ ([ordPos (hfg a)] ++ mapPath (orderCxMap g hg) p)) :=
            Htpy.append_congr (isPath_ordNeg (hf hab))
              (isPath_append_iff.mpr ⟨f v, isPath_mapPath (orderCxMap f hf) hrest',
                isPath_ordPos (hfg v)⟩) (Htpy.refl _) hih
          have h2 : Htpy (orderCx Q) (f u) (g v)
              ([ordNeg (hf hab), ordPos (hfg a)] ++ mapPath (orderCxMap g hg) p)
              ([ordPos (hfg u), ordNeg (hg hab)] ++ mapPath (orderCxMap g hg) p) :=
            Htpy.append_congr
              (show IsPath (orderCx Q).src (orderCx Q).tgt
                [ordNeg (hf hab), ordPos (hfg a)] (f u) (g a) from ⟨rfl, rfl, rfl⟩)
              (isPath_mapPath (orderCxMap g hg) hrest')
              (htpy_square_neg hf hg hfg hab) (Htpy.refl _)
          have hgoal := h1.trans h2
          simpa [mapPath, orderCxMap, ordPos, ordNeg, List.append_assoc] using hgoal

/-- **The conjugation form of the naturality homotopy for a loop.**  The image of a loop under
`g` is homotopic to the image under `f` conjugated by the edge at the basepoint. -/
theorem htpy_loop_mapPath_le {f g : P → Q} (hf : Monotone f) (hg : Monotone g)
    (hfg : ∀ x, f x ≤ g x) {u : P} {p : List ((orderCx P).E × Bool)}
    (hp : IsPath (orderCx P).src (orderCx P).tgt p u u) :
    Htpy (orderCx Q) (g u) (g u) (mapPath (orderCxMap g hg) p)
      ([ordNeg (hfg u)] ++ mapPath (orderCxMap f hf) p ++ [ordPos (hfg u)]) := by
  have hnat := htpy_mapPath_le hf hg hfg p hp
  have hfp : IsPath (orderCx Q).src (orderCx Q).tgt (mapPath (orderCxMap f hf) p) (f u) (f u) :=
    isPath_mapPath (orderCxMap f hf) hp
  have hgp : IsPath (orderCx Q).src (orderCx Q).tgt (mapPath (orderCxMap g hg) p) (g u) (g u) :=
    isPath_mapPath (orderCxMap g hg) hp
  -- prepend `[g u, f u]` to the naturality homotopy and cancel a backtrack
  have h1 : Htpy (orderCx Q) (g u) (g u)
      ([ordNeg (hfg u)] ++ (mapPath (orderCxMap f hf) p ++ [ordPos (hfg u)]) ++ [])
      ([ordNeg (hfg u)] ++ ([ordPos (hfg u)] ++ mapPath (orderCxMap g hg) p) ++ []) :=
    hnat.congr_append (isPath_ordNeg (hfg u)) (isPath_nil' (g u))
  have h2 : Htpy (orderCx Q) (g u) (g u)
      ([] ++ [ordNeg (hfg u), ordPos (hfg u)] ++ mapPath (orderCxMap g hg) p)
      ([] ++ [] ++ mapPath (orderCxMap g hg) p) :=
    (htpy_ordNeg_ordPos (hfg u)).congr_append (isPath_nil' (g u)) hgp
  simp only [List.nil_append, List.append_nil, List.cons_append] at h1 h2 ⊢
  exact (h2.symm.trans h1.symm)

end Comb
end FiniteChains
