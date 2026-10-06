module

public import RequestProject.CombPi1

@[expose] public section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb
universe u
variable {X : Complex2.{u}} {o a b c : X.V}

/-- The actual based loop obtained by joining a path to chosen paths from the root. -/
def rootedPathLoop (r : List (X.E × Bool)) (hr : IsPath X.src X.tgt r o a)
    (p : List (X.E × Bool)) (hp : IsPath X.src X.tgt p a b)
    (s : List (X.E × Bool)) (hs : IsPath X.src X.tgt s o b) : Loop X o :=
  ⟨r ++ p ++ revPath s, (hr.append hp).append (isPath_revPath hs)⟩

/-- Actual rooted path classes multiply by concatenation; the intermediate root path cancels. -/
theorem rootedPathLoop_append (r : List (X.E × Bool)) (hr : IsPath X.src X.tgt r o a)
    (p : List (X.E × Bool)) (hp : IsPath X.src X.tgt p a b)
    (s : List (X.E × Bool)) (hs : IsPath X.src X.tgt s o b)
    (q : List (X.E × Bool)) (hq : IsPath X.src X.tgt q b c)
    (t : List (X.E × Bool)) (ht : IsPath X.src X.tgt t o c) :
    Pi1.mk (rootedPathLoop r hr (p ++ q) (hp.append hq) t ht) =
      Pi1.mk (rootedPathLoop r hr p hp s hs) *
        Pi1.mk (rootedPathLoop s hs q hq t ht) := by
  apply Quotient.sound
  have h := (htpy_revPath_append hs).congr_append (hr.append hp)
    (hq.append (isPath_revPath ht))
  change Htpy X o o ((r ++ (p ++ q)) ++ revPath t)
    ((r ++ p ++ revPath s) ++ (s ++ q ++ revPath t))
  simpa only [List.append_assoc, List.nil_append] using h.symm

/-- Closing the empty actual path at a vertex gives the trivial based loop. -/
theorem rootedPathLoop_nil (r : List (X.E × Bool)) (hr : IsPath X.src X.tgt r o a) :
    Pi1.mk (rootedPathLoop r hr [] rfl r hr) = 1 := by
  apply Quotient.sound
  change Htpy X o o _ _
  simpa only [rootedPathLoop, List.append_nil] using htpy_append_revPath hr

/-- Close an actual oriented edge by actual paths from the root to its endpoints. -/
def rootedGermLoop (r : X.V → List (X.E × Bool))
    (hr : ∀ v, IsPath X.src X.tgt (r v) o v) (e : X.E × Bool) : Loop X o :=
  rootedPathLoop (r (germSrc X.src X.tgt e)) (hr _) [e] (isPath_single e)
    (r (germTgt X.src X.tgt e)) (hr _)

/-- Every actual rooted path class factors into its actual rooted single-edge classes. -/
theorem rootedPathLoop_eq_prod (r : X.V → List (X.E × Bool))
    (hr : ∀ v, IsPath X.src X.tgt (r v) o v)
    (p : List (X.E × Bool)) (a b : X.V) (hp : IsPath X.src X.tgt p a b) :
    Pi1.mk (rootedPathLoop (r a) (hr a) p hp (r b) (hr b)) =
      (p.map (fun e => Pi1.mk (rootedGermLoop r hr e))).prod := by
  induction p generalizing a with
  | nil =>
    change a = b at hp
    subst b
    exact rootedPathLoop_nil _ _
  | cons e p ih =>
    obtain ⟨he, hp⟩ := hp
    subst a
    have h := rootedPathLoop_append (r (germSrc X.src X.tgt e)) (hr _)
      [e] (isPath_single e) (r (germTgt X.src X.tgt e)) (hr _) p hp (r b) (hr b)
    simpa only [List.singleton_append, List.map_cons, List.prod_cons,
      rootedGermLoop, ih _ hp] using h

/-- Reversing an actual rooted germ inverts its actual loop class. -/
theorem rootedGermLoop_rev (r : X.V → List (X.E × Bool))
    (hr : ∀ v, IsPath X.src X.tgt (r v) o v) (e : X.E × Bool) :
    Pi1.mk (rootedGermLoop r hr (revGerm e)) =
      (Pi1.mk (rootedGermLoop r hr e))⁻¹ := by
  apply Quotient.sound
  change Htpy X o o (rootedGermLoop r hr (revGerm e)).val
    (revPath (rootedGermLoop r hr e).val)
  simp only [rootedGermLoop, rootedPathLoop, germSrc_revGerm, germTgt_revGerm,
    revPath_append, revPath_revPath, revPath_cons, revPath_nil,
    List.nil_append, List.append_assoc]
  exact Htpy.refl _

end FiniteChains.Comb
