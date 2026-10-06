import RequestProject.OrderComplexRetraction

/-!
# Transferring path statements along monotone maps and order isomorphisms

Auxiliary material for turning the injectivity statements of
`RequestProject/OrderComplexRetraction.lean` — which are formulated inside one ambient order
complex — into statements about the map of fundamental groups induced by a monotone map.

* `FiniteChains.Comb.htpyIn_true_iff` — a homotopy inside the whole poset is just a homotopy;
* `FiniteChains.Comb.mapPath_comp_eq_self` — a monotone map composed with a monotone left
  inverse returns an edge path unchanged;
* `FiniteChains.Comb.simplyConnected_orderCx_of_orderIso`,
  `FiniteChains.Comb.isConnected_orderCx_of_orderIso` — transfer of connectivity and simple
  connectedness along an order isomorphism;
* `FiniteChains.Comb.htpy_nil_of_injIn` and `FiniteChains.Comb.pi1Map_injective_of_injIn` —
  if the image subposet of a monotone embedding with a monotone retraction is injective on path
  classes inside the whole poset, then the induced map of fundamental groups is injective.
-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains
namespace Comb

universe u

variable {P Q R : Type u} [Preorder P] [Preorder Q] [Preorder R]

/-- A homotopy inside the whole poset is an ordinary homotopy. -/
theorem htpyIn_true_iff {a b : P} {p q : List ((orderCx P).E × Bool)} :
    HtpyIn (fun _ : P => True) a b p q ↔ Htpy (orderCx P) a b p q := by
  constructor
  · exact HtpyIn.htpy
  · intro h
    refine Relation.ReflTransGen.mono (fun x y hs => ?_) _ _ h
    exact hs.imp (fun h => ⟨h, fun _ _ => ⟨trivial, trivial⟩, fun _ _ => ⟨trivial, trivial⟩⟩)
      (fun h => ⟨h, fun _ _ => ⟨trivial, trivial⟩, fun _ _ => ⟨trivial, trivial⟩⟩)

/-- A monotone map followed by a monotone left inverse returns an edge path unchanged. -/
theorem mapPath_comp_eq_self {f : Q → P} (hf : Monotone f) {g : P → Q} (hg : Monotone g)
    (hgf : ∀ y, g (f y) = y) :
    ∀ l : List ((orderCx Q).E × Bool),
      mapPath (orderCxMap g hg) (mapPath (orderCxMap f hf) l) = l
  | [] => rfl
  | e :: t => by
      simp only [mapPath, List.map_cons, List.cons.injEq]
      refine ⟨?_, ?_⟩
      · refine Prod.ext ?_ rfl
        refine Subtype.ext (Prod.ext ?_ ?_)
        · exact hgf e.1.1.1
        · exact hgf e.1.1.2
      · simpa [mapPath] using mapPath_comp_eq_self hf hg hgf t

/-- Simple connectedness transfers along an order isomorphism. -/
theorem simplyConnected_orderCx_of_orderIso (e : P ≃o Q) (h : SimplyConnected (orderCx Q)) :
    SimplyConnected (orderCx P) := by
  intro a p hp
  have hmono : Monotone (e : P → Q) := fun _ _ hxy => e.monotone hxy
  have hmono' : Monotone (e.symm : Q → P) := fun _ _ hxy => e.symm.monotone hxy
  have himg := h (e a) (mapPath (orderCxMap (e : P → Q) hmono) p)
    (isPath_mapPath (orderCxMap (e : P → Q) hmono) hp)
  have hpush := mapPath_htpy (orderCxMap (e.symm : Q → P) hmono') himg
  rw [mapPath_comp_eq_self hmono hmono' (fun y => e.symm_apply_apply y) p] at hpush
  simpa [mapPath] using hpush

/-- Connectivity transfers along an order isomorphism. -/
theorem isConnected_orderCx_of_orderIso (e : P ≃o Q) (h : IsConnected (orderCx Q)) :
    IsConnected (orderCx P) := by
  intro a b
  have hmono' : Monotone (e.symm : Q → P) := fun _ _ hxy => e.symm.monotone hxy
  obtain ⟨l, hl⟩ := h (e a) (e b)
  refine ⟨mapPath (orderCxMap (e.symm : Q → P) hmono') l, ?_⟩
  have := isPath_mapPath (orderCxMap (e.symm : Q → P) hmono') hl
  simpa [e.symm_apply_apply] using this

/-- The lift of the image of an edge path, pushed back by a monotone retraction, is the original
path. -/
theorem mapPath_liftPathIn_mapPath {Bp : P → Prop} {f : Q → P} (hf : Monotone f)
    (hfB : ∀ y, Bp (f y)) {g : {z : P // Bp z} → Q} (hg : Monotone g)
    (hgf : ∀ y, g ⟨f y, hfB y⟩ = y) :
    ∀ (l : List ((orderCx Q).E × Bool)) (hl : PathIn Bp (mapPath (orderCxMap f hf) l)),
      mapPath (orderCxMap g hg) (liftPathIn (mapPath (orderCxMap f hf) l) hl) = l
  | [], _ => rfl
  | e :: t, hl => by
      have hrest := mapPath_liftPathIn_mapPath hf hfB hg hgf t (pathIn_of_cons hl).2
      simp only [mapPath, List.map_cons, liftPathIn, List.cons.injEq]
      refine ⟨?_, ?_⟩
      · refine Prod.ext ?_ rfl
        refine Subtype.ext (Prod.ext ?_ ?_)
        · exact hgf e.1.1.1
        · exact hgf e.1.1.2
      · simpa [mapPath] using hrest

/-- The image of an edge path under a monotone map with values in `Bp` lies inside `Bp`. -/
theorem pathIn_mapPath_of_image {Bp : P → Prop} {f : Q → P} (hf : Monotone f)
    (hfB : ∀ y, Bp (f y)) (l : List ((orderCx Q).E × Bool)) :
    PathIn Bp (mapPath (orderCxMap f hf) l) := by
  intro e he
  simp only [mapPath, List.mem_map] at he
  obtain ⟨x, -, rfl⟩ := he
  exact ⟨hfB _, hfB _⟩

/-- **From injectivity on path classes to injectivity on loops.**  If the image of a monotone map
`f` with a monotone retraction `g` is injective on path classes inside the whole poset, then a
loop of the source which becomes null-homotopic in the target is null-homotopic. -/
theorem htpy_nil_of_injIn {Bp : P → Prop} (hinj : InjIn (fun _ : P => True) Bp)
    {f : Q → P} (hf : Monotone f) (hfB : ∀ y, Bp (f y))
    {g : {z : P // Bp z} → Q} (hg : Monotone g) (hgf : ∀ y, g ⟨f y, hfB y⟩ = y)
    {y : Q} {p : List ((orderCx Q).E × Bool)}
    (hp : IsPath (orderCx Q).src (orderCx Q).tgt p y y)
    (h : Htpy (orderCx P) (f y) (f y) (mapPath (orderCxMap f hf) p) []) :
    Htpy (orderCx Q) y y p [] := by
  have hpB : PathIn Bp (mapPath (orderCxMap f hf) p) := pathIn_mapPath_of_image hf hfB p
  have hloop : IsPath (orderCx P).src (orderCx P).tgt (mapPath (orderCxMap f hf) p) (f y) (f y) :=
    isPath_mapPath (orderCxMap f hf) hp
  have hIn : HtpyIn Bp (f y) (f y) (mapPath (orderCxMap f hf) p) [] :=
    hinj (f y) _ (hfB y) hloop hpB (htpyIn_true_iff.mpr h)
  have hlift : Htpy (orderCx {z : P // Bp z}) ⟨f y, hfB y⟩ ⟨f y, hfB y⟩
      (liftPathIn (mapPath (orderCxMap f hf) p) hpB)
      (liftPathIn ([] : List ((orderCx P).E × Bool)) (pathIn_nil Bp)) :=
    htpy_lift_of_htpyIn hIn (hfB y) (hfB y) hpB (pathIn_nil Bp)
  have hpush := mapPath_htpy (orderCxMap g hg) hlift
  rw [mapPath_liftPathIn_mapPath hf hfB hg hgf p hpB] at hpush
  simp only [orderCxMap_onV] at hpush
  rw [hgf y] at hpush
  simpa [mapPath, liftPathIn] using hpush

/-- **Injectivity of the induced map of fundamental groups.** -/
theorem pi1Map_injective_of_injIn {Bp : P → Prop} (hinj : InjIn (fun _ : P => True) Bp)
    {f : Q → P} (hf : Monotone f) (hfB : ∀ y, Bp (f y))
    {g : {z : P // Bp z} → Q} (hg : Monotone g) (hgf : ∀ y, g ⟨f y, hfB y⟩ = y) (y : Q) :
    Function.Injective (Comb.pi1Map (orderCxMap f hf) y) := by
  refine (injective_iff_map_eq_one _).mpr ?_
  intro c hc
  induction c using Quotient.inductionOn with
  | h p =>
      have h : Htpy (orderCx P) (f y) (f y) (mapPath (orderCxMap f hf) p.1) [] :=
        Quotient.exact hc
      exact Quotient.sound (htpy_nil_of_injIn hinj hf hfB hg hgf p.2 h)

end Comb
end FiniteChains
