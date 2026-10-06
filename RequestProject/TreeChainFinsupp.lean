module

public import RequestProject.TreeChainTopological
public import RequestProject.TreeCoverNecessityFinsupp
public import RequestProject.PresChainTopologicalFinsupp

@[expose] public section

/-! Necessity for arbitrary connected cellular two-complexes and arbitrary cellular chains. -/

namespace FiniteChains.Comb
universe u

structure TopChainFS (K : Complex2.{u}) (n : ℕ) where
  /-- The stages of the chain. -/
  X : ℕ → Complex2.{u}
  /-- The inclusion of `X r` in `X (r + 1)`. -/
  inc : ∀ r, Hom (X r) (X (r + 1))
  incV : ∀ r, Function.Injective (inc r).onV
  incE : ∀ r, Function.Injective (inc r).onE
  incF : ∀ r, Function.Injective (inc r).onF
  /-- Every stage is connected. -/
  conn : ∀ r, IsConnected (X r)
  /-- The inclusion of `K` in the first stage. -/
  base : Hom K (X 0)
  baseV : Function.Injective base.onV
  baseE : Function.Injective base.onE
  baseF : Function.Injective base.onF
  /-- **The inclusion `X r ⊂ X (r + 1)` is zero on `π₂`.** -/
  zero_pi2 : ∀ r, r < n → ZeroPi2 (inc r)

namespace TopChainFS

variable {K : Complex2.{u}} {n : ℕ} (c : TopChainFS K n) (T₀ : SpanningTree K)

/-- The stages of a chain, with `K` itself put in front. -/
def shiftX : ℕ → Complex2.{u}
  | 0 => K
  | r + 1 => c.X r

/-- The inclusions of the shifted chain. -/
def shiftInc : ∀ r, Hom (c.shiftX r) (c.shiftX (r + 1))
  | 0 => c.base
  | r + 1 => c.inc r

theorem shiftInc_injective_onV : ∀ r, Function.Injective (c.shiftInc r).onV
  | 0 => c.baseV
  | r + 1 => c.incV r

theorem shiftInc_injective_onE : ∀ r, Function.Injective (c.shiftInc r).onE
  | 0 => c.baseE
  | r + 1 => c.incE r

theorem shiftConn (hconn : IsConnected K) : ∀ r, IsConnected (c.shiftX r)
  | 0 => hconn
  | r + 1 => c.conn r

/-- **Spanning trees compatible with the whole chain**, starting from the given spanning tree
of `K`. -/
theorem exists_trees (hconn : IsConnected K) :
    ∃ T : ∀ r, SpanningTree (c.shiftX r), T 0 = T₀ ∧
      ∀ (r : ℕ) (e : (c.shiftX r).E),
        (T (r + 1)).isTree ((c.shiftInc r).onE e) ↔ (T r).isTree e :=
  SpanningTree.exists_compatible_trees c.shiftX c.shiftInc (c.shiftConn hconn)
    c.shiftInc_injective_onV c.shiftInc_injective_onE T₀

end TopChainFS


/-- Arbitrary cellular chains killing universal-cover two-cycles produce a connected
regular cover with vanishing reduced cellular homology. -/
theorem fs_hasAcyclicRegularCover_of_topChains {K : Complex2.{u}}
    (hconn : IsConnected K) (x₀ : K.V)
    (hchains : ∀ n, Nonempty (TopChainFS K n)) : HasAcyclicRegularCover K := by
  classical
  obtain ⟨T₀⟩ := SpanningTree.exists_of_isConnected hconn x₀
  apply SpanningTree.fs_hasAcyclicRegularCover_of_presChains T₀
  intro n
  obtain ⟨c⟩ := hchains n
  obtain ⟨T, hT0, hTinc⟩ := c.exists_trees T₀ hconn
  let hinc r := hTinc (r + 1)
  have hbase : ∀ e : K.E, (T 1).isTree (c.base.onE e) ↔ T₀.isTree e := by
    intro e
    have he := hTinc 0 e
    rw [hT0] at he
    exact he
  refine ⟨(PresChainTopFS.toPresChainFS {
    gen := fun r => SpanningTree.NonTree (T (r + 1))
    cell := fun r => (c.X r).F
    decGen := fun _ => inferInstance
    rel := fun r => SpanningTree.treeRel (T (r + 1))
    genIncl := fun r => SpanningTree.nonTreeIncl (hinc r)
    genIncl_injective := fun r => SpanningTree.nonTreeIncl_injective (hinc r) (c.incE r)
    cellIncl := fun r => (c.inc r).onF
    cellIncl_injective := c.incF
    rel_incl := fun r => SpanningTree.treeRel_onF (hinc r)
    baseGen := SpanningTree.nonTreeIncl hbase
    baseGen_injective := SpanningTree.nonTreeIncl_injective hbase c.baseE
    baseCell := c.base.onF
    baseCell_injective := c.baseF
    rel_base := SpanningTree.treeRel_onF hbase
    zero_pi2 := fun r hr => SpanningTree.zeroPi2_presInclHom_of_zeroPi2
      (hinc r) (c.incE r) (c.zero_pi2 r hr) })⟩

end FiniteChains.Comb
