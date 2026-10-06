module

public import RequestProject.VertexPuncturedCube
public import RequestProject.OrderComplexRetraction

@[expose] public section

namespace FiniteChains.Davis
open Comb

def vertexIntersectionCoordinates (i : Fin 7) : Cube (Fin 3) :=
  ![![CubeCoord.free, .neg, .neg], ![CubeCoord.free, .neg, .free],
    ![CubeCoord.free, .neg, .pos], ![CubeCoord.free, .pos, .neg],
    ![CubeCoord.free, .free, .neg], ![CubeCoord.free, .pos, .free],
    ![CubeCoord.free, .free, .pos]] i

def vertexIntersectionCell (i : Fin 7) : VertexPuncturedCube :=
  ⟨vertexIntersectionCoordinates i, by fin_cases i <;> decide⟩

theorem vertexIntersectionCell_mem (i : Fin 7) :
    vertexPunctureLeft (vertexIntersectionCell i) ∧
      vertexPunctureRight (vertexIntersectionCell i) := by
  unfold vertexPunctureLeft vertexPunctureRight
  fin_cases i <;> decide

theorem vertexIntersection_classify (c : VertexPuncturedCube)
    (hc : vertexPunctureLeft c ∧ vertexPunctureRight c) :
    ∃ i : Fin 7, c = vertexIntersectionCell i := by
  obtain ⟨h0, hne⟩ := (vertexPuncture_intersection_iff c).mp hc
  have hv : c.1 = ![CubeCoord.free, c.1 1, c.1 2] := by
    funext v
    fin_cases v
    · exact h0
    · rfl
    · rfl
  cases h1 : c.1 1 <;> cases h2 : c.1 2 <;> rw [h1, h2] at hv
  case free.free =>
    exact False.elim (c.2.1 (hv.trans (by decide)))
  case free.pos => exact ⟨6, Subtype.ext hv⟩
  case free.neg => exact ⟨4, Subtype.ext hv⟩
  case pos.free => exact ⟨5, Subtype.ext hv⟩
  case pos.pos => exact False.elim (hne (hv.trans (by decide)))
  case pos.neg => exact ⟨3, Subtype.ext hv⟩
  case neg.free => exact ⟨1, Subtype.ext hv⟩
  case neg.pos => exact ⟨2, Subtype.ext hv⟩
  case neg.neg => exact ⟨0, Subtype.ext hv⟩

def vertexIntersectionAdjacent (i j : Fin 7) : Prop :=
  CoordinateFace (vertexIntersectionCoordinates i) (vertexIntersectionCoordinates j) ∨
    CoordinateFace (vertexIntersectionCoordinates j) (vertexIntersectionCoordinates i)

instance (i j : Fin 7) : Decidable (vertexIntersectionAdjacent i j) := by
  unfold vertexIntersectionAdjacent CoordinateFace
  infer_instance

/-- A finite, kernel-checked reachability certificate for the seven actual intersection cells. -/
theorem vertexIntersection_links : ∀ i : Fin 7, ∃ j k : Fin 7,
    vertexIntersectionAdjacent i j ∧ vertexIntersectionAdjacent j k ∧
      vertexIntersectionAdjacent k 0 := by decide

theorem intersection_path_of_adjacent (i j : Fin 7)
    (h : vertexIntersectionAdjacent i j) :
    ∃ p, IsPath (orderCx VertexPuncturedCube).src (orderCx VertexPuncturedCube).tgt
      p (vertexIntersectionCell i) (vertexIntersectionCell j) ∧
      PathIn (fun c => vertexPunctureLeft c ∧ vertexPunctureRight c) p := by
  rcases h with h | h
  · exact ⟨[ordPos h], isPath_ordPos h,
      pathIn_cons ⟨vertexIntersectionCell_mem i, vertexIntersectionCell_mem j⟩ (pathIn_nil _)⟩
  · exact ⟨[ordNeg h], isPath_ordNeg h,
      pathIn_cons ⟨vertexIntersectionCell_mem j, vertexIntersectionCell_mem i⟩ (pathIn_nil _)⟩

theorem vertexPuncture_intersection_connected :
    ConnectedIn (fun c : VertexPuncturedCube => vertexPunctureLeft c ∧ vertexPunctureRight c) := by
  have reach (i : Fin 7) : ∃ p,
      IsPath (orderCx VertexPuncturedCube).src (orderCx VertexPuncturedCube).tgt
        p (vertexIntersectionCell i) (vertexIntersectionCell 0) ∧
      PathIn (fun c => vertexPunctureLeft c ∧ vertexPunctureRight c) p := by
    obtain ⟨j, k, hij, hjk, hk0⟩ := vertexIntersection_links i
    obtain ⟨p, hp, hpin⟩ := intersection_path_of_adjacent i j hij
    obtain ⟨r, hr, hrin⟩ := intersection_path_of_adjacent j k hjk
    obtain ⟨s, hs, hsin⟩ := intersection_path_of_adjacent k 0 hk0
    exact ⟨p ++ r ++ s, (hp.append hr).append hs,
      pathIn_append (pathIn_append hpin hrin) hsin⟩
  intro a b ha hb
  obtain ⟨i, rfl⟩ := vertexIntersection_classify a ha
  obtain ⟨j, rfl⟩ := vertexIntersection_classify b hb
  obtain ⟨p, hp, hpin⟩ := reach i
  obtain ⟨r, hr, hrin⟩ := reach j
  exact ⟨p ++ revPath r, hp.append (isPath_revPath hr),
    pathIn_append hpin (pathIn_revPath hrin)⟩

theorem vertexPuncturedCube_simplyConnected : SimplyConnected (orderCx VertexPuncturedCube) := by
  have hnull := htpy_nil_of_pathIn_union
    (U := fun _ : VertexPuncturedCube => True)
    (A := vertexPunctureLeft) (B := vertexPunctureRight)
    (fun c => ⟨fun _ => vertexPuncture_cover c, fun _ => trivial⟩)
    (fun c d h _ _ => vertexPuncture_unmixed c d h)
    (nullIn_of_simplyConnected vertexPunctureLeft_simplyConnected)
    (nullIn_of_simplyConnected vertexPunctureRight_simplyConnected)
    (connectedIn_of_isConnected vertexPunctureLeft_connected)
    (connectedIn_of_isConnected vertexPunctureRight_connected)
    vertexPuncture_intersection_connected (vertexIntersectionCell_mem 0)
  intro a p hp
  exact hnull a p trivial hp (fun _ _ => ⟨trivial, trivial⟩)

theorem vertexPuncturedCube_connected : IsConnected (orderCx VertexPuncturedCube) := by
  have reach (c : VertexPuncturedCube) : ∃ p,
      IsPath (orderCx VertexPuncturedCube).src (orderCx VertexPuncturedCube).tgt
        p c (vertexIntersectionCell 0) := by
    rcases vertexPuncture_cover c with hc | hc
    · obtain ⟨p, hp, _⟩ := (connectedIn_of_isConnected vertexPunctureLeft_connected)
        c (vertexIntersectionCell 0) hc (vertexIntersectionCell_mem 0).1
      exact ⟨p, hp⟩
    · obtain ⟨p, hp, _⟩ := (connectedIn_of_isConnected vertexPunctureRight_connected)
        c (vertexIntersectionCell 0) hc (vertexIntersectionCell_mem 0).2
      exact ⟨p, hp⟩
  intro a b
  obtain ⟨p, hp⟩ := reach a
  obtain ⟨r, hr⟩ := reach b
  exact ⟨p ++ revPath r, hp.append (isPath_revPath hr)⟩

end FiniteChains.Davis
