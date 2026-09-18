import Mathlib.Data.Finset.Card

/-!
# Finite hypergraphs and critical colorability

Edges are finite sets of vertices, so the hypergraphs here are simple and
unordered. A proper coloring means that no edge is monochromatic. In particular,
an empty edge or a singleton edge cannot be properly colored.
-/

namespace Jsp690

variable {V : Type*} [DecidableEq V]

/-- A finite simple hypergraph on an ambient vertex type. -/
structure Hypergraph (V : Type*) [DecidableEq V] where
  vertices : Finset V
  edges : Finset (Finset V)
  edge_subset_vertices : ∀ e ∈ edges, e ⊆ vertices

/-- Every edge contains two vertices of different colors. -/
def ProperColoring (E : Finset (Finset V)) {k : Nat} (c : V → Fin k) : Prop :=
  ∀ e ∈ E, ∃ u ∈ e, ∃ v ∈ e, c u ≠ c v

/-- A coloring of the ambient type which is proper on the hypergraph's edges. -/
def Colorable (H : Hypergraph V) (k : Nat) : Prop :=
  ∃ c : V → Fin k, ProperColoring H.edges c

def Uniform (H : Hypergraph V) (r : Nat) : Prop :=
  ∀ e ∈ H.edges, e.card = r

def Degree (H : Hypergraph V) (v : V) : Nat :=
  (H.edges.filter (fun e => v ∈ e)).card

/-- Subhypergraphs may remove both edges and vertices. -/
def IsSubhypergraph (G H : Hypergraph V) : Prop :=
  G.vertices ⊆ H.vertices ∧ G.edges ⊆ H.edges

def IsProperSubhypergraph (G H : Hypergraph V) : Prop :=
  IsSubhypergraph G H ∧ (G.vertices ≠ H.vertices ∨ G.edges ≠ H.edges)

/-- Chromatic number three, with every proper subhypergraph two-colorable. -/
def Critical3 (H : Hypergraph V) : Prop :=
  Colorable H 3 ∧ ¬ Colorable H 2 ∧
    ∀ G : Hypergraph V, IsProperSubhypergraph G H → Colorable G 2

/-- The equivalent usual definition colors only vertices actually in `H`. -/
def VertexColorable (H : Hypergraph V) (k : Nat) : Prop :=
  ∃ c : {v // v ∈ H.vertices} → Fin k,
    ∀ e ∈ H.edges,
      ∃ u v : {v // v ∈ H.vertices}, u.val ∈ e ∧ v.val ∈ e ∧ c u ≠ c v

/-- Restricting an ambient coloring gives a coloring of the actual vertex set. -/
theorem vertexColorable_of_colorable {H : Hypergraph V} {k : Nat}
    (h : Colorable H k) : VertexColorable H k := by
  obtain ⟨c, hc⟩ := h
  refine ⟨fun v => c v.val, ?_⟩
  intro e he
  obtain ⟨u, hu, v, hv, huv⟩ := hc e he
  exact ⟨⟨u, H.edge_subset_vertices e he hu⟩,
    ⟨v, H.edge_subset_vertices e he hv⟩, hu, hv, huv⟩

/-- A nonempty palette lets us extend a coloring outside the actual vertex set. -/
theorem colorable_iff_vertexColorable {H : Hypergraph V} {k : Nat}
    (hk : 0 < k) : Colorable H k ↔ VertexColorable H k := by
  constructor
  · exact vertexColorable_of_colorable
  · rintro ⟨c, hc⟩
    let c' : V → Fin k := fun v =>
      if hv : v ∈ H.vertices then c ⟨v, hv⟩ else ⟨0, hk⟩
    refine ⟨c', ?_⟩
    intro e he
    obtain ⟨u, v, hu, hv, huv⟩ := hc e he
    refine ⟨u.val, hu, v.val, hv, ?_⟩
    simpa [c', u.property, v.property] using huv

omit [DecidableEq V] in
/-- Removing edges preserves a proper coloring. -/
theorem ProperColoring.mono {E F : Finset (Finset V)} {k : Nat} {c : V → Fin k}
    (hc : ProperColoring E c) (hFE : F ⊆ E) : ProperColoring F c := by
  intro e he
  exact hc e (hFE he)

/-- In a hypergraph with no isolated vertices, every proper subhypergraph
omits an edge. This includes subhypergraphs obtained by deleting vertices. -/
theorem exists_missing_edge_of_proper {H G : Hypergraph V}
    (hnoisolated : ∀ v ∈ H.vertices, ∃ e ∈ H.edges, v ∈ e)
    (hproper : IsProperSubhypergraph G H) :
    ∃ e ∈ H.edges, e ∉ G.edges := by
  have hn : ¬ H.edges ⊆ G.edges := by
    intro hHG
    have heq : G.edges = H.edges := Finset.Subset.antisymm hproper.1.2 hHG
    have hVG : H.vertices ⊆ G.vertices := by
      intro v hv
      obtain ⟨e, he, hve⟩ := hnoisolated v hv
      exact G.edge_subset_vertices e (hHG he) hve
    have hveq : G.vertices = H.vertices := Finset.Subset.antisymm hproper.1.1 hVG
    rcases hproper.2 with hvertices | hedges
    · exact hvertices hveq
    · exact hedges heq
  exact Finset.not_subset.mp hn

/-- Colorings after single-edge deletions certify all proper subhypergraphs,
provided the original hypergraph has no isolated vertices. -/
theorem colorable_of_proper {H G : Hypergraph V}
    (hnoisolated : ∀ v ∈ H.vertices, ∃ e ∈ H.edges, v ∈ e)
    (hdelete : ∀ e ∈ H.edges,
      ∃ c : V → Fin 2, ProperColoring (H.edges.erase e) c)
    (hproper : IsProperSubhypergraph G H) : Colorable G 2 := by
  obtain ⟨e, heH, heG⟩ := exists_missing_edge_of_proper hnoisolated hproper
  obtain ⟨c, hc⟩ := hdelete e heH
  refine ⟨c, hc.mono ?_⟩
  intro f hf
  refine Finset.mem_erase.mpr ⟨?_, hproper.1.2 hf⟩
  intro hfe
  apply heG
  simpa [hfe] using hf

/-- Assemble a three-critical hypergraph from finite coloring certificates. -/
theorem critical3_of_edge_deletions {H : Hypergraph V}
    (hthree : Colorable H 3)
    (hnotwo : ¬ Colorable H 2)
    (hnoisolated : ∀ v ∈ H.vertices, ∃ e ∈ H.edges, v ∈ e)
    (hdelete : ∀ e ∈ H.edges,
      ∃ c : V → Fin 2, ProperColoring (H.edges.erase e) c) : Critical3 H := by
  exact ⟨hthree, hnotwo, fun _ hproper =>
    colorable_of_proper hnoisolated hdelete hproper⟩

end Jsp690
