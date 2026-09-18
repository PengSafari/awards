import Jsp690.Certificates

namespace Jsp690

/-- Li's explicit nine-vertex construction is chromatic-critical. -/
theorem witness_critical : Critical3 witness := by
  exact critical3_of_edge_deletions
    ⟨threeColoring, witness_three_coloring⟩ witness_not_two_colorable
    witness_no_isolated witness_edge_deletions

/-- Complete JSP-000690, under its specified chromatic interpretation. -/
theorem jsp_000690 : ∃ H : Hypergraph (Fin 9),
    Uniform H 3 ∧ Critical3 H ∧ (∀ v ∈ H.vertices, 7 ≤ Degree H v) := by
  exact ⟨witness, witness_uniform, witness_critical, witness_min_degree⟩

/-- The stronger explicit witness also records both cardinalities and exact
minimum degree, rather than just a degree lower bound. -/
theorem jsp_000690_nine_vertices : ∃ H : Hypergraph (Fin 9),
    H.vertices.card = 9 ∧ H.edges.card = 22 ∧ Uniform H 3 ∧ Critical3 H ∧
    (∀ v ∈ H.vertices, 7 ≤ Degree H v) ∧
    (∃ v ∈ H.vertices, Degree H v = 7) := by
  exact ⟨witness, witness_vertex_count, witness_edge_count, witness_uniform,
    witness_critical, witness_min_degree, 1, Finset.mem_univ 1, witness_degree_seven⟩

/-- The ordinary interpretation, with colorings on the actual retained vertex
set, also holds for every proper subhypergraph. -/
theorem witness_actual_vertex_critical :
    VertexColorable witness 3 ∧ ¬ VertexColorable witness 2 ∧
    ∀ G : Hypergraph Vertex, IsProperSubhypergraph G witness → VertexColorable G 2 := by
  refine ⟨vertexColorable_of_colorable witness_critical.1, ?_, ?_⟩
  · intro h
    exact witness_not_two_colorable ((colorable_iff_vertexColorable (by decide)).mpr h)
  · intro G hG
    exact vertexColorable_of_colorable (witness_critical.2.2 G hG)

end Jsp690
