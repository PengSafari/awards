import Jsp690.Witness

/-! All finite facts below are checked by Lean's kernel using `decide`.
No external solver result or native evaluation axiom is used. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Jsp690

theorem witness_vertex_count : witness.vertices.card = 9 := by decide

theorem witness_edge_count : witness.edges.card = 22 := by decide

theorem witness_uniform : Uniform witness 3 := by
  unfold Uniform witness
  decide

theorem witness_degrees : ∀ v : Vertex,
    Degree witness v = if v = 0 then 10 else 7 := by
  unfold Degree witness
  decide

theorem witness_min_degree : ∀ v ∈ witness.vertices, 7 ≤ Degree witness v := by
  unfold Degree witness
  decide

theorem witness_degree_seven : Degree witness 1 = 7 := by
  unfold Degree witness
  decide

theorem witness_no_isolated : ∀ v ∈ witness.vertices,
    ∃ e ∈ witness.edges, v ∈ e := by
  decide

theorem witness_three_coloring : ProperColoring witness.edges threeColoring := by
  unfold ProperColoring witness
  decide

theorem witness_not_two_colorable : ¬ Colorable witness 2 := by
  unfold Colorable ProperColoring witness
  decide

theorem witness_edge_deletion_certificates : ∀ e ∈ witness.edges,
    ∃ S ∈ blueCertificates,
      ProperColoring (witness.edges.erase e) (coloringOfBlue S) := by
  unfold ProperColoring witness
  decide

theorem witness_edge_deletions : ∀ e ∈ witness.edges,
    ∃ c : Vertex → Fin 2, ProperColoring (witness.edges.erase e) c := by
  intro e he
  obtain ⟨S, _, hc⟩ := witness_edge_deletion_certificates e he
  exact ⟨coloringOfBlue S, hc⟩

end Jsp690
