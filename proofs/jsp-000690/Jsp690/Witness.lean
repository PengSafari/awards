import Jsp690.Basic
import Mathlib.Data.Fintype.Pi

/-! Ruiliang Li, arXiv:2512.24850v1, equation (5).
Vertices 1,...,9 in the paper are relabelled 0,...,8.
This file is generated from the independently checked witness.json. -/

namespace Jsp690

abbrev Vertex := Fin 9

def edges : Finset (Finset Vertex) :=
  {{0, 1, 2},
   {0, 1, 8},
   {0, 2, 7},
   {0, 3, 5},
   {0, 3, 7},
   {0, 3, 8},
   {0, 4, 6},
   {0, 4, 7},
   {0, 4, 8},
   {0, 5, 6},
   {1, 2, 5},
   {1, 2, 6},
   {1, 3, 8},
   {1, 4, 8},
   {1, 5, 6},
   {2, 3, 7},
   {2, 4, 7},
   {2, 5, 6},
   {3, 5, 7},
   {3, 5, 8},
   {4, 6, 7},
   {4, 6, 8}}

def witness : Hypergraph Vertex where
  vertices := Finset.univ
  edges := edges
  edge_subset_vertices := by
    intro e _ v _
    exact Finset.mem_univ v

def threeColoring (v : Vertex) : Fin 3 :=
  match v.val with
  | 2 => 1
  | 5 => 1
  | 6 => 2
  | 7 => 1
  | 8 => 1
  | _ => 0

def blueCertificates : Finset (Finset Vertex) :=
  {{5, 6, 7, 8},
   {2, 3, 4, 6},
   {1, 3, 4, 6},
   {2, 6, 7, 8},
   {2, 4, 5, 8},
   {1, 4, 5, 7},
   {2, 5, 7, 8},
   {2, 3, 6, 8},
   {1, 3, 6, 7},
   {1, 2, 3, 4},
   {1, 2, 3, 4, 5},
   {1, 2, 3, 4, 6},
   {1, 3, 6, 7, 8},
   {1, 4, 5, 7, 8},
   {1, 5, 6, 7, 8},
   {2, 3, 6, 7, 8},
   {2, 4, 5, 7, 8},
   {2, 5, 6, 7, 8},
   {1, 3, 4, 5, 7},
   {2, 3, 4, 5, 8},
   {1, 3, 4, 6, 7},
   {2, 3, 4, 6, 8}}

def coloringOfBlue (S : Finset Vertex) (v : Vertex) : Fin 2 :=
  if v ∈ S then 1 else 0

end Jsp690
