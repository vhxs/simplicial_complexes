import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Image

/-!
# Combinatorial Simplicial Complexes

This file defines combinatorial simplicial complexes: a collection of finite sets (faces)
of vertices, closed under taking nonempty subsets.

## Main definitions

* `CombinatorialSimplicialComplex V`: A combinatorial simplicial complex on vertex type `V`.
* `CombinatorialSimplicialComplex.vertices`: The vertex set (singletons that are faces).
* `CombinatorialSimplicialComplex.facets`: The maximal faces.
-/

open Finset Set

/-- A combinatorial simplicial complex on vertex type `V` is a collection of nonempty
finite sets (faces) closed under taking nonempty subsets. -/
structure CombinatorialSimplicialComplex (V : Type*) where
  /-- The set of faces. -/
  faces : Set (Finset V)
  /-- Every face is nonempty. -/
  nonempty_of_mem : ∀ {s}, s ∈ faces → s.Nonempty
  /-- The face set is downward closed: any nonempty subset of a face is also a face. -/
  down_closed : ∀ {s t}, s ∈ faces → t ⊆ s → t.Nonempty → t ∈ faces

namespace CombinatorialSimplicialComplex

variable {V : Type*} {K : CombinatorialSimplicialComplex V}

theorem not_mem_empty : (∅ : Finset V) ∉ K.faces :=
  fun h => absurd (K.nonempty_of_mem h) (by simp)

/-- Any singleton `{v}` contained in a face is itself a face. -/
theorem singleton_mem_of_mem {s : Finset V} {v : V} (hs : s ∈ K.faces) (hv : v ∈ s) :
    ({v} : Finset V) ∈ K.faces :=
  K.down_closed hs (singleton_subset_iff.mpr hv) (singleton_nonempty v)

/-! ### Vertices -/

/-- The vertices of `K`: the set of `v : V` such that `{v}` is a face. -/
def vertices (K : CombinatorialSimplicialComplex V) : Set V :=
  { v | ({v} : Finset V) ∈ K.faces }

theorem mem_vertices {v : V} : v ∈ K.vertices ↔ ({v} : Finset V) ∈ K.faces :=
  Iff.rfl

/-- Every vertex appearing in a face is a vertex of the complex. -/
theorem mem_vertices_of_mem {s : Finset V} (hs : s ∈ K.faces) {v : V} (hv : v ∈ s) :
    v ∈ K.vertices :=
  mem_vertices.mpr (K.singleton_mem_of_mem hs hv)

/-! ### Facets -/

/-- The facets of `K`: the maximal faces. -/
def facets (K : CombinatorialSimplicialComplex V) : Set (Finset V) :=
  { s ∈ K.faces | ∀ t ∈ K.faces, s ⊆ t → s = t }

theorem mem_facets {s : Finset V} :
    s ∈ K.facets ↔ s ∈ K.faces ∧ ∀ t ∈ K.faces, s ⊆ t → s = t :=
  Set.mem_sep_iff

theorem facets_subset : K.facets ⊆ K.faces :=
  fun _ hs => hs.1

theorem not_facet_iff_subface {s : Finset V} (hs : s ∈ K.faces) :
    s ∉ K.facets ↔ ∃ t ∈ K.faces, s ⊂ t := by
  rw [mem_facets, not_and_or]
  constructor
  · intro h
    rcases h with (h | h)
    · exact absurd hs h
    · push_neg at h
      obtain ⟨t, ht_mem, hst, hne⟩ := h
      exact ⟨t, ht_mem, hst, fun hts => hne (le_antisymm hst hts)⟩
  · rintro ⟨t, ht_mem, hst⟩
    right
    push_neg
    exact ⟨t, ht_mem, hst.1, fun h => hst.2 (le_of_eq h.symm)⟩

/-! ### Constructions -/

/-- The empty complex (no faces). -/
def empty : CombinatorialSimplicialComplex V where
  faces := ∅
  nonempty_of_mem h := absurd h (Set.notMem_empty _)
  down_closed h := absurd h (Set.notMem_empty _)

instance : Inhabited (CombinatorialSimplicialComplex V) := ⟨empty⟩

/-- The full simplex on a nonempty finite set `s`. -/
def fullSimplex {s : Finset V} (_ : s.Nonempty) : CombinatorialSimplicialComplex V where
  faces := { t | t ⊆ s ∧ t.Nonempty }
  nonempty_of_mem h := h.2
  down_closed h hts ht := ⟨hts.trans h.1, ht⟩

end CombinatorialSimplicialComplex
