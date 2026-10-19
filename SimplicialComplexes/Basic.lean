import Mathlib.AlgebraicTopology.SimplicialComplex.Basic

/-!
# Combinatorial simplicial complexes

This file extends Mathlib's `PreAbstractSimplicialComplex`: a collection of finite sets (faces)
of vertices, closed under taking nonempty subsets. Mathlib packages both conditions into the
single field `isRelLowerSet_faces`; the `nonempty_of_mem` and `down_closed` lemmas below unpack
it into the two conditions separately, which is how the rest of this development uses it.

Mathlib's `AbstractSimplicialComplex` — the extension requiring every singleton to be a face —
is deliberately not used: the complexes built here (`fullSimplex`, `barySubdivision`, …) do not
have all singletons as faces in general.

## Main definitions

* `PreAbstractSimplicialComplex.vertices`: The vertex set (singletons that are faces).
* `PreAbstractSimplicialComplex.facets`: The maximal faces.
-/

open Finset Set

namespace PreAbstractSimplicialComplex

variable {V : Type*} {K : PreAbstractSimplicialComplex V}

/-- Every face is nonempty. -/
theorem nonempty_of_mem {s : Finset V} (hs : s ∈ K.faces) : s.Nonempty :=
  K.isRelLowerSet_faces.prop_of_mem hs

/-- The faces are downward closed: every nonempty subset of a face is a face. -/
theorem down_closed {s t : Finset V} (hs : s ∈ K.faces) (hts : t ⊆ s) (ht : t.Nonempty) :
    t ∈ K.faces :=
  K.isRelLowerSet_faces.mem_of_le hs hts ht

theorem notMem_empty : (∅ : Finset V) ∉ K.faces :=
  fun h => absurd (nonempty_of_mem h) (by simp)

/-- Any singleton `{v}` contained in a face is itself a face. -/
theorem singleton_mem_of_mem {s : Finset V} {v : V} (hs : s ∈ K.faces) (hv : v ∈ s) :
    ({v} : Finset V) ∈ K.faces :=
  down_closed hs (singleton_subset_iff.mpr hv) (singleton_nonempty v)

/-! ### Vertices -/

/-- The vertices of `K`: the set of `v : V` such that `{v}` is a face. -/
def vertices (K : PreAbstractSimplicialComplex V) : Set V :=
  { v | ({v} : Finset V) ∈ K.faces }

theorem mem_vertices {v : V} : v ∈ K.vertices ↔ ({v} : Finset V) ∈ K.faces :=
  Iff.rfl

/-- Every vertex appearing in a face is a vertex of the complex. -/
theorem mem_vertices_of_mem {s : Finset V} (hs : s ∈ K.faces) {v : V} (hv : v ∈ s) :
    v ∈ K.vertices :=
  mem_vertices.mpr (singleton_mem_of_mem hs hv)

/-! ### Facets -/

/-- The facets of `K`: the maximal faces. -/
def facets (K : PreAbstractSimplicialComplex V) : Set (Finset V) :=
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
    · push Not at h
      obtain ⟨t, ht_mem, hst, hne⟩ := h
      exact ⟨t, ht_mem, hst, fun hts => hne (le_antisymm hst hts)⟩
  · rintro ⟨t, ht_mem, hst⟩
    right
    push Not
    exact ⟨t, ht_mem, hst.1, fun h => hst.2 (le_of_eq h.symm)⟩

/-! ### Constructions -/

/-- The full simplex on a nonempty finite set `s`. -/
def fullSimplex {s : Finset V} (_ : s.Nonempty) : PreAbstractSimplicialComplex V where
  faces := { t | t ⊆ s ∧ t.Nonempty }
  isRelLowerSet_faces := fun {_} h => ⟨h.2, fun _ hts ht => ⟨hts.trans h.1, ht⟩⟩

end PreAbstractSimplicialComplex
