import Mathlib.AlgebraicTopology.SimplicialComplex.Basic
import Mathlib.Data.Finset.Card

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
* `PreAbstractSimplicialComplex.IsPure`: All facets have the same number of vertices.
* `PreAbstractSimplicialComplex.skeleton`: The faces with at most `n + 1` vertices.
* `PreAbstractSimplicialComplex.link`: The faces disjoint from `s` whose union with `s` is a
  face — the combinatorial link `Lk(s, K)`.
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

/-! ### Dimension and purity -/

/-- `K` is pure of dimension `n` when every facet has `n + 1` vertices, i.e. dimension `n`.

The number of vertices is used in place of the dimension throughout, to avoid truncated
subtraction on `ℕ`. -/
def IsPure (K : PreAbstractSimplicialComplex V) (n : ℕ) : Prop :=
  ∀ s ∈ K.facets, s.card = n + 1

/-! ### Skeleta -/

/-- The `n`-skeleton of `K`: the faces with at most `n + 1` vertices, i.e. of dimension at
most `n`. -/
def skeleton (K : PreAbstractSimplicialComplex V) (n : ℕ) : PreAbstractSimplicialComplex V where
  faces := {s ∈ K.faces | s.card ≤ n + 1}
  isRelLowerSet_faces := fun {_} h =>
    ⟨nonempty_of_mem h.1, fun _ hts ht =>
      ⟨down_closed h.1 hts ht, le_trans (Finset.card_le_card hts) h.2⟩⟩

@[simp]
theorem mem_skeleton_iff {K : PreAbstractSimplicialComplex V} {n : ℕ} {s : Finset V} :
    s ∈ (K.skeleton n).faces ↔ s ∈ K.faces ∧ s.card ≤ n + 1 := Iff.rfl

theorem skeleton_le (K : PreAbstractSimplicialComplex V) (n : ℕ) : K.skeleton n ≤ K :=
  fun _ hs => hs.1

theorem skeleton_mono (K : PreAbstractSimplicialComplex V) {m n : ℕ} (h : m ≤ n) :
    K.skeleton m ≤ K.skeleton n :=
  fun _ hs => ⟨hs.1, le_trans hs.2 (by omega)⟩

/-! ### Links -/

section Link

variable [DecidableEq V]

/-- The link of `s` in `K`: the faces disjoint from `s` that together with `s` span a face.
Written `Lk(s, K)` in the literature. -/
def link (K : PreAbstractSimplicialComplex V) (s : Finset V) : PreAbstractSimplicialComplex V where
  faces := {t | t ∈ K.faces ∧ Disjoint t s ∧ t ∪ s ∈ K.faces}
  isRelLowerSet_faces := fun {_} h =>
    ⟨nonempty_of_mem h.1, fun {_} ht' hne =>
      ⟨down_closed h.1 ht' hne, Disjoint.mono_left ht' h.2.1,
        down_closed h.2.2 (Finset.union_subset_union ht' (Finset.Subset.refl _))
          (Finset.Nonempty.mono Finset.subset_union_left hne)⟩⟩

@[simp]
theorem mem_link_iff {K : PreAbstractSimplicialComplex V} {s t : Finset V} :
    t ∈ (K.link s).faces ↔ t ∈ K.faces ∧ Disjoint t s ∧ t ∪ s ∈ K.faces := Iff.rfl

theorem link_le (K : PreAbstractSimplicialComplex V) (s : Finset V) : K.link s ≤ K :=
  fun _ ht => ht.1

/-- The link of a facet is empty: a face of the link would have to be a nonempty set disjoint
from `s` that `s` could be enlarged by, contradicting maximality. -/
theorem link_facet_eq_bot {K : PreAbstractSimplicialComplex V} {s : Finset V}
    (hs : s ∈ K.facets) : K.link s = ⊥ := by
  refine le_antisymm (fun t ht => ?_) bot_le
  obtain ⟨htK, hdisj, hunion⟩ := ht
  obtain ⟨v, hv⟩ := nonempty_of_mem htK
  have hseq : s = t ∪ s := (mem_facets.mp hs).2 _ hunion Finset.subset_union_right
  have hvs : v ∈ s := by rw [hseq]; exact Finset.mem_union_left _ hv
  exact absurd hvs (Finset.disjoint_left.mp hdisj hv)

end Link

/-! ### Constructions -/

/-- The full simplex on a nonempty finite set `s`. -/
def fullSimplex {s : Finset V} (_ : s.Nonempty) : PreAbstractSimplicialComplex V where
  faces := { t | t ⊆ s ∧ t.Nonempty }
  isRelLowerSet_faces := fun {_} h => ⟨h.2, fun _ hts ht => ⟨hts.trans h.1, ht⟩⟩

end PreAbstractSimplicialComplex
