import Mathlib.Analysis.Convex.Hull
import Mathlib.Topology.Order.Basic
import SimplicialComplexes.GeometricRealization
import SimplicialComplexes.GeometricRealizeMap

/-!
# Stars in Simplicial Complexes

This file defines the open star of a vertex in a combinatorial simplicial complex
and proves its basic properties.

The open star of a vertex `v` in `K` is the set of points in the geometric realization
whose barycentric coordinate at `v` is strictly positive:

  `openStar K v = {x ∈ |K| | x v > 0}`

It also defines the carrier of a point — the face spanned by the vertices where its
coordinates are nonzero — which is the combinatorial counterpart of the open star.

## Main definitions

* `PreAbstractSimplicialComplex.openStar`: The open star of a vertex.
* `PreAbstractSimplicialComplex.carrier`: The carrier of a point of `|K|`.

## Main results

* `isOpen_openStar`: The open star is open in the subspace topology on `|K|`.
* `mem_space_apply_nonneg`: Points in `|K|` have non-negative coordinates.
* `iUnion_openStar`: The open stars of all vertices cover `|K|`.
* `carrier_mem_faces`: The carrier of a point of `|K|` is a face of `K`.
* `mem_openStar_iff_mem_carrier`: `x ∈ openStar K v` exactly when `v` lies in the carrier of `x`.
* `SimplicialMap.mapsTo_openStar`: Simplicial maps send open stars to open stars.
-/

open Finset Set Geometry PreAbstractSimplicialComplex

set_option linter.style.openClassical false
open Classical

namespace PreAbstractSimplicialComplex

variable {V : Type*} [DecidableEq V] {K : PreAbstractSimplicialComplex V}

/-! ### Definition -/

/-- The open star of vertex `v` in `K`: the set of points in the geometric realization
whose barycentric coordinate at `v` is strictly positive. -/
def openStar (K : PreAbstractSimplicialComplex V) (v : V) :
    Set K.geometricRealization.space :=
  {x | 0 < (x : V → ℝ) v}

@[simp]
theorem mem_openStar_iff {v : V} {x : K.geometricRealization.space} :
    x ∈ openStar K v ↔ 0 < (x : V → ℝ) v :=
  Iff.rfl

/-! ### Openness -/

/-- The open star is open in the subspace topology on `|K|`. -/
theorem isOpen_openStar (v : V) : IsOpen (openStar K v) :=
  isOpen_Ioi.preimage ((continuous_apply v).comp continuous_subtype_val)

/-! ### Non-negativity of coordinates -/

/-- Every point in the geometric realization has non-negative coordinates. -/
theorem mem_space_apply_nonneg {x : V → ℝ} (hx : x ∈ K.geometricRealization.space) (v : V) :
    0 ≤ x v := by
  simp only [SimplicialComplex.mem_space_iff, geometricRealization_faces,
             Set.mem_image] at hx
  obtain ⟨_, ⟨s, _, rfl⟩, hxs⟩ := hx
  apply convexHull_min _ (convex_Ici 0) hxs v
  intro y hy
  simp only [faceEmbed, Finset.coe_image, Set.mem_image] at hy
  obtain ⟨w, _, rfl⟩ := hy
  simp [vertexEmbed]

/-! ### Open stars cover the space -/

/-- Every point of `|K|` has a strictly positive coordinate, at a vertex of `K`. -/
theorem exists_pos_apply {x : V → ℝ} (hx : x ∈ K.geometricRealization.space) :
    ∃ v ∈ K.vertices, 0 < x v := by
  simp only [SimplicialComplex.mem_space_iff, geometricRealization_faces,
             Set.mem_image] at hx
  obtain ⟨_, ⟨s, hs, rfl⟩, hxs⟩ := hx
  -- x is a convex combination of {e_v | v ∈ s}; some coefficient must be positive
  rw [Finset.mem_convexHull'] at hxs
  obtain ⟨w, hw_nn, hw_sum, hw_eq⟩ := hxs
  -- some w is positive since they sum to 1
  have ⟨e, he_mem, he_pos⟩ : ∃ e ∈ faceEmbed s, 0 < w e := by
    by_contra h
    push Not at h
    have : ∑ e ∈ faceEmbed s, w e = 0 :=
      Finset.sum_eq_zero (fun e he => le_antisymm (h e he) (hw_nn e he))
    linarith [hw_sum]
  -- extract the vertex v from e = vertexEmbed v
  simp only [faceEmbed, Finset.mem_image] at he_mem
  obtain ⟨v, hv_mem, rfl⟩ := he_mem
  refine ⟨v, mem_vertices_of_mem hs hv_mem, ?_⟩
  -- x v = (∑ e, w e • e) v ≥ w (vertexEmbed v) * 1 > 0
  have hxv : x v = ∑ e ∈ faceEmbed s, w e * e v := by
    conv_lhs => rw [← hw_eq]
    simp [Finset.sum_apply, smul_eq_mul]
  have hterm_nn : ∀ e ∈ faceEmbed s, 0 ≤ w e * e v := fun e he => by
    apply mul_nonneg (hw_nn e he)
    simp only [faceEmbed, Finset.mem_image] at he
    obtain ⟨u, _, rfl⟩ := he
    simp only [vertexEmbed, Pi.single_apply]
    split_ifs <;> norm_num
  rw [hxv]
  calc 0 < w (vertexEmbed v) * vertexEmbed v v := by
          rw [vertexEmbed_apply_same]; linarith
    _ ≤ ∑ e ∈ faceEmbed s, w e * e v :=
          Finset.single_le_sum (f := fun e : V → ℝ => w e * e v)
            hterm_nn (Finset.mem_image_of_mem _ hv_mem)

/-- The open stars of the vertices cover `|K|`. -/
theorem iUnion_openStar :
    ⋃ v ∈ K.vertices, openStar K v = Set.univ := by
  ext ⟨x, hx⟩
  simp only [Set.mem_iUnion, Set.mem_univ, iff_true, mem_openStar_iff]
  obtain ⟨v, hv, hpos⟩ := exists_pos_apply hx
  exact ⟨v, hv, hpos⟩

/-! ### Carriers -/

section Carrier

variable [Fintype V]

/-- The carrier of a point: the finset of vertices at which its coordinates are nonzero.
For a point of `|K|` this is the smallest face whose realization contains it. -/
noncomputable def carrier (x : V → ℝ) : Finset V :=
  Finset.univ.filter fun v => x v ≠ 0

omit [DecidableEq V] in
@[simp]
theorem mem_carrier_iff {x : V → ℝ} {v : V} : v ∈ carrier x ↔ x v ≠ 0 := by
  simp [carrier]

/-- Coordinates on `|K|` are nonnegative, so the carrier collects the strictly positive ones. -/
theorem mem_carrier_iff_pos {x : V → ℝ} (hx : x ∈ K.geometricRealization.space) {v : V} :
    v ∈ carrier x ↔ 0 < x v := by
  rw [mem_carrier_iff]
  exact ⟨fun h => (mem_space_apply_nonneg hx v).lt_of_ne (Ne.symm h), fun h => h.ne'⟩

/-- A point of `convexHull ℝ ↑(faceEmbed s)` is supported on `s`. -/
theorem carrier_subset_of_mem_convexHull {s : Finset V} {x : V → ℝ}
    (hx : x ∈ convexHull ℝ (↑(faceEmbed s) : Set (V → ℝ))) : carrier x ⊆ s := by
  obtain ⟨w, -, -, rfl⟩ := exists_weights_of_mem_convexHull_faceEmbed hx
  intro v hv
  rw [mem_carrier_iff] at hv
  by_contra hvs
  refine hv ?_
  rw [Finset.sum_apply]
  refine Finset.sum_eq_zero fun u hu => ?_
  have hne : u ≠ v := fun h => hvs (h ▸ hu)
  simp [vertexEmbed_apply_of_ne hne]

theorem carrier_nonempty {x : V → ℝ} (hx : x ∈ K.geometricRealization.space) :
    (carrier x).Nonempty := by
  obtain ⟨v, -, hv⟩ := exists_pos_apply hx
  exact ⟨v, (mem_carrier_iff_pos hx).mpr hv⟩

/-- The carrier of a point of `|K|` is a face of `K`. -/
theorem carrier_mem_faces {x : V → ℝ} (hx : x ∈ K.geometricRealization.space) :
    carrier x ∈ K.faces := by
  have hx' := hx
  simp only [SimplicialComplex.mem_space_iff, geometricRealization_faces,
             Set.mem_image] at hx
  obtain ⟨_, ⟨s, hs, rfl⟩, hxs⟩ := hx
  exact down_closed hs (carrier_subset_of_mem_convexHull hxs) (carrier_nonempty hx')

/-- A point lies in the open star of `v` exactly when `v` belongs to its carrier. -/
theorem mem_openStar_iff_mem_carrier {v : V} {x : K.geometricRealization.space} :
    x ∈ openStar K v ↔ v ∈ carrier (x : V → ℝ) :=
  (mem_carrier_iff_pos x.2).symm

end Carrier

end PreAbstractSimplicialComplex

namespace SimplicialMap

variable {W : Type*} [DecidableEq W] {L : PreAbstractSimplicialComplex W}

/-- A simplicial map sends the open star of `v` into the open star of `f v`. -/
theorem mapsTo_openStar [Fintype V] [Fintype W]
    (f : SimplicialMap K L) (v : V) :
    Set.MapsTo f.realizeMap (openStar K v) (openStar L (f v)) := by
  intro ⟨x, hx⟩ hxv
  simp only [mem_openStar_iff] at hxv ⊢
  change 0 < f.toLinearMap x (f v)
  simp only [toLinearMap]
  rw [FunOnFinite.linearMap_apply_apply]
  exact lt_of_lt_of_le hxv
    (Finset.single_le_sum (f := x)
      (fun u _ => mem_space_apply_nonneg hx u)
      (Finset.mem_filter.mpr ⟨Finset.mem_univ v, rfl⟩))

end SimplicialMap
