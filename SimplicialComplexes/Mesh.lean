import SimplicialComplexes.BarycentricSubdivision

/-!
# Mesh estimates for barycentric subdivision

This file proves the metric estimate underlying the simplicial approximation theorem: passing
to the barycentric subdivision shrinks simplices by a definite factor.

The key geometric fact is that the centroid of a finite set of points is close to every point
of its convex hull: if `s` has `n` points then every point of the hull is within
`(1 - 1/n) · diam` of the centroid. Since a face of `sd K` is a chain of faces of `K`, any two
of its barycenters are related this way, which is what shrinks the mesh.

The estimates are stated for an arbitrary finite configuration of points `p : W → E` in a
normed space rather than for `vertexEmbed` specifically, because iterated subdivision applies
them to configurations of iterated barycenters, which are no longer basis vectors.

## Main results

* `norm_sub_centroid_le_of_mem`: A point of the configuration is within `(1 - 1/n) · diam`
  of the centroid.
* `norm_sub_centroid_le`: The same bound throughout the convex hull, by convexity.
* `norm_centroid_sub_centroid_le`: Two centroids along a chain `s ⊆ t` are within
  `(1 - 1/#t) · diam` of each other.
* `norm_sub_barycenter_le`: The specialization to `barycenter` and `faceEmbed`.
-/

open Finset Set Geometry Metric

set_option linter.style.openClassical false
open Classical

namespace PreAbstractSimplicialComplex

/-! ### Centroids of finite point configurations -/

section Centroid

variable {W E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {p : W → E} {s t : Finset W}

/-- The centroid of the points `p v` for `v ∈ s`: their average. This is `barycenter` for a
general configuration of points in place of the standard basis vectors. -/
noncomputable def centroid (p : W → E) (s : Finset W) : E :=
  (s.card : ℝ)⁻¹ • ∑ v ∈ s, p v

theorem centroid_eq_centerMass (p : W → E) (s : Finset W) :
    centroid p s = s.centerMass (fun _ => (1 : ℝ)) p := by
  simp [centroid, Finset.centerMass, Finset.sum_const, nsmul_eq_mul]

omit [NormedSpace ℝ E] in
theorem isBounded_image (p : W → E) (s : Finset W) :
    Bornology.IsBounded (p '' (↑s : Set W)) :=
  (s.finite_toSet.image p).isBounded

/-- The centroid lies in the convex hull of the points. -/
theorem centroid_mem_convexHull (hs : s.Nonempty) :
    centroid p s ∈ convexHull ℝ (p '' (↑s : Set W)) := by
  rw [centroid_eq_centerMass]
  apply Finset.centerMass_mem_convexHull
  · intro i _; norm_num
  · simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
    exact Nat.cast_pos.mpr (Finset.card_pos.mpr hs)
  · exact fun v hv => Set.mem_image_of_mem p (Finset.mem_coe.mpr hv)

/-- A point of the configuration lies within `(1 - 1/n) · diam` of the centroid, `n = #s`.

Writing `p u - centroid p s` as the average of the `n` differences `p u - p v`, the term for
`v = u` vanishes, leaving `n - 1` terms each of norm at most the diameter. -/
theorem norm_sub_centroid_le_of_mem {u : W} (hu : u ∈ s) :
    ‖p u - centroid p s‖ ≤ (1 - (s.card : ℝ)⁻¹) * diam (p '' (↑s : Set W)) := by
  have hcard : 0 < s.card := Finset.card_pos.mpr ⟨u, hu⟩
  have hcard' : (0 : ℝ) < s.card := Nat.cast_pos.mpr hcard
  have key : p u - centroid p s = (s.card : ℝ)⁻¹ • ∑ v ∈ s, (p u - p v) := by
    rw [centroid, Finset.sum_sub_distrib, Finset.sum_const, smul_sub,
      ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, inv_mul_cancel₀ hcard'.ne', one_smul]
  have herase : ∑ v ∈ s, (p u - p v) = ∑ v ∈ s.erase u, (p u - p v) :=
    (Finset.sum_erase _ (by simp)).symm
  rw [key, herase, norm_smul, norm_inv, Real.norm_natCast]
  have hbound : ‖∑ v ∈ s.erase u, (p u - p v)‖
      ≤ (s.erase u).card • diam (p '' (↑s : Set W)) := by
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_card_nsmul _ _ _ fun v hv => ?_)
    rw [← dist_eq_norm]
    exact dist_le_diam_of_mem (isBounded_image p s)
      (Set.mem_image_of_mem p (Finset.mem_coe.mpr hu))
      (Set.mem_image_of_mem p (Finset.mem_coe.mpr (Finset.mem_of_mem_erase hv)))
  rw [Finset.card_erase_of_mem hu, nsmul_eq_mul] at hbound
  have hcast : ((s.card - 1 : ℕ) : ℝ) = (s.card : ℝ) - 1 := by
    push_cast [Nat.cast_sub hcard]
    ring
  rw [hcast] at hbound
  calc (s.card : ℝ)⁻¹ * ‖∑ v ∈ s.erase u, (p u - p v)‖
      ≤ (s.card : ℝ)⁻¹ * (((s.card : ℝ) - 1) * diam (p '' (↑s : Set W))) :=
        mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = (1 - (s.card : ℝ)⁻¹) * diam (p '' (↑s : Set W)) := by field_simp

/-- Every point of the convex hull lies within `(1 - 1/n) · diam` of the centroid: the bound
holds at each point of the configuration, and closed balls are convex. -/
theorem norm_sub_centroid_le {q : E} (hq : q ∈ convexHull ℝ (p '' (↑s : Set W))) :
    ‖q - centroid p s‖ ≤ (1 - (s.card : ℝ)⁻¹) * diam (p '' (↑s : Set W)) := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp only [Finset.coe_empty, Set.image_empty, convexHull_empty] at hq
    exact absurd hq (Set.notMem_empty q)
  · have hsub : p '' (↑s : Set W)
        ⊆ closedBall (centroid p s) ((1 - (s.card : ℝ)⁻¹) * diam (p '' (↑s : Set W))) := by
      rintro _ ⟨v, hv, rfl⟩
      rw [mem_closedBall, dist_eq_norm]
      exact norm_sub_centroid_le_of_mem (Finset.mem_coe.mp hv)
    have := convexHull_min hsub (convex_closedBall _ _) hq
    rwa [mem_closedBall, dist_eq_norm] at this

/-- Along a chain `s ⊆ t`, the two centroids are within `(1 - 1/#t) · diam` of each other.
This is the estimate that shrinks the mesh under subdivision. -/
theorem norm_centroid_sub_centroid_le (hst : s ⊆ t) (hs : s.Nonempty) :
    ‖centroid p s - centroid p t‖ ≤ (1 - (t.card : ℝ)⁻¹) * diam (p '' (↑t : Set W)) := by
  refine norm_sub_centroid_le (convexHull_mono ?_ (centroid_mem_convexHull hs))
  exact Set.image_mono (Finset.coe_subset.mpr hst)

end Centroid

/-! ### Specialization to the vertex embedding -/

variable {V : Type*} [DecidableEq V] [Fintype V]

theorem barycenter_eq_centroid (s : Finset V) : barycenter s = centroid vertexEmbed s := rfl

/-- A vertex of `s` lies within `(1 - 1/n) · diam s` of the barycenter, where `n = #s`. -/
theorem norm_vertexEmbed_sub_barycenter_le {s : Finset V} {u : V} (hu : u ∈ s) :
    ‖vertexEmbed u - barycenter s‖
      ≤ (1 - (s.card : ℝ)⁻¹) * diam (↑(faceEmbed s) : Set (V → ℝ)) := by
  rw [barycenter_eq_centroid, coe_faceEmbed]
  exact norm_sub_centroid_le_of_mem hu

/-- Every point of a simplex lies within `(1 - 1/n) · diam` of its barycenter. -/
theorem norm_sub_barycenter_le {s : Finset V} {q : V → ℝ}
    (hq : q ∈ convexHull ℝ (↑(faceEmbed s) : Set (V → ℝ))) :
    ‖q - barycenter s‖ ≤ (1 - (s.card : ℝ)⁻¹) * diam (↑(faceEmbed s) : Set (V → ℝ)) := by
  rw [coe_faceEmbed] at hq
  rw [barycenter_eq_centroid, coe_faceEmbed]
  exact norm_sub_centroid_le hq

end PreAbstractSimplicialComplex
