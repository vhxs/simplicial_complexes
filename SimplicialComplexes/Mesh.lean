/-
Copyright (c) 2026 Vikram Saraph. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vikram Saraph
-/
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

/-! ### One step of subdivision -/

section Subdivision

variable {W : Type*} [DecidableEq W] {C : PreAbstractSimplicialComplex W}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [DecidableEq W] in
/-- Distinct faces in a chain have distinct cardinalities, so a bound on the number of vertices
of a face of `C` bounds the number of vertices of a face of `sd C`. Dimension is preserved. -/
theorem card_le_of_mem_barySubdivision {N : ℕ} (hN : ∀ s ∈ C.faces, s.card ≤ N)
    {t : Finset (FaceVertex C)} (ht : t ∈ (barySubdivision C).faces) : t.card ≤ N := by
  have hmaps : Set.MapsTo (fun c : FaceVertex C => c.1.card) ↑t ↑(Finset.Icc 1 N) := by
    intro c _
    simp only [Finset.coe_Icc, Set.mem_Icc]
    exact ⟨Finset.card_pos.mpr (nonempty_of_mem c.2), hN c.1 c.2⟩
  have hinj : Set.InjOn (fun c : FaceVertex C => c.1.card) ↑t := by
    intro c hc c' hc' hcard
    by_contra hne
    rcases ht.2 hc hc' hne with h | h
    · exact hne (Subtype.ext (Finset.eq_of_subset_of_card_le h hcard.ge))
    · exact hne (Subtype.ext (Finset.eq_of_subset_of_card_le h hcard.le).symm)
  calc t.card ≤ (Finset.Icc 1 N).card := Finset.card_le_card_of_injOn _ hmaps hinj
    _ = N := by simp

omit [DecidableEq W] in
/-- **One step of subdivision shrinks diameters.** If every face of `C` spans a set of diameter
at most `m` and has at most `N` vertices, then every face of `sd C` — a chain of faces of `C` —
spans barycenters of diameter at most `(1 - 1/N) · m`. -/
theorem diam_image_centroid_le {p : W → E} {m : ℝ} {N : ℕ}
    (hm : ∀ s ∈ C.faces, diam (p '' (↑s : Set W)) ≤ m)
    (hN : ∀ s ∈ C.faces, s.card ≤ N)
    {t : Finset (FaceVertex C)} (ht : t ∈ (barySubdivision C).faces) :
    diam ((fun c : FaceVertex C => centroid p c.1) '' (↑t : Set (FaceVertex C)))
      ≤ (1 - (N : ℝ)⁻¹) * m := by
  obtain ⟨c₀, hc₀⟩ := ht.1
  have hm0 : 0 ≤ m := le_trans diam_nonneg (hm c₀.1 c₀.2)
  have hN1 : 1 ≤ N := le_trans (Finset.card_pos.mpr (nonempty_of_mem c₀.2)) (hN c₀.1 c₀.2)
  have h1N : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hfactor : (0 : ℝ) ≤ 1 - (N : ℝ)⁻¹ := by
    have := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) h1N
    simp only [one_div, inv_one] at this
    linarith
  have key : ∀ a b : FaceVertex C, a.1 ⊆ b.1 →
      ‖centroid p a.1 - centroid p b.1‖ ≤ (1 - (N : ℝ)⁻¹) * m := by
    intro a b hab
    refine le_trans (norm_centroid_sub_centroid_le hab (nonempty_of_mem a.2)) ?_
    have hb1 : (0 : ℝ) < b.1.card := by
      exact_mod_cast Finset.card_pos.mpr (nonempty_of_mem b.2)
    have hcardle : ((N : ℝ))⁻¹ ≤ ((b.1.card : ℝ))⁻¹ := by
      rw [← one_div, ← one_div]
      exact one_div_le_one_div_of_le hb1 (by exact_mod_cast hN b.1 b.2)
    exact mul_le_mul (by linarith) (hm b.1 b.2) diam_nonneg hfactor
  refine diam_le_of_forall_dist_le (mul_nonneg hfactor hm0) ?_
  rintro _ ⟨c, hc, rfl⟩ _ ⟨c', hc', rfl⟩
  rw [dist_eq_norm]
  rcases eq_or_ne c c' with rfl | hne
  · simpa using mul_nonneg hfactor hm0
  · rcases ht.2 hc hc' hne with h | h
    · exact key c c' h
    · rw [← norm_neg, neg_sub]
      exact key c' c h

end Subdivision

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
