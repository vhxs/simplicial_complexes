import Mathlib
import SimplicialComplexes.Basic

/-!
# Geometric Realization of Combinatorial Simplicial Complexes

This file constructs the geometric realization of a combinatorial simplicial complex
as a `Geometry.SimplicialComplex ℝ (V → ℝ)` in the sense of Mathlib.

Given a combinatorial simplicial complex `K` on vertex type `V`, we embed each
vertex `v : V` as the standard basis vector `Pi.single v 1 : V → ℝ`, and each
combinatorial face as the corresponding finite set of basis vectors.

## Main definitions

* `vertexEmbed`: Embeds vertices as standard basis vectors in `V → ℝ`.
* `faceEmbed`: Maps combinatorial faces to finite sets of basis vectors.
* `geometricRealization`: The geometric realization as a `Geometry.SimplicialComplex`.

## Main results

* `vertexEmbed_injective`: The vertex embedding is injective.
* `faceEmbed_inter`: The face embedding commutes with intersection.
-/

open Finset Set Geometry

namespace PreAbstractSimplicialComplex

-- Classical decidability is needed for Finset operations on (V → ℝ),
-- since ℝ does not have computable decidable equality.
set_option linter.style.openClassical false
open Classical

variable {V : Type*} [DecidableEq V]

/-! ### The vertex embedding -/

/-- Embed vertex `v` as the standard basis vector `Pi.single v 1 : V → ℝ`. -/
def vertexEmbed (v : V) : V → ℝ := Pi.single v 1

theorem vertexEmbed_apply_same (v : V) : vertexEmbed v v = 1 :=
  Pi.single_eq_same v 1

theorem vertexEmbed_apply_of_ne {v w : V} (h : v ≠ w) : vertexEmbed v w = 0 := by
  unfold vertexEmbed; exact Pi.single_eq_of_ne (Ne.symm h) 1

theorem vertexEmbed_injective : Function.Injective (vertexEmbed (V := V)) := by
  intro v w h
  by_contra hne
  have : (1 : ℝ) = 0 := by
    have := congr_fun h v
    rw [vertexEmbed_apply_same, vertexEmbed_apply_of_ne (Ne.symm hne)] at this
    exact this
  exact one_ne_zero this

/-! ### The face embedding -/

/-- Map a combinatorial face `s` to the finite set of standard basis vectors for its vertices. -/
noncomputable def faceEmbed (s : Finset V) : Finset (V → ℝ) := s.image vertexEmbed

theorem faceEmbed_nonempty {s : Finset V} (hs : s.Nonempty) : (faceEmbed s).Nonempty := by
  exact Finset.Nonempty.image hs vertexEmbed

theorem faceEmbed_mono {s t : Finset V} (h : s ⊆ t) : faceEmbed s ⊆ faceEmbed t := by
  exact Finset.image_subset_image h

theorem faceEmbed_injective : Function.Injective (faceEmbed (V := V)) := by
  intro s t h
  simp only [faceEmbed] at h
  exact Finset.image_injective vertexEmbed_injective h

/-- The face embedding commutes with intersection. -/
theorem faceEmbed_inter (s t : Finset V) :
    faceEmbed (s ∩ t) = faceEmbed s ∩ faceEmbed t := by
  simp only [faceEmbed, Finset.image_inter _ _ vertexEmbed_injective]

/-! ### Affine independence of embedded faces -/

/-- For distinct vertices, the differences `Pi.single v 1 - Pi.single v₀ 1` (for `v ∈ s, v ≠ v₀`)
are linearly independent. The proof evaluates a hypothetical linear combination at coordinate `v`
to force each coefficient to zero. -/
private lemma linearIndependent_vertexEmbed_sub {s : Finset V} {v₀ : V} :
    LinearIndependent ℝ (fun i : {v : ↑s // v.1 ≠ v₀} =>
        vertexEmbed i.1.1 - vertexEmbed v₀) := by
  rw [linearIndependent_iff']
  intro t g htg i hi
  -- Evaluate at ↑↑i; only the i term survives.
  have key := congr_fun htg i.1.1
  simp only [Pi.zero_apply, Finset.sum_apply, Pi.smul_apply, Pi.sub_apply,
             smul_eq_mul, vertexEmbed, Pi.single_apply] at key
  -- Eliminate the v₀ subtraction term
  have hv_ne' : ↑↑i ≠ v₀ := i.2
  simp only [ite_eq_right hv_ne', sub_zero] at key
  -- key : ∑ j ∈ t, g j * (if ↑↑i = ↑↑j then 1 else 0) = 0
  -- Reduce the sum to the single i term.
  have sum_eq := Finset.sum_eq_single_of_mem i hi
    (f := fun (x : {v : ↑s // v.1 ≠ v₀}) => g x * if (↑↑i : V) = (↑↑x : V) then (1:ℝ) else 0)
    (fun j _ hjne => by
      simp [show (↑↑i : V) ≠ (↑↑j : V) from
        fun h => hjne (Subtype.ext (Subtype.ext h)).symm])
  simp only [ite_true, mul_one] at sum_eq
  linarith

/-- The standard basis vectors `{Pi.single v 1 | v ∈ s}` form an affinely independent family.

**Proof sketch**: By `affineIndependent_iff_linearIndependent_vsub`, fixing a base vertex `v₀ ∈ s`,
it suffices to show `{(Pi.single v 1 - Pi.single v₀ 1) | v ∈ s, v ≠ v₀}` is linearly
independent. Each such vector is 1 at coordinate `v`, -1 at `v₀`, and 0 elsewhere.
Examining the `v`-th coordinate forces each coefficient to zero. -/
theorem affineIndependent_faceEmbed {s : Finset V} :
    AffineIndependent ℝ ((↑) : (faceEmbed s) → (V → ℝ)) := by
  rcases s.eq_empty_or_nonempty with rfl | ⟨v₀, hv₀⟩
  · -- faceEmbed ∅ = ∅; the index type is empty so the statement holds vacuously.
    simp only [faceEmbed, Finset.image_empty]
    intro _ _ _ _ i
    exact absurd i.2 (Finset.notMem_empty _)
  · -- Pick b₀ = vertexEmbed v₀ as the base point.
    have hb₀ : vertexEmbed v₀ ∈ faceEmbed s := Finset.mem_image_of_mem _ hv₀
    let b₀ : ↑(faceEmbed s) := ⟨vertexEmbed v₀, hb₀⟩
    apply (affineIndependent_iff_linearIndependent_vsub ℝ _ b₀).mpr
    -- In the module V → ℝ, vsub is pointwise subtraction.
    simp only [vsub_eq_sub]
    rw [linearIndependent_iff']
    -- Take an arbitrary finset t of indices and coefficients g summing to zero;
    -- show the coefficient at any element ⟨⟨vertexEmbed v, _⟩, _⟩ is zero.
    rintro t g htg ⟨⟨x, hx_mem⟩, hx_ne⟩ hi
    -- Extract the vertex v with x = vertexEmbed v
    simp only [faceEmbed, Finset.mem_image] at hx_mem
    obtain ⟨v, hv_mem, rfl⟩ := hx_mem
    -- x ≠ b₀ implies v ≠ v₀
    have hv_ne : v ≠ v₀ := fun h => hx_ne (Subtype.ext (congrArg vertexEmbed h))
    -- Evaluate at coordinate v: only the term for vertex v contributes
    have hb₀_val : (↑b₀ : V → ℝ) = vertexEmbed v₀ := rfl
    have key := congr_fun htg v
    simp only [Pi.zero_apply, Finset.sum_apply, Pi.smul_apply, Pi.sub_apply,
               smul_eq_mul, hb₀_val, vertexEmbed, Pi.single_apply] at key
    simp only [ite_eq_right hv_ne, sub_zero] at key
    -- key : ∑ i ∈ t, g i * (↑↑i : V → ℝ) v = 0
    -- Reduce the sum: for j ≠ ⟨⟨vertexEmbed v, _⟩, _⟩, the vector (↑↑j : V → ℝ)
    -- is vertexEmbed w for w ≠ v, so (↑↑j : V → ℝ) v = Pi.single w 1 v = 0.
    set a : {x : ↥(faceEmbed s) // x ≠ b₀} := ⟨⟨vertexEmbed v, hx_mem⟩, hx_ne⟩
    have hav : (↑↑a : V → ℝ) v = 1 := by
      change vertexEmbed v v = 1; simp [vertexEmbed]
    have sum_eq := Finset.sum_eq_single_of_mem a hi
      (f := fun x => g x * (↑↑x : V → ℝ) v)
      (fun j _ hjne => by
        obtain ⟨⟨y, hy_mem⟩, _⟩ := j
        simp only [faceEmbed, Finset.mem_image] at hy_mem
        obtain ⟨w, _, rfl⟩ := hy_mem
        have hwv : w ≠ v := fun h =>
          hjne (Subtype.ext (Subtype.ext (congrArg vertexEmbed h)))
        simp [vertexEmbed, hwv])
    simp only [sum_eq, hav, mul_one] at key
    exact key

/-! ### The geometric realization functor -/

/-- The geometric realization of a combinatorial simplicial complex `K` on vertex type `V`
as a `Geometry.SimplicialComplex ℝ (V → ℝ)`.

Each vertex `v : V` is realized as `Pi.single v 1 : V → ℝ`, and each face is realized
as the convex hull of the corresponding standard basis vectors. -/
noncomputable def geometricRealization (K : PreAbstractSimplicialComplex V) :
    Geometry.SimplicialComplex ℝ (V → ℝ) where
  faces := faceEmbed '' K.faces
  indep := by
    intro s hs
    simp only [Set.mem_image] at hs
    obtain ⟨s', _, rfl⟩ := hs
    exact affineIndependent_faceEmbed
  isRelLowerSet_faces := by
    intro s hs
    simp only [Set.mem_image] at hs
    obtain ⟨s', hs'_mem, rfl⟩ := hs
    refine ⟨faceEmbed_nonempty (K.nonempty_of_mem hs'_mem), ?_⟩
    intro u hus hu
    -- u ⊆ faceEmbed s': use subset_image_iff to find t' ⊆ s' with t'.image vertexEmbed = u
    simp only [faceEmbed] at hus
    rw [Finset.subset_image_iff] at hus
    obtain ⟨t', ht'_sub, rfl⟩ := hus
    have ht'_ne : t'.Nonempty := by
      simp only [Finset.image_nonempty] at hu; exact hu
    exact ⟨t', K.down_closed hs'_mem ht'_sub ht'_ne, rfl⟩
  inter_subset_convexHull := by
    -- For standard simplices, the intersection of convex hulls equals the convex hull of
    -- the vertex intersection:
    --   convexHull ℝ {e_v | v ∈ s'} ∩ convexHull ℝ {e_v | v ∈ t'}
    --   = convexHull ℝ {e_v | v ∈ s' ∩ t'}
    -- A point x is in convexHull {e_v | v ∈ s'} iff x is a probability distribution supported
    -- on s' (xᵥ ≥ 0, xᵥ = 0 for v ∉ s', ∑_{v ∈ s'} xᵥ = 1). The intersection forces support
    -- on s' ∩ t', i.e., exactly convexHull ↑(faceEmbed (s' ∩ t')).
    intro s t hs ht
    simp only [Set.mem_image] at hs ht
    obtain ⟨s', _, rfl⟩ := hs
    obtain ⟨t', _, rfl⟩ := ht
    have hunion : faceEmbed s' ∪ faceEmbed t' = faceEmbed (s' ∪ t') := by
      simp only [faceEmbed, Finset.image_union]
    have hind : AffineIndependent ℝ ((↑) : ↑(faceEmbed s' ∪ faceEmbed t') → (V → ℝ)) := by
      rw [hunion]; exact affineIndependent_faceEmbed
    exact (AffineIndependent.convexHull_inter' hind).ge

@[simp]
theorem geometricRealization_faces (K : PreAbstractSimplicialComplex V) :
    K.geometricRealization.faces = faceEmbed '' K.faces :=
  rfl

end PreAbstractSimplicialComplex
