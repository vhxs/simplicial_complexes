import Mathlib.Analysis.Convex.Hull
import SimplicialComplexes.GeometricRealization
import SimplicialComplexes.SimplicialMap

/-!
# Geometric Realization of Simplicial Maps

Given a simplicial map `f : SimplicialMap K L`, we construct the induced continuous map
between geometric realizations `|K| → |L|`.

The induced map is the restriction to `|K|` of the linear map `(V → ℝ) →ₗ[ℝ] (W → ℝ)`
that sends each standard basis vector `Pi.single v 1` to `Pi.single (f v) 1`.

## Main definitions

* `SimplicialMap.toLinearMap`: The underlying linear map on `V → ℝ`.
* `SimplicialMap.realizeMap`: The induced continuous map between geometric realizations.
-/

open Finset Set Geometry PreAbstractSimplicialComplex

set_option linter.style.openClassical false
open Classical

variable {V W X Y : Type*} [DecidableEq V] [DecidableEq W] [DecidableEq X] [DecidableEq Y]
variable {K : PreAbstractSimplicialComplex V}
variable {L : PreAbstractSimplicialComplex W}
variable {M : PreAbstractSimplicialComplex X}
variable {N : PreAbstractSimplicialComplex Y}

namespace SimplicialMap

/-! ### The underlying linear map -/

/-- The linear map `(V → ℝ) →ₗ[ℝ] (W → ℝ)` induced by a simplicial map,
defined by sending each basis vector `Pi.single v 1` to `Pi.single (f v) 1`. -/
noncomputable def toLinearMap [Fintype V] [Fintype W]
    (f : SimplicialMap K L) : (V → ℝ) →ₗ[ℝ] (W → ℝ) :=
  FunOnFinite.linearMap ℝ ℝ f

@[simp]
theorem toLinearMap_vertexEmbed [Fintype V] [Fintype W]
    (f : SimplicialMap K L) (v : V) :
    f.toLinearMap (vertexEmbed v) = vertexEmbed (f v) := by
  simp [toLinearMap, vertexEmbed, FunOnFinite.linearMap_piSingle]

theorem toLinearMap_image_faceEmbed [Fintype V] [Fintype W]
    (f : SimplicialMap K L) (s : Finset V) :
    f.toLinearMap '' ↑(faceEmbed s) = ↑(faceEmbed (s.image f)) := by
  simp only [faceEmbed, coe_image, Set.image_image, toLinearMap_vertexEmbed]

theorem toLinearMap_convexHull [Fintype V] [Fintype W]
    (f : SimplicialMap K L) (s : Finset V) :
    f.toLinearMap '' convexHull ℝ ↑(faceEmbed s) = convexHull ℝ ↑(faceEmbed (s.image f)) := by
  rw [f.toLinearMap.image_convexHull, toLinearMap_image_faceEmbed]

@[simp]
theorem id_toLinearMap [Fintype V] :
    (SimplicialMap.id K).toLinearMap = LinearMap.id := by
  unfold toLinearMap
  have h : (⇑(SimplicialMap.id K) : V → V) = _root_.id := funext id_apply
  rw [h, FunOnFinite.linearMap_id]

omit [DecidableEq V] in
@[simp]
theorem comp_toLinearMap [Fintype V] [Fintype W] [Fintype X]
    (g : SimplicialMap L M) (f : SimplicialMap K L) :
    (g.comp f).toLinearMap = g.toLinearMap.comp f.toLinearMap := by
  unfold toLinearMap
  have h : (⇑(g.comp f) : V → X) = ⇑g ∘ ⇑f := funext (fun v => comp_apply g f v)
  rw [h, FunOnFinite.linearMap_comp]

theorem toLinearMap_mem_space [Fintype V] [Fintype W]
    (f : SimplicialMap K L) {x : V → ℝ} (hx : x ∈ K.geometricRealization.space) :
    f.toLinearMap x ∈ L.geometricRealization.space := by
  simp only [SimplicialComplex.mem_space_iff, geometricRealization_faces,
             Set.mem_image] at hx ⊢
  obtain ⟨_, ⟨s, hs, rfl⟩, hxs⟩ := hx
  refine ⟨faceEmbed (s.image f), ⟨s.image f, f.map_face hs, rfl⟩, ?_⟩
  rw [← toLinearMap_convexHull]
  exact Set.mem_image_of_mem _ hxs

/-- The continuous map between geometric realizations induced by a simplicial map. -/
noncomputable def realizeMap [Fintype V] [Fintype W]
    (f : SimplicialMap K L) :
    C(K.geometricRealization.space, L.geometricRealization.space) where
  toFun := fun ⟨x, hx⟩ => ⟨f.toLinearMap x, f.toLinearMap_mem_space hx⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact f.toLinearMap.continuous_of_finiteDimensional.comp continuous_subtype_val

end SimplicialMap
