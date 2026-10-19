import SimplicialComplexes.Star
import SimplicialComplexes.BarycentricSubdivision

/-!
# Towards the simplicial approximation theorem

This file collects the results that turn a continuous map `|K| → |L|` into a simplicial map,
starting with the combinatorial core: a vertex map that respects open stars is simplicial.

Given `F : |K| → |L|` and a vertex map `g : V → W`, say that `g` satisfies the *star condition*
for `F` if `F` carries the open star of each vertex `v` into the open star of `g v`. The main
result here is that such a `g` sends faces to faces, so it is a simplicial map. The proof feeds
the barycenter of a face `s` through `F`: its carrier is a face of `L` containing `g v` for
every `v ∈ s`, so the image of `s` is a face by downward closure.

## Main results

* `carrier_barycenter`: The carrier of the barycenter of `s` is `s`.
* `image_mem_faces_of_mapsTo_openStar`: The star condition implies faces map to faces.
* `SimplicialMap.ofStarCondition`: The simplicial map determined by such a vertex map.
-/

open Finset Set Geometry PreAbstractSimplicialComplex

set_option linter.style.openClassical false
open Classical

namespace PreAbstractSimplicialComplex

variable {V W : Type*} [DecidableEq V] [DecidableEq W]
variable {K : PreAbstractSimplicialComplex V} {L : PreAbstractSimplicialComplex W}

/-! ### The barycenter and its carrier -/

/-- The barycenter of `s` has coordinate `(s.card)⁻¹` exactly on `s`, so its carrier is `s`. -/
theorem carrier_barycenter [Fintype V] {s : Finset V} : carrier (barycenter s) = s := by
  ext v
  rw [mem_carrier_iff, barycenter_apply]
  split_ifs with hv
  · have hcard : (s.card : ℝ) ≠ 0 := (Nat.cast_pos.mpr (Finset.card_pos.mpr ⟨v, hv⟩)).ne'
    simp [hv, hcard]
  · simp [hv]

/-! ### The star condition -/

/-- **Star condition.** If `F : |K| → |L|` carries the open star of every vertex `v` into the
open star of `g v`, then `g` sends faces of `K` to faces of `L`.

The barycenter of a face `s` lies in the open star of each of its vertices, so its image under
`F` lies in the open star of each `g v`; that is, every `g v` belongs to the carrier of the
image point, which is a face of `L`. -/
theorem image_mem_faces_of_mapsTo_openStar [Finite V] [Finite W]
    {F : K.geometricRealization.space → L.geometricRealization.space} {g : V → W}
    (hg : ∀ v ∈ K.vertices, Set.MapsTo F (openStar K v) (openStar L (g v)))
    {s : Finset V} (hs : s ∈ K.faces) : s.image g ∈ L.faces := by
  have : Fintype V := Fintype.ofFinite V
  have : Fintype W := Fintype.ofFinite W
  have hsne : s.Nonempty := nonempty_of_mem hs
  set b : K.geometricRealization.space := ⟨barycenter s, barycenter_mem_space hs⟩ with hb
  have hcarrier : ∀ v ∈ s, g v ∈ carrier ((F b : W → ℝ)) := by
    intro v hv
    have hbv : b ∈ openStar K v := by
      rw [mem_openStar_iff_mem_carrier]
      show v ∈ carrier (barycenter s)
      rw [carrier_barycenter]
      exact hv
    exact mem_openStar_iff_mem_carrier.mp (hg v (mem_vertices_of_mem hs hv) hbv)
  refine down_closed (carrier_mem_faces (F b).2) ?_ (hsne.image g)
  intro w hw
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
  exact hcarrier v hv

end PreAbstractSimplicialComplex

namespace SimplicialMap

variable {V W : Type*} [DecidableEq V] [DecidableEq W]
variable {K : PreAbstractSimplicialComplex V} {L : PreAbstractSimplicialComplex W}

/-- The simplicial map determined by a vertex map satisfying the star condition for `F`. -/
def ofStarCondition [Finite V] [Finite W]
    (F : K.geometricRealization.space → L.geometricRealization.space) (g : V → W)
    (hg : ∀ v ∈ K.vertices, Set.MapsTo F (openStar K v) (openStar L (g v))) :
    SimplicialMap K L where
  toFun := g
  map_face hs := image_mem_faces_of_mapsTo_openStar hg hs

@[simp]
theorem ofStarCondition_apply [Finite V] [Finite W]
    (F : K.geometricRealization.space → L.geometricRealization.space) (g : V → W)
    (hg : ∀ v ∈ K.vertices, Set.MapsTo F (openStar K v) (openStar L (g v))) (v : V) :
    ofStarCondition F g hg v = g v := rfl

end SimplicialMap
