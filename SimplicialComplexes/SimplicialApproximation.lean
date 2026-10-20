import SimplicialComplexes.Star
import SimplicialComplexes.IteratedSubdivision

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

open Finset Set Geometry Metric PreAbstractSimplicialComplex

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

/-! ### Simplices of an iterated subdivision are small -/

section Small

variable [Fintype V]

/-- **Points of an open star have small image.** If `x` lies in `|sd^n K|` with a positive
coordinate at the vertex `c`, then its image is within `(1 - 1/N)^n · m` of the point placed
at `c`: the face carrying `x` contains `c`, and that face's image is small. -/
theorem dist_sdLinearIter_le_of_apply_pos {K : PreAbstractSimplicialComplex V} {m : ℝ} {N : ℕ}
    (hm : ∀ s ∈ K.faces, diam (vertexEmbed '' (↑s : Set V)) ≤ m)
    (hN : ∀ s ∈ K.faces, s.card ≤ N) (n : ℕ) (c : SdVertex K n)
    {x : SdVertex K n → ℝ} (hx : x ∈ (sdComplex K n).geometricRealization.space)
    (hc : 0 < x c) :
    dist (sdLinearIter K n x) (sdPoints K n c) ≤ (1 - (N : ℝ)⁻¹) ^ n * m := by
  have hx' := hx
  simp only [SimplicialComplex.mem_space_iff, geometricRealization_faces,
    Set.mem_image] at hx
  obtain ⟨_, ⟨t, ht, rfl⟩, hxt⟩ := hx
  have hct : c ∈ t := carrier_subset_of_mem_convexHull hxt ((mem_carrier_iff_pos hx').mpr hc)
  have h1 : sdLinearIter K n x
      ∈ sdLinearIter K n '' (convexHull ℝ (↑(faceEmbed t) : Set (SdVertex K n → ℝ))) :=
    Set.mem_image_of_mem _ hxt
  have h2 : sdPoints K n c
      ∈ sdLinearIter K n '' (convexHull ℝ (↑(faceEmbed t) : Set (SdVertex K n → ℝ))) := by
    rw [sdLinearIter_image_convexHull]
    exact subset_convexHull ℝ _ (Set.mem_image_of_mem _ (Finset.mem_coe.mpr hct))
  have hbdd : Bornology.IsBounded
      (sdLinearIter K n '' (convexHull ℝ (↑(faceEmbed t) : Set (SdVertex K n → ℝ)))) := by
    rw [sdLinearIter_image_convexHull]
    exact isBounded_convexHull.mpr (isBounded_image (sdPoints K n) t)
  exact le_trans (dist_le_diam_of_mem hbdd h1 h2) (diam_sdLinearIter_image_le hm hN n ht)

end Small

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

namespace PreAbstractSimplicialComplex

variable {V W : Type*} [DecidableEq V] [DecidableEq W]

/-! ### The simplicial approximation theorem -/

/-- **Simplicial approximation.** Every continuous map `f : |K| → |L|` admits a simplicial
approximation after finitely many barycentric subdivisions of `K`: there are `n` and a
simplicial map `g : sd^n K → L` carrying the open star of each vertex `c` into the open star
of `g c` along `f`.

The proof is the classical one. The open stars of the vertices of `L` cover `|L|`; pulling back
along `f` gives an open cover of the compact space `|K|`, with a Lebesgue number `δ`. Choose `n`
so that the simplices of `sd^n K` have image of diameter below `δ`. Then the image of the open
star of a vertex `c` sits in the `δ`-ball around the point placed at `c`, hence inside one
member `f ⁻¹' (openStar L w)` of the cover, and `g c := w` works.

`Nonempty W` is needed only to give `g` a value at vertices of `sd^n K` that are not vertices
of the complex; if `W` is empty then `L` has no faces and `|L|` is empty. -/
theorem exists_simplicialApproximation [Fintype V] [Finite W] [Nonempty W]
    {K : PreAbstractSimplicialComplex V} {L : PreAbstractSimplicialComplex W} {m : ℝ} {N : ℕ}
    (hm : ∀ s ∈ K.faces, diam (vertexEmbed '' (↑s : Set V)) ≤ m)
    (hN : ∀ s ∈ K.faces, s.card ≤ N) (hN1 : 1 ≤ N)
    (f : C(K.geometricRealization.space, L.geometricRealization.space)) :
    ∃ (n : ℕ) (g : SimplicialMap (sdComplex K n) L),
      ∀ c ∈ (sdComplex K n).vertices,
        Set.MapsTo (fun x => f (sdRealizeIterMap K n x))
          (openStar (sdComplex K n) c) (openStar L (g c)) := by
  -- the stars of `L`, pulled back along `f`, form an open cover of the compact space `|K|`
  have hopen : ∀ w : W, IsOpen (f ⁻¹' openStar L w) :=
    fun w => (isOpen_openStar w).preimage f.continuous
  have hcover : (Set.univ : Set K.geometricRealization.space) ⊆ ⋃ w : W, f ⁻¹' openStar L w := by
    intro x _
    obtain ⟨w, -, hw⟩ := exists_pos_apply (f x).2
    exact Set.mem_iUnion.mpr ⟨w, hw⟩
  obtain ⟨δ, hδ, hball⟩ := lebesgue_number_lemma_of_metric isCompact_univ hopen hcover
  -- subdivide until the simplices are smaller than the Lebesgue number
  have h1N : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hfactor : (0 : ℝ) ≤ 1 - (N : ℝ)⁻¹ := by
    have := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) h1N
    simp only [one_div, inv_one] at this
    linarith
  have hlt : 1 - (N : ℝ)⁻¹ < 1 := by
    have : (0 : ℝ) < (N : ℝ)⁻¹ := by positivity
    linarith
  obtain ⟨n, hn⟩ := exists_pow_mul_lt (m := m) hfactor hlt hδ
  refine ⟨n, ?_⟩
  -- at each vertex, the image of the star lies in one member of the cover
  have key : ∀ c : SdVertex K n, c ∈ (sdComplex K n).vertices →
      ∃ w : W, Set.MapsTo (fun x => f (sdRealizeIterMap K n x))
        (openStar (sdComplex K n) c) (openStar L w) := by
    intro c hc
    have hcmem : sdPoints K n c ∈ K.geometricRealization.space := by
      rw [← sdLinearIter_apply_vertexEmbed K n c]
      exact sdLinearIter_mem_space K n (vertexEmbed_mem_space hc)
    obtain ⟨w, hw⟩ := hball ⟨sdPoints K n c, hcmem⟩ (Set.mem_univ _)
    refine ⟨w, fun x hx => hw ?_⟩
    have hdist : dist (sdLinearIter K n x.1) (sdPoints K n c) ≤ (1 - (N : ℝ)⁻¹) ^ n * m :=
      dist_sdLinearIter_le_of_apply_pos hm hN n c x.2 hx
    rw [mem_ball, Subtype.dist_eq]
    exact lt_of_le_of_lt hdist hn
  choose! g hg using key
  exact ⟨SimplicialMap.ofStarCondition _ g hg, hg⟩

end PreAbstractSimplicialComplex
