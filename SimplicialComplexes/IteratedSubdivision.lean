import SimplicialComplexes.Mesh

/-!
# Iterated barycentric subdivision

Each barycentric subdivision changes the vertex type — the vertices of `sd K` are the faces of
`K` — so the `n`-th subdivision is defined by recursion carrying its vertex type along, as a
`Σ W, PreAbstractSimplicialComplex W`.

Alongside the complex we carry the placement of its vertices in `V → ℝ`: a vertex of `sd^(n+1) K`
is a face of `sd^n K`, placed at the centroid of the points of that face. The mesh estimate of
`Mesh.lean` then shrinks diameters by a factor `1 - 1/N` at each step, where `N` bounds the
number of vertices of a face, so after `n` steps every face spans a set of diameter at most
`(1 - 1/N)^n · m`. Since that tends to zero, subdivisions eventually refine any given scale.

## Main definitions

* `SdVertex K n`, `sdComplex K n`: The vertex type and the complex `sd^n K`.
* `sdPoints K n`: The placement of those vertices in `V → ℝ` as iterated barycenters.

## Main results

* `card_le_sdComplex`: Subdivision preserves the bound on the number of vertices of a face.
* `diam_sdPoints_le`: After `n` subdivisions every face spans a set of diameter
  at most `(1 - 1/N)^n · m`.
* `exists_diam_sdPoints_lt`: Hence faces eventually span sets of diameter below any `ε > 0`.
-/

open Finset Set Geometry Metric

set_option linter.style.openClassical false
open Classical

universe u

namespace PreAbstractSimplicialComplex

variable {V : Type u} [DecidableEq V] [Fintype V]

/-! ### The iterated subdivision -/

/-- The `n`-th barycentric subdivision of `K`, carrying its vertex type along: the vertices of
each subdivision are the faces of the previous one. -/
def sdIter (K : PreAbstractSimplicialComplex V) :
    ℕ → Σ W : Type u, PreAbstractSimplicialComplex W
  | 0 => ⟨V, K⟩
  | n + 1 => ⟨FaceVertex (sdIter K n).2, barySubdivision (sdIter K n).2⟩

/-- The vertex type of `sd^n K`. -/
abbrev SdVertex (K : PreAbstractSimplicialComplex V) (n : ℕ) : Type u := (sdIter K n).1

/-- The complex `sd^n K`. -/
abbrev sdComplex (K : PreAbstractSimplicialComplex V) (n : ℕ) :
    PreAbstractSimplicialComplex (SdVertex K n) := (sdIter K n).2

omit [DecidableEq V] [Fintype V] in
@[simp]
theorem sdComplex_zero (K : PreAbstractSimplicialComplex V) : sdComplex K 0 = K := rfl

omit [DecidableEq V] [Fintype V] in
@[simp]
theorem sdComplex_succ (K : PreAbstractSimplicialComplex V) (n : ℕ) :
    sdComplex K (n + 1) = barySubdivision (sdComplex K n) := rfl

/-- The placement of the vertices of `sd^n K` in `V → ℝ`: a vertex of `sd^(n+1) K` is a face of
`sd^n K`, and sits at the centroid of the points of that face. -/
noncomputable def sdPoints (K : PreAbstractSimplicialComplex V) :
    (n : ℕ) → SdVertex K n → (V → ℝ)
  | 0 => (vertexEmbed : V → (V → ℝ))
  | n + 1 => fun c => centroid (sdPoints K n) c.1

@[simp]
theorem sdPoints_zero (K : PreAbstractSimplicialComplex V) :
    sdPoints K 0 = (vertexEmbed : V → (V → ℝ)) := rfl

@[simp]
theorem sdPoints_succ (K : PreAbstractSimplicialComplex V) (n : ℕ)
    (c : SdVertex K (n + 1)) : sdPoints K (n + 1) c = centroid (sdPoints K n) c.1 := rfl

/-! ### Instances for the iterated vertex types -/

/-- Vertices of `sd^n K` have decidable equality: at each step they are faces of the previous
complex, i.e. a subtype of `Finset` of the previous vertex type. -/
instance instDecidableEqSdVertex (K : PreAbstractSimplicialComplex V) :
    ∀ n, DecidableEq (SdVertex K n)
  | 0 => inferInstanceAs (DecidableEq V)
  | n + 1 =>
    letI := instDecidableEqSdVertex K n
    inferInstanceAs (DecidableEq {s : Finset (SdVertex K n) // s ∈ (sdComplex K n).faces})

/-- `sd^n K` has finitely many vertices. -/
noncomputable instance instFintypeSdVertex (K : PreAbstractSimplicialComplex V) :
    ∀ n, Fintype (SdVertex K n)
  | 0 => inferInstanceAs (Fintype V)
  | n + 1 =>
    letI := instFintypeSdVertex K n
    letI := instDecidableEqSdVertex K n
    inferInstanceAs (Fintype {s : Finset (SdVertex K n) // s ∈ (sdComplex K n).faces})

/-- The same instances, in the shape instance search meets them at the recursive step. -/
noncomputable instance (K : PreAbstractSimplicialComplex V) (n : ℕ) :
    Fintype (FaceVertex (sdComplex K n)) := instFintypeSdVertex K (n + 1)

instance (K : PreAbstractSimplicialComplex V) (n : ℕ) :
    DecidableEq (FaceVertex (sdComplex K n)) := instDecidableEqSdVertex K (n + 1)

/-! ### The realization map of the iterated subdivision -/

/-- The linear map placing `sd^n K` into `V → ℝ`, obtained by composing the one-step maps. -/
noncomputable def sdLinearIter (K : PreAbstractSimplicialComplex V) :
    (n : ℕ) → ((SdVertex K n → ℝ) →ₗ[ℝ] (V → ℝ))
  | 0 => LinearMap.id
  | n + 1 => (sdLinearIter K n).comp sdLinearMap

@[simp]
theorem sdLinearIter_zero (K : PreAbstractSimplicialComplex V) :
    sdLinearIter K 0 = LinearMap.id := rfl

@[simp]
theorem sdLinearIter_succ (K : PreAbstractSimplicialComplex V) (n : ℕ) :
    sdLinearIter K (n + 1) = (sdLinearIter K n).comp sdLinearMap := rfl

omit [DecidableEq V] in
/-- One step: a linear map placing the vertices of `C` at points `q` places the vertices of
`sd C` — which are faces of `C` — at the corresponding centroids.

This is stated for a general complex rather than inline in the induction below because `rw`
cannot see through the type-level recursion defining `SdVertex`. -/
theorem comp_sdLinearMap_apply_vertexEmbed {W : Type*} [DecidableEq W]
    {C : PreAbstractSimplicialComplex W} [Fintype (FaceVertex C)]
    (φ : (W → ℝ) →ₗ[ℝ] (V → ℝ)) (q : W → (V → ℝ)) (hq : ∀ u, φ (vertexEmbed u) = q u)
    (c : FaceVertex C) : φ (sdLinearMap (vertexEmbed c)) = centroid q c.1 := by
  rw [sdLinearMap_apply_vertexEmbed, barycenter, map_smul, map_sum, centroid]
  exact congrArg _ (Finset.sum_congr rfl fun u _ => hq u)

/-- The iterated realization map sends the `c`-th basis vector to the point placed at `c`. -/
theorem sdLinearIter_apply_vertexEmbed (K : PreAbstractSimplicialComplex V) :
    ∀ (n : ℕ) (c : SdVertex K n), sdLinearIter K n (vertexEmbed c) = sdPoints K n c := by
  intro n
  induction n with
  | zero => intro c; rfl
  | succ n ih =>
    intro c
    exact comp_sdLinearMap_apply_vertexEmbed (sdLinearIter K n) (sdPoints K n) ih c

/-- The iterated realization map carries `|sd^n K|` into `|K|`. -/
theorem sdLinearIter_mem_space (K : PreAbstractSimplicialComplex V) :
    ∀ (n : ℕ) {x : SdVertex K n → ℝ}, x ∈ (sdComplex K n).geometricRealization.space →
      sdLinearIter K n x ∈ K.geometricRealization.space := by
  intro n
  induction n with
  | zero => exact fun hx => hx
  | succ n ih => exact fun hx => ih (sdLinearMap_mem_space hx)

/-- The iterated realization map carries the vertex set of a face to the placed points. -/
theorem sdLinearIter_image_faceEmbed (K : PreAbstractSimplicialComplex V) (n : ℕ)
    (t : Finset (SdVertex K n)) :
    sdLinearIter K n '' (↑(faceEmbed t) : Set (SdVertex K n → ℝ))
      = sdPoints K n '' (↑t : Set (SdVertex K n)) := by
  rw [coe_faceEmbed, Set.image_image]
  exact Set.image_congr fun u _ => sdLinearIter_apply_vertexEmbed K n u

/-- The image of a simplex of `sd^n K` is the simplex spanned by the placed points. -/
theorem sdLinearIter_image_convexHull (K : PreAbstractSimplicialComplex V) (n : ℕ)
    (t : Finset (SdVertex K n)) :
    sdLinearIter K n '' (convexHull ℝ (↑(faceEmbed t) : Set (SdVertex K n → ℝ)))
      = convexHull ℝ (sdPoints K n '' (↑t : Set (SdVertex K n))) := by
  rw [← sdLinearIter_image_faceEmbed, (sdLinearIter K n).image_convexHull]

/-! ### Dimension is preserved -/

omit [DecidableEq V] [Fintype V] in
/-- Subdivision does not increase the number of vertices of a face. -/
theorem card_le_sdComplex {K : PreAbstractSimplicialComplex V} {N : ℕ}
    (hN : ∀ s ∈ K.faces, s.card ≤ N) :
    ∀ (n : ℕ), ∀ s ∈ (sdComplex K n).faces, s.card ≤ N := by
  intro n
  induction n with
  | zero => exact hN
  | succ n ih => exact fun s hs => card_le_of_mem_barySubdivision ih hs

/-! ### The mesh shrinks geometrically -/

/-- After `n` subdivisions, every face spans a set of diameter at most `(1 - 1/N)^n · m`. -/
theorem diam_sdPoints_le {K : PreAbstractSimplicialComplex V} {m : ℝ} {N : ℕ}
    (hm : ∀ s ∈ K.faces, diam (vertexEmbed '' (↑s : Set V)) ≤ m)
    (hN : ∀ s ∈ K.faces, s.card ≤ N) :
    ∀ (n : ℕ), ∀ s ∈ (sdComplex K n).faces,
      diam (sdPoints K n '' (↑s : Set (SdVertex K n))) ≤ (1 - (N : ℝ)⁻¹) ^ n * m := by
  intro n
  induction n with
  | zero =>
    simp only [pow_zero, one_mul, sdPoints_zero]
    exact hm
  | succ n ih =>
    intro s hs
    have := diam_image_centroid_le (p := sdPoints K n) ih (card_le_sdComplex hN n) hs
    calc diam (sdPoints K (n + 1) '' (↑s : Set (SdVertex K (n + 1))))
        ≤ (1 - (N : ℝ)⁻¹) * ((1 - (N : ℝ)⁻¹) ^ n * m) := this
      _ = (1 - (N : ℝ)⁻¹) ^ (n + 1) * m := by ring

omit [DecidableEq V] [Fintype V] in
/-- A geometrically decaying bound eventually drops below any positive scale. -/
theorem exists_pow_mul_lt {r m δ : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (hδ : 0 < δ) :
    ∃ n : ℕ, r ^ n * m < δ := by
  have htend : Filter.Tendsto (fun n : ℕ => r ^ n * m) Filter.atTop (nhds 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).mul_const m
  exact (htend.eventually (gt_mem_nhds hδ)).exists

/-- The diameters eventually drop below any positive scale. -/
theorem exists_diam_sdPoints_lt {K : PreAbstractSimplicialComplex V} {m : ℝ} {N : ℕ}
    (hm : ∀ s ∈ K.faces, diam (vertexEmbed '' (↑s : Set V)) ≤ m)
    (hN : ∀ s ∈ K.faces, s.card ≤ N) (hN1 : 1 ≤ N) {ε : ℝ} (hε : 0 < ε) :
    ∃ n : ℕ, ∀ s ∈ (sdComplex K n).faces,
      diam (sdPoints K n '' (↑s : Set (SdVertex K n))) < ε := by
  have h1N : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hNpos : (0 : ℝ) < N := by linarith
  have hfactor : (0 : ℝ) ≤ 1 - (N : ℝ)⁻¹ := by
    have := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) h1N
    simp only [one_div, inv_one] at this
    linarith
  have hlt : 1 - (N : ℝ)⁻¹ < 1 := by
    have : (0 : ℝ) < (N : ℝ)⁻¹ := by positivity
    linarith
  -- `(1 - 1/N)^n * m → 0`, so some term is below `ε`
  have htend : Filter.Tendsto (fun n : ℕ => (1 - (N : ℝ)⁻¹) ^ n * m) Filter.atTop (nhds 0) := by
    have := tendsto_pow_atTop_nhds_zero_of_lt_one hfactor hlt
    simpa using this.mul_const m
  obtain ⟨n, hn⟩ := ((htend.eventually (gt_mem_nhds hε)).exists)
  exact ⟨n, fun s hs => lt_of_le_of_lt (diam_sdPoints_le hm hN n s hs) hn⟩

/-- **The simplices of `sd^n K` are small in `|K|`.** Their images have diameter at most
`(1 - 1/N)^n · m`. -/
theorem diam_sdLinearIter_image_le {K : PreAbstractSimplicialComplex V} {m : ℝ} {N : ℕ}
    (hm : ∀ s ∈ K.faces, diam (vertexEmbed '' (↑s : Set V)) ≤ m)
    (hN : ∀ s ∈ K.faces, s.card ≤ N) (n : ℕ) {t : Finset (SdVertex K n)}
    (ht : t ∈ (sdComplex K n).faces) :
    diam (sdLinearIter K n '' (convexHull ℝ (↑(faceEmbed t) : Set (SdVertex K n → ℝ))))
      ≤ (1 - (N : ℝ)⁻¹) ^ n * m := by
  rw [sdLinearIter_image_convexHull, convexHull_diam]
  exact diam_sdPoints_le hm hN n t ht

/-- The map `|sd^n K| → |K|` realizing the iterated subdivision. -/
noncomputable def sdRealizeIterMap (K : PreAbstractSimplicialComplex V) (n : ℕ) :
    (sdComplex K n).geometricRealization.space → K.geometricRealization.space :=
  fun x => ⟨sdLinearIter K n x.1, sdLinearIter_mem_space K n x.2⟩

@[simp]
theorem sdRealizeIterMap_coe (K : PreAbstractSimplicialComplex V) (n : ℕ)
    (x : (sdComplex K n).geometricRealization.space) :
    (sdRealizeIterMap K n x : V → ℝ) = sdLinearIter K n x.1 := rfl

/-- The realization map of the iterated subdivision is continuous: it is the restriction of a
linear map on a finite-dimensional space. -/
noncomputable def sdRealizeIterCM (K : PreAbstractSimplicialComplex V) (n : ℕ) :
    C((sdComplex K n).geometricRealization.space, K.geometricRealization.space) where
  toFun := sdRealizeIterMap K n
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (sdLinearIter K n).continuous_of_finiteDimensional.comp continuous_subtype_val

@[simp]
theorem sdRealizeIterCM_apply (K : PreAbstractSimplicialComplex V) (n : ℕ)
    (x : (sdComplex K n).geometricRealization.space) :
    sdRealizeIterCM K n x = sdRealizeIterMap K n x := rfl

/-! ### The iterated realization is a homeomorphism -/

/-- Each subdivision realizes homeomorphically, so `|sd^n K| ≅ |K|`. -/
theorem isHomeomorph_sdRealizeIterMap (K : PreAbstractSimplicialComplex V) :
    ∀ n : ℕ, IsHomeomorph (sdRealizeIterMap K n) := by
  intro n
  induction n with
  | zero =>
    have : sdRealizeIterMap K 0 = id := by
      funext x
      exact Subtype.ext rfl
    rw [this]
    exact IsHomeomorph.id
  | succ n ih =>
    have hcomp : sdRealizeIterMap K (n + 1) = sdRealizeIterMap K n ∘ sdRealizeMap := by
      funext x
      exact Subtype.ext rfl
    rw [hcomp]
    exact ih.comp sdRealizeMap_isHomeomorph

/-- `|sd^n K| ≅ |K|`: the identification of the iterated subdivision with the original space. -/
noncomputable def sdRealizeIterHomeomorph (K : PreAbstractSimplicialComplex V) (n : ℕ) :
    (sdComplex K n).geometricRealization.space ≃ₜ K.geometricRealization.space :=
  (isHomeomorph_sdRealizeIterMap K n).homeomorph _

@[simp]
theorem sdRealizeIterHomeomorph_apply (K : PreAbstractSimplicialComplex V) (n : ℕ)
    (x : (sdComplex K n).geometricRealization.space) :
    sdRealizeIterHomeomorph K n x = sdRealizeIterMap K n x := rfl

/-- The inverse identification `|K| ≅ |sd^n K|`, as a continuous map. -/
noncomputable def sdRealizeIterSymmCM (K : PreAbstractSimplicialComplex V) (n : ℕ) :
    C(K.geometricRealization.space, (sdComplex K n).geometricRealization.space) :=
  ⟨(sdRealizeIterHomeomorph K n).symm, (sdRealizeIterHomeomorph K n).symm.continuous⟩

@[simp]
theorem sdRealizeIterMap_sdRealizeIterSymmCM (K : PreAbstractSimplicialComplex V) (n : ℕ)
    (y : K.geometricRealization.space) :
    sdRealizeIterMap K n (sdRealizeIterSymmCM K n y) = y :=
  (sdRealizeIterHomeomorph K n).apply_symm_apply y

end PreAbstractSimplicialComplex
