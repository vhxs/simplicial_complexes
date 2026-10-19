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

end PreAbstractSimplicialComplex
