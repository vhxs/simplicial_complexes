import Mathlib.Analysis.Convex.Combination
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Homeomorph.Lemmas
import SimplicialComplexes.Basic
import SimplicialComplexes.GeometricRealization

/-!
# Barycentric Subdivision

This file defines the (combinatorial) barycentric subdivision of a simplicial complex.

Given `K : CombinatorialSimplicialComplex V`, the barycentric subdivision `barySubdivision K`
is a new simplicial complex whose:
- vertices are the faces of `K` (type `FaceVertex K`)
- faces are nonempty finite chains of faces of `K` under inclusion

## Main definitions

* `FaceVertex K`: The vertex type of `barySubdivision K`.
* `isChainFaces`: A finite set of face-vertices forms a chain if the underlying finsets
  are pairwise comparable under `⊆`.
* `barySubdivision`: The barycentric subdivision of `K`.
* `barycenter s`: The barycenter of a face `s`, i.e., the average of its vertex embeddings.

## Main results

* `isChainFaces_mono`: Subsets of chains are chains.
* `singleton_mem_barySubdivision`: Every face-vertex is a vertex of `barySubdivision K`.
* `barySubdivision_vertices`: The vertex set of `barySubdivision K` is all of `FaceVertex K`.
* `barycenter_mem_space`: The barycenter of any face of `K` lies in `|K|`.
-/

open Finset Set Geometry

set_option linter.style.openClassical false
open Classical

-- `DecidableEq V` is assumed rather than taken from `Classical`: the vertex embedding carries
-- that instance, and at the type `FaceVertex K` both a classical and a structural instance are
-- available, so leaving the choice to instance search mixes the two and unification diverges.
variable {V : Type*} [DecidableEq V]

/-! ### Indexing a list by position -/

section ListVal

variable {M : Type*} [AddCommMonoid M]

/-- `f` applied to the `i`-th entry of `l`, or `0` when `i` is out of range. -/
def listVal (l : List V) (f : V → M) (i : ℕ) : M :=
  if h : i < l.length then f l[i] else 0

omit [DecidableEq V] in
theorem listVal_of_lt {l : List V} {f : V → M} {i : ℕ} (h : i < l.length) :
    listVal l f i = f l[i] := dif_pos h

omit [DecidableEq V] in
theorem listVal_of_le {l : List V} {f : V → M} {i : ℕ} (h : l.length ≤ i) :
    listVal l f i = 0 := dif_neg (Nat.not_lt.mpr h)

/-- Summing `f` over the first `n` entries of a duplicate-free list gives the same result
whether taken over the prefix as a finset or as a range sum. -/
theorem sum_toFinset_take_eq_sum_range {l : List V} (hl : l.Nodup) (f : V → M) (n : ℕ) :
    ∑ v ∈ (l.take n).toFinset, f v = ∑ i ∈ Finset.range n, listVal l f i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rcases lt_or_ge n l.length with hn | hn
    · have hnotmem : l[n] ∉ (l.take n).toFinset := by
        rw [List.mem_toFinset]
        intro hcon
        obtain ⟨j, hj, hjeq⟩ := List.mem_iff_getElem.mp hcon
        rw [List.length_take] at hj
        rw [List.getElem_take] at hjeq
        have : j = n := (List.Nodup.getElem_inj_iff hl).mp hjeq
        omega
      have htake : (l.take (n + 1)).toFinset = insert l[n] (l.take n).toFinset := by
        rw [List.take_add_one, List.getElem?_eq_getElem hn]
        simp only [Option.toList_some, List.toFinset_append, List.toFinset_cons,
          List.toFinset_nil, Finset.union_insert, Finset.union_empty]
      rw [htake, Finset.sum_insert hnotmem, Finset.sum_range_succ, listVal_of_lt hn, ih,
        add_comm]
    · have h1 : l.take (n + 1) = l.take n := by
        rw [List.take_of_length_le (by omega), List.take_of_length_le hn]
      rw [h1, Finset.sum_range_succ, listVal_of_le hn, add_zero, ih]

end ListVal

/-- The vertex type of the barycentric subdivision of `K`: faces of `K`. -/
abbrev FaceVertex (K : CombinatorialSimplicialComplex V) := {s : Finset V // s ∈ K.faces}

namespace CombinatorialSimplicialComplex

variable {K : CombinatorialSimplicialComplex V}

/-! ### Chains of faces -/

/-- A finite set of face-vertices is a chain if its underlying finsets are pairwise
comparable under inclusion. -/
def isChainFaces (t : Finset (FaceVertex K)) : Prop :=
  (t : Set (FaceVertex K)).Pairwise (fun a b => a.1 ⊆ b.1 ∨ b.1 ⊆ a.1)

omit [DecidableEq V] in
@[simp]
theorem isChainFaces_empty : isChainFaces (∅ : Finset (FaceVertex K)) := by
  simp [isChainFaces]

omit [DecidableEq V] in
theorem isChainFaces_singleton (c : FaceVertex K) :
    isChainFaces ({c} : Finset (FaceVertex K)) := by
  simp [isChainFaces]

omit [DecidableEq V] in
theorem isChainFaces_mono {s t : Finset (FaceVertex K)} (hst : s ⊆ t)
    (ht : isChainFaces t) : isChainFaces s :=
  Set.Pairwise.mono (Finset.coe_subset.mpr hst) ht

/-! ### The barycentric subdivision -/

/-- The barycentric subdivision of `K`: faces are nonempty chains of faces of `K`. -/
def barySubdivision (K : CombinatorialSimplicialComplex V) :
    CombinatorialSimplicialComplex (FaceVertex K) where
  faces := {t | t.Nonempty ∧ isChainFaces t}
  nonempty_of_mem h := h.1
  down_closed h hst hne := ⟨hne, isChainFaces_mono hst h.2⟩

omit [DecidableEq V] in
@[simp]
theorem barySubdivision_faces :
    (barySubdivision K).faces = {t | t.Nonempty ∧ isChainFaces t} := rfl

omit [DecidableEq V] in
theorem mem_barySubdivision_iff {t : Finset (FaceVertex K)} :
    t ∈ (barySubdivision K).faces ↔ t.Nonempty ∧ isChainFaces t := Iff.rfl

omit [DecidableEq V] in
/-- Every singleton `{c}` is a face of `barySubdivision K`. -/
theorem singleton_mem_barySubdivision (c : FaceVertex K) :
    ({c} : Finset (FaceVertex K)) ∈ (barySubdivision K).faces :=
  ⟨Finset.singleton_nonempty c, isChainFaces_singleton c⟩

omit [DecidableEq V] in
/-- Every face-vertex is a vertex of `barySubdivision K`. -/
theorem barySubdivision_vertices :
    (barySubdivision K).vertices = Set.univ := by
  ext c
  simp only [mem_vertices, barySubdivision_faces, Set.mem_setOf_eq, Set.mem_univ, iff_true]
  exact singleton_mem_barySubdivision c

/-! ### Barycenter of a face -/

/-- The barycenter of a face `s`: the average of its vertex embeddings in `V → ℝ`. -/
noncomputable def barycenter (s : Finset V) : V → ℝ :=
  (s.card : ℝ)⁻¹ • ∑ v ∈ s, vertexEmbed v

theorem barycenter_eq_centerMass (s : Finset V) :
    barycenter s = s.centerMass (fun _ => (1 : ℝ)) vertexEmbed := by
  simp [barycenter, Finset.centerMass, Finset.sum_const, one_smul, nsmul_eq_mul]

/-- The barycenter of a nonempty finset lies in the convex hull of its vertex embeddings. -/
theorem barycenter_mem_convexHull {s : Finset V} (hne : s.Nonempty) :
    barycenter s ∈ convexHull ℝ ↑(faceEmbed s) := by
  rw [barycenter_eq_centerMass]
  apply Finset.centerMass_mem_convexHull
  · intro i _; norm_num
  · simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
    exact Nat.cast_pos.mpr (Finset.card_pos.mpr hne)
  · intro v hv
    exact Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hv)

/-- The barycenter of a face of `K` lies in the geometric realization `|K|`. -/
theorem barycenter_mem_space {s : Finset V} (hs : s ∈ K.faces) :
    barycenter s ∈ K.geometricRealization.space := by
  simp only [SimplicialComplex.mem_space_iff, geometricRealization_faces, Set.mem_image]
  exact ⟨faceEmbed s, ⟨s, hs, rfl⟩, barycenter_mem_convexHull (K.nonempty_of_mem hs)⟩

/-! ### The linear map on geometric realizations -/

/-- The linear map `|sd(K)| → |K|` extending `Pi.single c 1 ↦ barycenter c.1`. -/
noncomputable def sdLinearMap [Fintype (FaceVertex K)] :
    (FaceVertex K → ℝ) →ₗ[ℝ] (V → ℝ) :=
  (Pi.basisFun ℝ (FaceVertex K)).constr ℝ (fun c => barycenter c.1)

/-- `sdLinearMap` sends the `c`-th basis vector to the barycenter of `c`. -/
theorem sdLinearMap_apply_single [Fintype (FaceVertex K)] (c : FaceVertex K) :
    sdLinearMap (Pi.single c 1) = barycenter c.1 := by
  have h := (Pi.basisFun ℝ (FaceVertex K)).constr_basis ℝ (fun c => barycenter c.1) c
  simp only [Pi.basisFun_apply] at h
  exact h

theorem sdLinearMap_apply_vertexEmbed [Fintype (FaceVertex K)] (c : FaceVertex K) :
    sdLinearMap (vertexEmbed c) = barycenter c.1 :=
  sdLinearMap_apply_single c

/-- `sdLinearMap` sends `|sd(K)|` into `|K|`. -/
theorem sdLinearMap_mem_space [Fintype (FaceVertex K)] {x : FaceVertex K → ℝ}
    (hx : x ∈ (barySubdivision K).geometricRealization.space) :
    sdLinearMap x ∈ K.geometricRealization.space := by
  simp only [SimplicialComplex.mem_space_iff, geometricRealization_faces,
             Set.mem_image] at hx ⊢
  obtain ⟨_, ⟨t, ht, rfl⟩, hxt⟩ := hx
  rw [mem_barySubdivision_iff] at ht
  -- Extract the element of t with maximal cardinality — it will contain all others
  obtain ⟨c_max, hc_max_mem, hc_max_card⟩ := t.exists_max_image (fun c => c.1.card) ht.1
  -- Every c ∈ t satisfies c.1 ⊆ c_max.1 (by chain property + cardinality maximality)
  have hc_max_max : ∀ c ∈ t, c.1 ⊆ c_max.1 := by
    intro c hc
    rcases eq_or_ne c c_max with rfl | hne
    · exact Finset.Subset.refl _
    · rcases ht.2 (Finset.mem_coe.mpr hc) (Finset.mem_coe.mpr hc_max_mem) hne with h | h
      · exact h
      · exact absurd (Subtype.ext (Finset.eq_of_subset_of_card_le h (hc_max_card c hc)))
                     hne.symm
  -- The goal: sdLinearMap x ∈ convexHull ℝ ↑(faceEmbed c_max.1)
  refine ⟨faceEmbed c_max.1, ⟨c_max.1, c_max.2, rfl⟩, ?_⟩
  -- Each sd-vertex of t maps to a point in convexHull ℝ ↑(faceEmbed c_max.1)
  have hbary_sub : sdLinearMap '' (↑(faceEmbed t) : Set (FaceVertex K → ℝ)) ⊆
      convexHull ℝ (↑(faceEmbed c_max.1) : Set (V → ℝ)) := by
    rintro _ ⟨e, he, rfl⟩
    simp only [faceEmbed, Finset.coe_image, Set.mem_image] at he
    obtain ⟨c, hc, rfl⟩ := he
    rw [sdLinearMap_apply_vertexEmbed]
    exact convexHull_mono
      (Finset.coe_subset.mpr (Finset.image_subset_image (hc_max_max c hc)))
      (barycenter_mem_convexHull (K.nonempty_of_mem c.2))
  -- sdLinearMap x lands in convexHull of the image, which lies in convexHull ↑(faceEmbed c_max.1)
  have himg : sdLinearMap x ∈
      convexHull ℝ (sdLinearMap '' (↑(faceEmbed t) : Set (FaceVertex K → ℝ))) := by
    rw [← sdLinearMap.image_convexHull]; exact Set.mem_image_of_mem _ hxt
  exact convexHull_min hbary_sub (convex_convexHull ℝ _) himg

/-- The continuous map `|sd(K)| → |K|` induced by the barycentric subdivision. -/
noncomputable def sdRealizeMap [Fintype (FaceVertex K)] :
    C((barySubdivision K).geometricRealization.space, K.geometricRealization.space) where
  toFun := fun ⟨x, hx⟩ => ⟨sdLinearMap x, sdLinearMap_mem_space hx⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact sdLinearMap.continuous_of_finiteDimensional.comp continuous_subtype_val

/-! ### Homeomorphism -/

/-- `sdLinearMap` commutes with finite weighted sums: applying it to `∑ c ∈ t, μ c • vertexEmbed c`
gives `∑ c ∈ t, μ c • barycenter c.1`. -/
theorem sdLinearMap_apply_sum [Fintype (FaceVertex K)]
    (t : Finset (FaceVertex K)) (μ : FaceVertex K → ℝ) :
    sdLinearMap (∑ c ∈ t, μ c • vertexEmbed c) = ∑ c ∈ t, μ c • barycenter c.1 := by
  simp only [map_sum, map_smul, sdLinearMap_apply_vertexEmbed]

/-- A point in `convexHull ℝ ↑(faceEmbed s)` can be written as `∑ v ∈ s, w v • vertexEmbed v`
with nonneg weights summing to 1. -/
theorem exists_weights_of_mem_convexHull_faceEmbed {s : Finset V} {y : V → ℝ}
    (hy : y ∈ convexHull ℝ (↑(faceEmbed s) : Set (V → ℝ))) :
    ∃ w : V → ℝ, (∀ v ∈ s, 0 ≤ w v) ∧ ∑ v ∈ s, w v = 1 ∧
      y = ∑ v ∈ s, w v • vertexEmbed v := by
  rw [Finset.convexHull_eq] at hy
  obtain ⟨f, hf_nn, hf_sum, hf_cm⟩ := hy
  have hinj : ∀ a ∈ s, ∀ b ∈ s, vertexEmbed a = vertexEmbed b → a = b :=
    fun a _ b _ h => vertexEmbed_injective h
  refine ⟨fun v => f (vertexEmbed v), ?_, ?_, ?_⟩
  · intro v hv
    exact hf_nn _ (Finset.mem_image_of_mem _ hv)
  · simp only [faceEmbed] at hf_sum
    rwa [← Finset.sum_image hinj]
  · rw [← hf_cm]
    simp only [Finset.centerMass, id_eq]
    rw [hf_sum, inv_one, one_smul]
    simp only [faceEmbed]
    exact Finset.sum_image hinj

/-- A convex combination of vertex embeddings of a face `t ∈ (barySubdivision K).faces` lies
in `|sd(K)|`. -/
theorem weightedSum_mem_sdSpace
    {t : Finset (FaceVertex K)} {μ : FaceVertex K → ℝ}
    (ht : t ∈ (barySubdivision K).faces)
    (hμ_nn : ∀ c ∈ t, 0 ≤ μ c)
    (hμ_sum : ∑ c ∈ t, μ c = 1) :
    ∑ c ∈ t, μ c • vertexEmbed c ∈
      (barySubdivision K).geometricRealization.space := by
  simp only [SimplicialComplex.mem_space_iff, geometricRealization_faces, Set.mem_image]
  refine ⟨faceEmbed t, ⟨t, ht, rfl⟩, ?_⟩
  have hcm : t.centerMass μ vertexEmbed = ∑ c ∈ t, μ c • vertexEmbed c := by
    simp [Finset.centerMass, hμ_sum]
  rw [← hcm]
  apply Finset.centerMass_mem_convexHull
  · exact hμ_nn
  · rw [hμ_sum]; norm_num
  · intro c hc
    exact Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hc)

/-- Every finset `s` with a weight function `w` admits a list representation sorted by
non-increasing weight. -/
theorem sorted_list_of_finset (s : Finset V) (w : V → ℝ) :
    ∃ l : List V, l.toFinset = s ∧ l.Pairwise (fun a b => w b ≤ w a) ∧ l.Nodup := by
  suffices h : ∀ n (s : Finset V), s.card = n →
      ∃ l : List V, l.toFinset = s ∧ l.Pairwise (fun a b => w b ≤ w a) ∧ l.Nodup from
    h s.card s rfl
  intro n
  induction n with
  | zero =>
    intro s hs
    exact ⟨[], by simp [Finset.card_eq_zero.mp hs], List.Pairwise.nil, List.nodup_nil⟩
  | succ n ih =>
    intro s hs
    have hne : s.Nonempty := Finset.card_pos.mp (hs ▸ Nat.succ_pos n)
    obtain ⟨m, hm_mem, hm_max⟩ := Finset.exists_max_image s w hne
    obtain ⟨l', hl'_set, hl'_pw, hl'_nd⟩ := ih (s.erase m)
      (by rw [Finset.card_erase_of_mem hm_mem, hs]; omega)
    exact ⟨m :: l',
      by rw [List.toFinset_cons, hl'_set, Finset.insert_erase hm_mem],
      List.pairwise_cons.mpr
        ⟨fun b hb => hm_max b
          (Finset.mem_of_mem_erase (hl'_set ▸ List.mem_toFinset.mpr hb)),
         hl'_pw⟩,
      List.nodup_cons.mpr
        ⟨by rw [← List.mem_toFinset, hl'_set]; simp [Finset.mem_erase],
         hl'_nd⟩⟩

/-- Each nonempty prefix of a duplicate-free list whose `toFinset` is a face of `K` is itself
a face of `K`. -/
theorem prefix_mem_faces {s : Finset V} (hs : s ∈ K.faces)
    {l : List V} (hl : l.toFinset = s) (hl_nd : l.Nodup)
    (i : Fin l.length) : (l.take (i.val + 1)).toFinset ∈ K.faces := by
  apply K.down_closed hs
  · -- (l.take (i+1)).toFinset ⊆ s
    intro x hx
    rw [List.mem_toFinset] at hx
    rw [← hl, List.mem_toFinset]
    exact List.take_subset _ _ hx
  · -- (l.take (i+1)).toFinset is nonempty: head of l is in l.take (i+1)
    have hne_l : l ≠ [] := by rintro rfl; exact absurd i.isLt (by simp)
    obtain ⟨a, l', rfl⟩ : ∃ a l', l = a :: l' := by
      cases l with | nil => exact absurd rfl hne_l | cons a l' => exact ⟨a, l', rfl⟩
    exact ⟨a, List.mem_toFinset.mpr (by simp [List.take])⟩

/-- The image of all prefix-faces of a nonempty list forms a nonempty chain, hence a face of
`barySubdivision K`. -/
theorem prefixChain_mem_barySubdivision {l : List V} (hl_pos : 0 < l.length)
    (hpfx : ∀ i : Fin l.length, (l.take (i.val + 1)).toFinset ∈ K.faces) :
    Finset.image (fun i => (⟨(l.take (i.val + 1)).toFinset, hpfx i⟩ : FaceVertex K))
      Finset.univ ∈ (barySubdivision K).faces := by
  rw [mem_barySubdivision_iff]
  refine ⟨⟨_, Finset.mem_image_of_mem _ (Finset.mem_univ ⟨0, hl_pos⟩)⟩, ?_⟩
  intro a ha b hb _
  simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range] at ha hb
  obtain ⟨i, rfl⟩ := ha
  obtain ⟨j, rfl⟩ := hb
  -- Chain property: compare by index; WLOG i ≤ j gives take (i+1) ⊆ take (j+1)
  rcases Nat.le_total i.val j.val with hij | hij
  · left
    intro x hx
    simp only [List.mem_toFinset] at hx ⊢
    have hmem : x ∈ (l.take (j.val + 1)).take (i.val + 1) := by
      have hmin : min (i.val + 1) (j.val + 1) = i.val + 1 := by omega
      rw [List.take_take, hmin]; exact hx
    exact List.take_subset _ _ hmem
  · right
    intro x hx
    simp only [List.mem_toFinset] at hx ⊢
    have hmem : x ∈ (l.take (i.val + 1)).take (j.val + 1) := by
      have hmin : min (j.val + 1) (i.val + 1) = j.val + 1 := by omega
      rw [List.take_take, hmin]; exact hx
    exact List.take_subset _ _ hmem

/-- Given a sorted list `l` representing a face `s` of `K` with weights `w`, there exist
chain weights `μ` on the prefix-chain that are nonneg, sum to 1, and reconstruct the original
weighted sum of vertex embeddings.

The weights are `μ(prefix i) = (i+1) * (w(l[i]) - w(l[i+1]))` (with boundary term at the end),
which are nonneg by the sorted order and telescope to reproduce `∑ v ∈ s, w v • vertexEmbed v`. -/
theorem chain_weights_of_sorted_list
    {s : Finset V} {w : V → ℝ}
    (hw_nn : ∀ v ∈ s, 0 ≤ w v) (hw_sum : ∑ v ∈ s, w v = 1)
    {l : List V} (hl : l.toFinset = s) (hl_sorted : l.Pairwise (fun a b => w b ≤ w a))
    (hl_nd : l.Nodup)
    (hpfx : ∀ i : Fin l.length, (l.take (i.val + 1)).toFinset ∈ K.faces) :
    let t := Finset.image (fun i => (⟨(l.take (i.val + 1)).toFinset, hpfx i⟩ : FaceVertex K))
               Finset.univ
    ∃ μ : FaceVertex K → ℝ,
      (∀ c ∈ t, 0 ≤ μ c) ∧
      ∑ c ∈ t, μ c = 1 ∧
      ∑ c ∈ t, μ c • barycenter c.1 = ∑ v ∈ s, w v • vertexEmbed v := by
  intro t
  have ht_def : t = Finset.image
      (fun i : Fin l.length => (⟨(l.take (i.val + 1)).toFinset, hpfx i⟩ : FaceVertex K))
      Finset.univ := rfl
  set W : ℕ → ℝ := listVal l w with hW
  set ev : ℕ → (V → ℝ) := listVal l vertexEmbed with hev
  have hcard : ∀ i : Fin l.length, ((l.take (i.val + 1)).toFinset).card = i.val + 1 := by
    intro i
    have hi := i.isLt
    rw [List.toFinset_card_of_nodup (List.Nodup.sublist (l.take_sublist _) hl_nd),
      List.length_take]
    omega
  have hinj : Set.InjOn
      (fun i : Fin l.length => (⟨(l.take (i.val + 1)).toFinset, hpfx i⟩ : FaceVertex K))
      ↑(Finset.univ : Finset (Fin l.length)) := by
    intro i _ j _ hij
    have := congrArg (fun c : FaceVertex K => c.1.card) hij
    simp only [hcard i, hcard j] at this
    exact Fin.ext (by omega)
  have hsum : ∀ g : FaceVertex K → ℝ,
      ∑ c ∈ t, g c = ∑ i : Fin l.length, g ⟨(l.take (i.val + 1)).toFinset, hpfx i⟩ := by
    intro g
    rw [ht_def]
    exact Finset.sum_image hinj
  have hsum' : ∀ g : FaceVertex K → (V → ℝ),
      ∑ c ∈ t, g c = ∑ i : Fin l.length, g ⟨(l.take (i.val + 1)).toFinset, hpfx i⟩ := by
    intro g
    rw [ht_def]
    exact Finset.sum_image hinj
  have hWnn : ∀ i, 0 ≤ W i := by
    intro i
    rcases lt_or_ge i l.length with hi | hi
    · rw [hW, listVal_of_lt hi]
      exact hw_nn _ (hl ▸ List.mem_toFinset.mpr (List.getElem_mem hi))
    · rw [hW, listVal_of_le hi]
  have hWmono : ∀ i, W (i + 1) ≤ W i := by
    intro i
    rcases lt_or_ge (i + 1) l.length with hi | hi
    · have hi' : i < l.length := by omega
      rw [hW, listVal_of_lt hi, listVal_of_lt hi']
      exact List.pairwise_iff_getElem.mp hl_sorted i (i + 1) hi' hi (by omega)
    · rw [hW, listVal_of_le hi]
      exact hWnn i
  have hWlen : W l.length = 0 := by rw [hW, listVal_of_le le_rfl]
  have hWsum : ∑ i ∈ Finset.range l.length, W i = 1 := by
    rw [hW, ← sum_toFinset_take_eq_sum_range hl_nd w l.length, List.take_of_length_le le_rfl,
      hl, hw_sum]
  have hWev : ∑ i ∈ Finset.range l.length, W i • ev i = ∑ v ∈ s, w v • vertexEmbed v := by
    have h := sum_toFinset_take_eq_sum_range hl_nd (fun v => w v • vertexEmbed v) l.length
    rw [List.take_of_length_le le_rfl, hl] at h
    rw [h]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.mem_range] at hi
    rw [hW, hev, listVal_of_lt hi, listVal_of_lt hi, listVal_of_lt hi]
  have hbary : ∀ i : Fin l.length, barycenter (l.take (i.val + 1)).toFinset
      = (((i.val : ℝ) + 1)⁻¹) • ∑ j ∈ Finset.range (i.val + 1), ev j := by
    intro i
    rw [barycenter, hcard i, hev, ← sum_toFinset_take_eq_sum_range hl_nd vertexEmbed (i.val + 1)]
    push_cast
    rfl
  -- Abel summation: the weights `(i+1) * (W i - W (i+1))` telescope.
  have tel1 : ∀ n : ℕ, ∑ i ∈ Finset.range n, ((i : ℝ) + 1) * (W i - W (i + 1))
      = (∑ i ∈ Finset.range n, W i) - n * W n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, ih, Finset.sum_range_succ (f := W)]
      push_cast
      ring
  have tel2 : ∀ n : ℕ,
      ∑ i ∈ Finset.range n, (W i - W (i + 1)) • (∑ j ∈ Finset.range (i + 1), ev j)
      = (∑ i ∈ Finset.range n, W i • ev i) - W n • (∑ j ∈ Finset.range n, ev j) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, ih, Finset.sum_range_succ (f := fun i => W i • ev i),
        Finset.sum_range_succ (f := ev)]
      simp only [sub_smul, smul_add]
      abel
  refine ⟨fun c => (c.1.card : ℝ) * (W (c.1.card - 1) - W c.1.card), ?_, ?_, ?_⟩
  · intro c hc
    rw [ht_def, Finset.mem_image] at hc
    obtain ⟨i, -, rfl⟩ := hc
    simp only [hcard i, Nat.add_sub_cancel]
    exact mul_nonneg (by positivity) (sub_nonneg.mpr (hWmono i.val))
  · rw [hsum]
    have hterm : ∀ i : Fin l.length,
        ((((l.take (i.val + 1)).toFinset).card : ℝ)
          * (W (((l.take (i.val + 1)).toFinset).card - 1)
            - W ((l.take (i.val + 1)).toFinset).card))
        = ((i.val : ℝ) + 1) * (W i.val - W (i.val + 1)) := by
      intro i
      simp only [hcard i, Nat.add_sub_cancel]
      push_cast
      ring
    rw [Finset.sum_congr rfl fun i _ => hterm i,
      Fin.sum_univ_eq_sum_range (fun i => ((i : ℝ) + 1) * (W i - W (i + 1))) l.length,
      tel1 l.length, hWlen, hWsum]
    ring
  · rw [hsum']
    have hterm : ∀ i : Fin l.length,
        ((((l.take (i.val + 1)).toFinset).card : ℝ)
          * (W (((l.take (i.val + 1)).toFinset).card - 1)
            - W ((l.take (i.val + 1)).toFinset).card))
          • barycenter (l.take (i.val + 1)).toFinset
        = (W i.val - W (i.val + 1)) • ∑ j ∈ Finset.range (i.val + 1), ev j := by
      intro i
      rw [hbary i]
      simp only [hcard i, Nat.add_sub_cancel]
      rw [smul_smul]
      congr 1
      push_cast
      field_simp
    rw [Finset.sum_congr rfl fun i _ => hterm i,
      Fin.sum_univ_eq_sum_range
        (fun i => (W i - W (i + 1)) • ∑ j ∈ Finset.range (i + 1), ev j) l.length,
      tel2 l.length, hWlen, hWev, zero_smul, sub_zero]

/-- Core surjectivity construction: given `s ∈ K.faces` and valid barycentric weights `w` on `s`,
there is a nonempty chain `t` of faces of `K` and weights `μ` on `t` such that the weighted
sum of barycenters `∑ c ∈ t, μ c • barycenter c.1` equals `∑ v ∈ s, w v • vertexEmbed v`.

Proof idea: sort the support of `w` by decreasing weight to get vertices `v₁ ≥ v₂ ≥ … ≥ vₖ`,
form the chain `{v₁} ⊆ {v₁,v₂} ⊆ … ⊆ s`, and set `μᵢ = i · (w(vᵢ) − w(vᵢ₊₁))` (with
`μₖ = k · w(vₖ)`). These are nonneg, sum to 1, and reconstruct the original weights. -/
theorem chain_preimage_of_weights
    (s : Finset V) (hs : s ∈ K.faces)
    (w : V → ℝ) (hw_nn : ∀ v ∈ s, 0 ≤ w v) (hw_sum : ∑ v ∈ s, w v = 1) :
    ∃ (t : Finset (FaceVertex K)) (μ : FaceVertex K → ℝ),
      t ∈ (barySubdivision K).faces ∧
      (∀ c ∈ t, 0 ≤ μ c) ∧
      ∑ c ∈ t, μ c = 1 ∧
      ∑ c ∈ t, μ c • barycenter c.1 = ∑ v ∈ s, w v • vertexEmbed v := by
  have hs_ne : s.Nonempty := by
    rcases s.eq_empty_or_nonempty with rfl | h
    · simp at hw_sum
    · exact h
  obtain ⟨l, hl_toFinset, hl_sorted, hl_nodup⟩ := sorted_list_of_finset s w
  have hl_ne : l ≠ [] := fun h => hs_ne.ne_empty (by simp [← hl_toFinset, h])
  have hl_pos : 0 < l.length := by cases l with | nil => exact absurd rfl hl_ne | cons _ _ => simp
  have hpfx : ∀ i : Fin l.length, (l.take (i.val + 1)).toFinset ∈ K.faces :=
    fun i => prefix_mem_faces hs hl_toFinset hl_nodup i
  let t : Finset (FaceVertex K) :=
    Finset.image (fun i => (⟨(l.take (i.val + 1)).toFinset, hpfx i⟩ : FaceVertex K)) Finset.univ
  have ht : t ∈ (barySubdivision K).faces := prefixChain_mem_barySubdivision hl_pos hpfx
  obtain ⟨μ, hμ_nn, hμ_sum, hμ_eq⟩ :=
    chain_weights_of_sorted_list hw_nn hw_sum hl_toFinset hl_sorted hl_nodup hpfx
  exact ⟨t, μ, ht, hμ_nn, hμ_sum, hμ_eq⟩

/-! ### Injectivity of the subdivision map -/

/-- The barycenter of `s`, evaluated at a vertex. -/
theorem barycenter_apply (s : Finset V) (v : V) :
    barycenter s v = if v ∈ s then (s.card : ℝ)⁻¹ else 0 := by
  rw [barycenter]
  simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul, vertexEmbed, Pi.single_apply]
  rw [Finset.sum_ite_eq s v (fun _ => (1 : ℝ))]
  split_ifs <;> simp

theorem weightedBarycenter_apply (T : Finset (FaceVertex K)) (μ : FaceVertex K → ℝ) (v : V) :
    (∑ c ∈ T, μ c • barycenter c.1) v = ∑ c ∈ T, if v ∈ c.1 then μ c / c.1.card else 0 := by
  rw [Finset.sum_apply]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Pi.smul_apply, smul_eq_mul, barycenter_apply]
  split_ifs <;> simp [div_eq_mul_inv]

omit [DecidableEq V] in
theorem isChainFaces.exists_subset_max {T : Finset (FaceVertex K)} (hT : isChainFaces T)
    (hne : T.Nonempty) : ∃ d ∈ T, ∀ c ∈ T, c.1 ⊆ d.1 := by
  obtain ⟨d, hd, hdcard⟩ := T.exists_max_image (fun c => c.1.card) hne
  refine ⟨d, hd, fun c hc => ?_⟩
  rcases eq_or_ne c d with rfl | hne'
  · exact Finset.Subset.refl _
  · rcases hT (Finset.mem_coe.mpr hc) (Finset.mem_coe.mpr hd) hne' with h | h
    · exact h
    · exact absurd (Subtype.ext (Finset.eq_of_subset_of_card_le h (hdcard c hc))) hne'.symm

omit [DecidableEq V] in
theorem card_pos_of_mem_faces {c : FaceVertex K} : (0 : ℝ) < c.1.card := by
  exact_mod_cast Finset.card_pos.mpr (K.nonempty_of_mem c.2)

theorem le_weightedBarycenter_apply {T : Finset (FaceVertex K)} {μ : FaceVertex K → ℝ}
    (hμ : ∀ c ∈ T, 0 ≤ μ c) {d : FaceVertex K} (hd : d ∈ T) {v : V} (hv : v ∈ d.1) :
    μ d / d.1.card ≤ (∑ c ∈ T, μ c • barycenter c.1) v := by
  rw [weightedBarycenter_apply]
  rw [show μ d / (d.1.card : ℝ) = (if v ∈ d.1 then μ d / d.1.card else 0) from (if_pos hv).symm]
  refine Finset.single_le_sum (f := fun c => if v ∈ c.1 then μ c / (c.1.card : ℝ) else 0)
    (fun c hc => ?_) hd
  dsimp only
  split_ifs with h
  · exact div_nonneg (hμ c hc) (Nat.cast_nonneg _)
  · exact le_rfl

theorem exists_weightedBarycenter_apply_eq {T : Finset (FaceVertex K)} (hT : isChainFaces T)
    {μ : FaceVertex K → ℝ} {d : FaceVertex K} (hd : d ∈ T) (hmax : ∀ c ∈ T, c.1 ⊆ d.1) :
    ∃ v ∈ d.1, (∑ c ∈ T, μ c • barycenter c.1) v = μ d / d.1.card := by
  rcases (T.erase d).eq_empty_or_nonempty with hT0 | hT0
  · obtain ⟨v, hv⟩ := K.nonempty_of_mem d.2
    refine ⟨v, hv, ?_⟩
    rw [weightedBarycenter_apply, ← Finset.sum_erase_add T _ hd, hT0, Finset.sum_empty,
      zero_add, if_pos hv]
  · obtain ⟨e, he, hemax⟩ :=
      (isChainFaces_mono (Finset.erase_subset d T) hT).exists_subset_max hT0
    have hed : e.1 ⊆ d.1 := hmax e (Finset.mem_of_mem_erase he)
    have hne : e.1 ≠ d.1 := fun h => (Finset.ne_of_mem_erase he) (Subtype.ext h)
    obtain ⟨v, hvd, hve⟩ :=
      Finset.exists_of_ssubset (Finset.ssubset_iff_subset_ne.mpr ⟨hed, hne⟩)
    refine ⟨v, hvd, ?_⟩
    rw [weightedBarycenter_apply, ← Finset.sum_erase_add T _ hd,
      Finset.sum_eq_zero (fun c hc => if_neg (fun hvc => hve (hemax c hc hvc))),
      zero_add, if_pos hvd]

theorem weightedBarycenter_apply_pos_iff {T : Finset (FaceVertex K)} {μ : FaceVertex K → ℝ}
    {d : FaceVertex K} (hd : d ∈ T) (hmax : ∀ c ∈ T, c.1 ⊆ d.1) (hμ : ∀ c ∈ T, 0 < μ c) (v : V) :
    0 < (∑ c ∈ T, μ c • barycenter c.1) v ↔ v ∈ d.1 := by
  constructor
  · intro hpos
    by_contra hv
    rw [weightedBarycenter_apply,
      Finset.sum_eq_zero (fun c hc => if_neg (fun hvc => hv (hmax c hc hvc)))] at hpos
    exact lt_irrefl 0 hpos
  · intro hv
    have h1 := le_weightedBarycenter_apply (fun c hc => (hμ c hc).le) hd hv
    have h2 : 0 < μ d / (d.1.card : ℝ) := div_pos (hμ d hd) card_pos_of_mem_faces
    linarith

/-- Weighted sums of barycenters over chains determine both the chain and the weights. -/
theorem chain_weights_unique :
    ∀ (n : ℕ) {T T' : Finset (FaceVertex K)} {μ μ' : FaceVertex K → ℝ},
      T.card = n → isChainFaces T → isChainFaces T' →
      (∀ c ∈ T, 0 < μ c) → (∀ c ∈ T', 0 < μ' c) →
      ∑ c ∈ T, μ c • barycenter c.1 = ∑ c ∈ T', μ' c • barycenter c.1 →
      T = T' ∧ ∀ c ∈ T, μ c = μ' c := by
  intro n
  induction n with
  | zero =>
    intro T T' μ μ' hcard _ _ _ hμ' heq
    have hTempty : T = ∅ := Finset.card_eq_zero.mp hcard
    subst hTempty
    rw [Finset.sum_empty] at heq
    have hT'empty : T' = ∅ := by
      by_contra hcon
      obtain ⟨c, hc⟩ := Finset.nonempty_iff_ne_empty.mpr hcon
      obtain ⟨v, hv⟩ := K.nonempty_of_mem c.2
      have h1 := le_weightedBarycenter_apply (fun c hc => (hμ' c hc).le) hc hv
      rw [← heq] at h1
      simp only [Pi.zero_apply] at h1
      have h2 : 0 < μ' c / (c.1.card : ℝ) := div_pos (hμ' c hc) card_pos_of_mem_faces
      linarith
    exact ⟨hT'empty.symm, by simp⟩
  | succ n ih =>
    intro T T' μ μ' hcard hT hT' hμ hμ' heq
    have hTne : T.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨d, hd, hdmax⟩ := hT.exists_subset_max hTne
    have hT'ne : T'.Nonempty := by
      rcases T'.eq_empty_or_nonempty with rfl | h
      · exfalso
        obtain ⟨v, hv⟩ := K.nonempty_of_mem d.2
        have h1 := le_weightedBarycenter_apply (fun c hc => (hμ c hc).le) hd hv
        rw [heq, Finset.sum_empty] at h1
        simp only [Pi.zero_apply] at h1
        have h2 : 0 < μ d / (d.1.card : ℝ) := div_pos (hμ d hd) card_pos_of_mem_faces
        linarith
      · exact h
    obtain ⟨d', hd', hd'max⟩ := hT'.exists_subset_max hT'ne
    have hdd' : d = d' := by
      refine Subtype.ext (Finset.ext fun v => ?_)
      rw [← weightedBarycenter_apply_pos_iff hd hdmax hμ v, heq,
        weightedBarycenter_apply_pos_iff hd' hd'max hμ' v]
    subst hdd'
    obtain ⟨v₀, hv₀, hv₀eq⟩ := exists_weightedBarycenter_apply_eq (μ := μ) hT hd hdmax
    obtain ⟨v₁, hv₁, hv₁eq⟩ := exists_weightedBarycenter_apply_eq (μ := μ') hT' hd' hd'max
    have hle1 : μ' d / (d.1.card : ℝ) ≤ μ d / (d.1.card : ℝ) := by
      rw [← hv₀eq, heq]
      exact le_weightedBarycenter_apply (fun c hc => (hμ' c hc).le) hd' hv₀
    have hle2 : μ d / (d.1.card : ℝ) ≤ μ' d / (d.1.card : ℝ) := by
      rw [← hv₁eq, ← heq]
      exact le_weightedBarycenter_apply (fun c hc => (hμ c hc).le) hd hv₁
    have hμd : μ d = μ' d := by
      have h := le_antisymm hle2 hle1
      have hc : (d.1.card : ℝ) ≠ 0 := ne_of_gt card_pos_of_mem_faces
      field_simp at h
      exact h
    have hsub : ∑ c ∈ T.erase d, μ c • barycenter c.1
        = ∑ c ∈ T'.erase d, μ' c • barycenter c.1 := by
      have e1 : ∑ c ∈ T.erase d, μ c • barycenter c.1 + μ d • barycenter d.1
          = ∑ c ∈ T, μ c • barycenter c.1 := Finset.sum_erase_add T _ hd
      have e2 : ∑ c ∈ T'.erase d, μ' c • barycenter c.1 + μ' d • barycenter d.1
          = ∑ c ∈ T', μ' c • barycenter c.1 := Finset.sum_erase_add T' _ hd'
      rw [← e1, ← e2, hμd] at heq
      exact add_right_cancel heq
    obtain ⟨hTT', hww⟩ := ih (by rw [Finset.card_erase_of_mem hd, hcard]; omega)
      (isChainFaces_mono (Finset.erase_subset _ _) hT)
      (isChainFaces_mono (Finset.erase_subset _ _) hT')
      (fun c hc => hμ c (Finset.mem_of_mem_erase hc))
      (fun c hc => hμ' c (Finset.mem_of_mem_erase hc)) hsub
    refine ⟨?_, fun c hc => ?_⟩
    · rw [← Finset.insert_erase hd, ← Finset.insert_erase hd', hTT']
    · rcases eq_or_ne c d with rfl | hcd
      · exact hμd
      · exact hww c (Finset.mem_erase.mpr ⟨hcd, hc⟩)

/-- Every point of `|sd K|` is a positively weighted sum of barycenters over a chain, with the
weights given by its own coordinates. -/
theorem exists_chain_repr_of_mem_sdSpace [Fintype (FaceVertex K)] {x : FaceVertex K → ℝ}
    (hx : x ∈ (barySubdivision K).geometricRealization.space) :
    ∃ T : Finset (FaceVertex K), isChainFaces T ∧ (∀ c ∈ T, 0 < x c) ∧ (∀ c ∉ T, x c = 0) ∧
      sdLinearMap x = ∑ c ∈ T, x c • barycenter c.1 := by
  simp only [SimplicialComplex.mem_space_iff, geometricRealization_faces, Set.mem_image] at hx
  obtain ⟨_, ⟨t, ht, rfl⟩, hxt⟩ := hx
  rw [mem_barySubdivision_iff] at ht
  obtain ⟨w, hw_nn, _, hx_eq⟩ := exists_weights_of_mem_convexHull_faceEmbed hxt
  have hx_apply : ∀ c, x c = if c ∈ t then w c else 0 := by
    intro c
    rw [hx_eq, Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul, vertexEmbed, Pi.single_apply, mul_ite, mul_one,
      mul_zero]
    rw [Finset.sum_ite_eq t c w]
  have hx_nn : ∀ c, 0 ≤ x c := by
    intro c
    rw [hx_apply c]
    split_ifs with h
    · exact hw_nn c h
    · exact le_rfl
  have hzero : ∀ c, c ∉ t.filter (fun c => 0 < x c) → x c = 0 := by
    intro c hc
    by_cases hct : c ∈ t
    · rcases lt_or_eq_of_le (hx_nn c) with hpos | hzero
      · exact absurd (Finset.mem_filter.mpr ⟨hct, hpos⟩) hc
      · exact hzero.symm
    · rw [hx_apply c, if_neg hct]
  have hL : sdLinearMap x = ∑ c ∈ t, x c • barycenter c.1 := by
    have h1 : sdLinearMap x = ∑ c ∈ t, w c • barycenter c.1 := by
      rw [hx_eq]; exact sdLinearMap_apply_sum t w
    rw [h1]
    exact Finset.sum_congr rfl fun c hc => by rw [hx_apply c, if_pos hc]
  refine ⟨t.filter (fun c => 0 < x c), isChainFaces_mono (Finset.filter_subset _ _) ht.2,
    fun c hc => (Finset.mem_filter.mp hc).2, hzero, ?_⟩
  rw [hL]
  refine (Finset.sum_subset (Finset.filter_subset _ _) (fun c _ hcf => ?_)).symm
  rw [hzero c hcf, zero_smul]

/-- `sdRealizeMap` is injective: distinct points of `|sd(K)|` map to distinct points of `|K|`. -/
theorem sdRealizeMap_injective [Fintype (FaceVertex K)] :
    Function.Injective (sdRealizeMap (K := K)) := by
  rintro ⟨x, hx⟩ ⟨x', hx'⟩ hxx'
  have hval : sdLinearMap x = sdLinearMap x' := congrArg Subtype.val hxx'
  obtain ⟨T, hTchain, hTpos, hTzero, hTsum⟩ := exists_chain_repr_of_mem_sdSpace hx
  obtain ⟨T', hT'chain, hT'pos, hT'zero, hT'sum⟩ := exists_chain_repr_of_mem_sdSpace hx'
  have heq : ∑ c ∈ T, x c • barycenter c.1 = ∑ c ∈ T', x' c • barycenter c.1 := by
    rw [← hTsum, ← hT'sum, hval]
  obtain ⟨hTT', hw⟩ := chain_weights_unique T.card rfl hTchain hT'chain hTpos hT'pos heq
  refine Subtype.ext (funext fun c => ?_)
  change x c = x' c
  by_cases hc : c ∈ T
  · exact hw c hc
  · rw [hTzero c hc, hT'zero c (hTT' ▸ hc)]

/-- `sdRealizeMap` is surjective: every point of `|K|` is the image of some point in `|sd(K)|`. -/
theorem sdRealizeMap_surjective [Fintype (FaceVertex K)] :
    Function.Surjective (sdRealizeMap (K := K)) := by
  intro ⟨y, hy⟩
  simp only [SimplicialComplex.mem_space_iff, geometricRealization_faces,
             Set.mem_image] at hy
  obtain ⟨_, ⟨s, hs, rfl⟩, hys⟩ := hy
  obtain ⟨w, hw_nn, hw_sum, hy_eq⟩ := exists_weights_of_mem_convexHull_faceEmbed hys
  obtain ⟨t, μ, ht, hμ_nn, hμ_sum, hμ_eq⟩ :=
    chain_preimage_of_weights s hs w hw_nn hw_sum
  refine ⟨⟨∑ c ∈ t, μ c • vertexEmbed c, weightedSum_mem_sdSpace ht hμ_nn hμ_sum⟩, ?_⟩
  apply Subtype.ext
  change sdLinearMap (∑ c ∈ t, μ c • vertexEmbed c) = y
  rw [sdLinearMap_apply_sum, hμ_eq, ← hy_eq]

/-- `sdRealizeMap` is a homeomorphism: continuous bijection from a compact space to a Hausdorff
space. Compactness of `|sd(K)|` must be supplied as an instance. -/
theorem sdRealizeMap_isHomeomorph [Fintype (FaceVertex K)]
    [CompactSpace (barySubdivision K).geometricRealization.space] :
    IsHomeomorph (sdRealizeMap (K := K)) := by
  rw [isHomeomorph_iff_isEmbedding_surjective]
  exact ⟨(sdRealizeMap.continuous_toFun.isClosedEmbedding sdRealizeMap_injective).isEmbedding,
         sdRealizeMap_surjective⟩

end CombinatorialSimplicialComplex
