import Mathlib.Data.Finset.Image
import SimplicialComplexes.Basic

/-!
# Simplicial Maps

A simplicial map between combinatorial simplicial complexes is a function on vertices
that sends every face to a face.

## Main definitions

* `SimplicialMap K L`: A simplicial map from `K` to `L`.
* `SimplicialMap.id`: The identity simplicial map.
* `SimplicialMap.comp`: Composition of simplicial maps.

## Main results

* `SimplicialMap.map_vertex`: Simplicial maps preserve vertices.
-/

open Finset

-- `Finset.image` requires `DecidableEq` on the codomain; use classical instances.
set_option linter.style.openClassical false
open Classical

/-- A simplicial map from `K` to `L` is a function on vertices that sends
every face of `K` to a face of `L`. -/
structure SimplicialMap {V W : Type*} (K : CombinatorialSimplicialComplex V)
    (L : CombinatorialSimplicialComplex W) where
  /-- The underlying vertex map. -/
  toFun : V → W
  /-- The image of every face is a face. -/
  map_face : ∀ {s : Finset V}, s ∈ K.faces → s.image toFun ∈ L.faces

namespace SimplicialMap

variable {V W X Y : Type*}
variable {K : CombinatorialSimplicialComplex V}
variable {L : CombinatorialSimplicialComplex W}
variable {M : CombinatorialSimplicialComplex X}
variable {N : CombinatorialSimplicialComplex Y}

instance : FunLike (SimplicialMap K L) V W where
  coe f := f.toFun
  coe_injective f g h := by cases f; cases g; congr

@[ext]
theorem ext {f g : SimplicialMap K L} (h : ∀ v, f v = g v) : f = g :=
  DFunLike.ext f g h

@[simp]
theorem toFun_eq_coe (f : SimplicialMap K L) : f.toFun = f := rfl

/-- A simplicial map sends vertices to vertices. -/
theorem map_vertex (f : SimplicialMap K L) {v : V} (hv : v ∈ K.vertices) :
    f v ∈ L.vertices := by
  rw [CombinatorialSimplicialComplex.mem_vertices] at hv ⊢
  simpa using f.map_face hv

/-- The identity simplicial map. -/
def id (K : CombinatorialSimplicialComplex V) : SimplicialMap K K where
  toFun := _root_.id
  map_face hs := by rwa [Finset.image_id]

@[simp]
theorem id_apply (v : V) : (SimplicialMap.id K) v = v := rfl

/-- Composition of simplicial maps. -/
def comp (g : SimplicialMap L M) (f : SimplicialMap K L) : SimplicialMap K M where
  toFun := g ∘ f
  map_face hs := by
    rw [← Finset.image_image]
    exact g.map_face (f.map_face hs)

@[simp]
theorem comp_apply (g : SimplicialMap L M) (f : SimplicialMap K L) (v : V) :
    g.comp f v = g (f v) := rfl

theorem comp_id (f : SimplicialMap K L) : f.comp (SimplicialMap.id K) = f := by ext; simp

theorem id_comp (f : SimplicialMap K L) : (SimplicialMap.id L).comp f = f := by ext; simp

theorem comp_assoc (h : SimplicialMap M N) (g : SimplicialMap L M) (f : SimplicialMap K L) :
    (h.comp g).comp f = h.comp (g.comp f) := by ext; simp

end SimplicialMap
