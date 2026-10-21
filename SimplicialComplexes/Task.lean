import SimplicialComplexes.ChromaticSubdivision
import SimplicialComplexes.SimplicialMap

/-!
# Carrier maps, chromatic maps, and tasks

The vocabulary in which distributed tasks are stated. A *carrier map* `Γ` sends each face of a
complex to a subcomplex of another, monotonically: larger faces have more freedom. A *task* is
an input complex, an output complex, and a carrier map saying which outputs are legal for which
inputs. A simplicial map is *carried by* `Γ` when the image of each face lands inside what `Γ`
allows for it.

Maps between chromatic complexes must preserve colours — a process may not adopt another
process's identifier — which is what `ChromaticMap` adds to `SimplicialMap`.

## Main definitions

* `CarrierMap K L`: A monotone map from faces of `K` to subcomplexes of `L`.
* `SimplicialMap.IsCarriedBy`: The image of each face lies in the subcomplex `Γ` allows.
* `ChromaticMap C D`: A colour-preserving simplicial map.
* `Task`: An input complex, an output complex and a carrier map between them.
-/

open Finset Set

universe u v w

namespace PreAbstractSimplicialComplex

variable {V : Type u} {W : Type v}

/-! ### Carrier maps -/

/-- A carrier map from `K` to `L`: each face of `K` is assigned a subcomplex of `L`, and larger
faces are assigned larger subcomplexes. This is the form a task specification takes — `Γ s` is
the set of outputs legal for the input `s`. -/
structure CarrierMap (K : PreAbstractSimplicialComplex V) (L : PreAbstractSimplicialComplex W)
    where
  /-- The subcomplex of `L` carried by a face of `K`. -/
  toFun : Finset V → PreAbstractSimplicialComplex W
  /-- Everything carried lies in `L`. -/
  le_target : ∀ s ∈ K.faces, toFun s ≤ L
  /-- Monotonicity: a larger input face permits everything a smaller one does. -/
  monotone' : ∀ s ∈ K.faces, ∀ t ∈ K.faces, s ⊆ t → toFun s ≤ toFun t

namespace CarrierMap

variable {K : PreAbstractSimplicialComplex V} {L : PreAbstractSimplicialComplex W}

instance : CoeFun (CarrierMap K L) (fun _ => Finset V → PreAbstractSimplicialComplex W) :=
  ⟨CarrierMap.toFun⟩

@[simp]
theorem coe_mk (f) (h₁) (h₂) : ⇑(CarrierMap.mk (K := K) (L := L) f h₁ h₂) = f := rfl

theorem mono (Γ : CarrierMap K L) {s t : Finset V} (hs : s ∈ K.faces) (ht : t ∈ K.faces)
    (hst : s ⊆ t) : Γ s ≤ Γ t := Γ.monotone' s hs t ht hst

end CarrierMap

/-! ### Being carried by a carrier map -/

/-- A simplicial map is *carried by* `Γ` when the image of every face `s` is a face of the
subcomplex `Γ s`. -/
def SimplicialMap.IsCarriedBy [DecidableEq W] {K : PreAbstractSimplicialComplex V}
    {L : PreAbstractSimplicialComplex W} (μ : SimplicialMap K L) (Γ : CarrierMap K L) : Prop :=
  ∀ s ∈ K.faces, s.image μ ∈ (Γ s).faces

end PreAbstractSimplicialComplex

namespace ChromaticComplex

open PreAbstractSimplicialComplex

variable {V : Type u} {W : Type v} {Name : Type w} [DecidableEq W]

/-! ### Chromatic maps -/

/-- A colour-preserving simplicial map between chromatic complexes: process identifiers are
carried along unchanged. -/
structure ChromaticMap (C : ChromaticComplex V Name) (D : ChromaticComplex W Name) where
  /-- The underlying simplicial map. -/
  toSimplicialMap : SimplicialMap C.complex D.complex
  /-- Colours are preserved at every vertex. -/
  col_map : ∀ v ∈ C.complex.vertices, D.col (toSimplicialMap v) = C.col v

namespace ChromaticMap

variable {C : ChromaticComplex V Name} {D : ChromaticComplex W Name}

instance : CoeFun (ChromaticMap C D) (fun _ => V → W) :=
  ⟨fun f => f.toSimplicialMap⟩

@[simp]
theorem coe_toSimplicialMap (f : ChromaticMap C D) (v : V) : f.toSimplicialMap v = f v := rfl

/-- A chromatic map sends vertices to vertices. -/
theorem map_vertex (f : ChromaticMap C D) {v : V} (hv : v ∈ C.complex.vertices) :
    f v ∈ D.complex.vertices :=
  SimplicialMap.map_vertex f.toSimplicialMap hv

end ChromaticMap

/-! ### Tasks -/

/-- A *task*: an input complex, an output complex, and a carrier map specifying which outputs
are legal for which inputs. -/
structure Task (V : Type u) (W : Type v) (Name : Type w) [DecidableEq W] where
  /-- The complex of legal inputs. -/
  input : ChromaticComplex V Name
  /-- The complex of legal outputs. -/
  output : ChromaticComplex W Name
  /-- Which outputs are legal for which inputs. -/
  spec : CarrierMap input.complex output.complex

end ChromaticComplex
