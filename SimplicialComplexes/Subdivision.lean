/-
Copyright (c) 2026 Vikram Saraph. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vikram Saraph
-/
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
import SimplicialComplexes.Task

/-!
# Subdivisions, via carriers

A subdivision of `K` is usually defined geometrically: a complex `D` with `|D| = |K|` such that
every simplex of `D` lies in a unique minimal simplex of `K`. That minimal simplex is the
*carrier*, and essentially every argument about subdivisions is conducted through it rather
than through the homeomorphism.

This file takes the carrier as the definition. A `Subdivision D K` is a monotone assignment of
a face of `K` to each face of `D`; a `ChromaticSubdivision` additionally requires that the
colours occurring in a face already occur in its carrier. A simplicial map out of `D` is
*carried by* a carrier map `Γ` on `K` when the image of each face `t` lands in `Γ (carrier t)`.

**This is weaker than the geometric notion**, deliberately. It supports the statements and
arguments we need without putting `|Chr σ| ≅ |σ|` — which is Kozlov's theorem, proved via
Schlegel diagrams, with no polytope theory in Mathlib to build on — on the critical path. A
geometric condition can be added as a separate field or hypothesis if something needs it. Note
in particular that nothing here forces `D` to cover `K`, so statements quantifying over "some
subdivision" are weaker than their geometric counterparts.

## Main definitions

* `Subdivision D K`: A monotone carrier assignment from faces of `D` to faces of `K`.
* `ChromaticSubdivision E C`: The same between chromatic complexes, preserving colours.
* `Subdivision.IsCarriedBy`: A map out of `D` respects a carrier map on `K`.

## Main results

* `chrSubdivision`: The standard chromatic subdivision is a chromatic subdivision in this
  sense, with the carrier of a simplex given by the union of its views.
-/

open Finset Set

universe u v w

namespace PreAbstractSimplicialComplex

variable {V : Type u} {W : Type v}

/-- A subdivision of `K` by `D`, recorded through its carrier: each face of `D` is assigned a
face of `K`, monotonically. -/
structure Subdivision (D : PreAbstractSimplicialComplex W) (K : PreAbstractSimplicialComplex V)
    where
  /-- The minimal face of `K` containing a given face of `D`. -/
  carrier : Finset W → Finset V
  /-- Carriers are faces. -/
  carrier_mem : ∀ t ∈ D.faces, carrier t ∈ K.faces
  /-- Larger faces have larger carriers. -/
  carrier_mono : ∀ t ∈ D.faces, ∀ t' ∈ D.faces, t ⊆ t' → carrier t ⊆ carrier t'

namespace Subdivision

variable {D : PreAbstractSimplicialComplex W} {K : PreAbstractSimplicialComplex V}

/-- A simplicial map out of a subdivision is *carried by* `Γ` when the image of each face lies
in the subcomplex that `Γ` allows for its carrier. This is the notion the asynchronous
computability theorem uses. -/
def IsCarriedBy {X : Type w} [DecidableEq X] {L : PreAbstractSimplicialComplex X}
    (S : Subdivision D K) (μ : SimplicialMap D L) (Γ : CarrierMap K L) : Prop :=
  ∀ t ∈ D.faces, t.image μ ∈ (Γ (S.carrier t)).faces

end Subdivision

end PreAbstractSimplicialComplex

namespace ChromaticComplex

open PreAbstractSimplicialComplex

variable {V : Type u} {W : Type v} {Name : Type w}

/-- A chromatic subdivision: a subdivision whose colours already occur in the carrier. -/
structure ChromaticSubdivision (E : ChromaticComplex W Name) (C : ChromaticComplex V Name)
    extends Subdivision E.complex C.complex where
  /-- Every colour occurring in a face occurs already in its carrier. -/
  col_carrier : ∀ t ∈ E.complex.faces, ∀ v ∈ t, ∃ u ∈ carrier t, C.col u = E.col v

/-! ### The standard chromatic subdivision is one -/

section Chr

variable [DecidableEq V] {C : ChromaticComplex V Name}

omit [DecidableEq V] in
/-- In a simplex of `Chr C` the views are totally ordered, so one of them contains the rest. -/
theorem IsChrFace.exists_max_view {T : Finset (ChrVertex C)} (hT : IsChrFace C T)
    (hne : T.Nonempty) : ∃ a ∈ T, ∀ b ∈ T, b.view ⊆ a.view := by
  obtain ⟨a, ha, hmax⟩ := T.exists_max_image (fun x => x.view.card) hne
  refine ⟨a, ha, fun b hb => ?_⟩
  rcases hT.1 b hb a ha with h | h
  · exact h
  · exact le_of_eq (Finset.eq_of_subset_of_card_le h (hmax b hb)).symm

/-- The carrier of a simplex of `Chr C`: the union of the views of its vertices, which by
total ordering is the largest of them. -/
theorem IsChrFace.sup_view_mem {T : Finset (ChrVertex C)} (hT : IsChrFace C T)
    (hne : T.Nonempty) : T.sup (fun a => a.view) ∈ C.complex.faces := by
  obtain ⟨a, ha, hle⟩ := hT.exists_max_view hne
  have : T.sup (fun a => a.view) = a.view :=
    le_antisymm (Finset.sup_le fun b hb => hle b hb) (Finset.le_sup ha)
  rw [this]
  exact a.view_mem

/-- **The standard chromatic subdivision is a chromatic subdivision**, with the carrier of a
simplex given by the union of the views of its vertices. -/
def chrSubdivision (C : ChromaticComplex V Name) : ChromaticSubdivision (Chr C) C where
  carrier t := t.sup (fun a => a.view)
  carrier_mem _ ht := ht.2.sup_view_mem ht.1
  carrier_mono _ _ _ _ htt' := Finset.sup_mono htt'
  col_carrier _ _ v hv := ⟨v.proc, Finset.mem_of_subset (Finset.le_sup hv) v.proc_mem, rfl⟩

@[simp]
theorem chrSubdivision_carrier (C : ChromaticComplex V Name) (t : Finset (ChrVertex C)) :
    (chrSubdivision C).carrier t = t.sup (fun a => a.view) := rfl

end Chr

end ChromaticComplex
