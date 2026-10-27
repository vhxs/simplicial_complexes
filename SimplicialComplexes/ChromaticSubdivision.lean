/-
Copyright (c) 2026 Vikram Saraph. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vikram Saraph
-/
import SimplicialComplexes.Basic

/-!
# Chromatic complexes and the standard chromatic subdivision

A *chromatic* complex is a simplicial complex whose vertices are coloured — in the distributed
computing reading, by process identifiers — so that the vertices of a face carry distinct
colours. The *standard chromatic subdivision* `Chr C` is the complex of one-round immediate
snapshot executions: a vertex is a process `i` together with its *view* `σᵢ`, a face of `C`
containing `i`, and a set of such pairs spans a simplex when the views are totally ordered by
inclusion and satisfy the immediate snapshot condition — if `i` sees `j`, then `i` sees
everything `j` saw.

Unlike barycentric subdivision, `Chr` is colour-preserving, which is what makes it the right
notion for distributed tasks: process identifiers may not be permuted. The colour type is
therefore unchanged by `Chr`, though the vertex type is not, so iteration carries the vertex
type along exactly as `sdIter` does for barycentric subdivision.

## Main definitions

* `ChromaticComplex V Name`: A complex on `V` with a colouring by `Name`, injective on faces.
* `ChrVertex C`: A vertex of the subdivision — a process together with its view.
* `IsChrFace C T`: The ordering and immediate snapshot conditions on a set of such vertices.
* `Chr C`: The standard chromatic subdivision, again a chromatic complex.
* `chrIter C n`, `ChrVertexIter C n`: The `n`-th chromatic subdivision and its vertex type.

## Main results

* `ChrVertex.eq_of_proc_eq`: Within a simplex, a process determines the vertex.
* `col_proc_injOn`: Hence the subdivision is again chromatic.
-/

open Finset Set

universe u v

variable {V : Type u} {Name : Type v}

/-- A simplicial complex whose vertices are coloured by `Name`, with distinct colours on the
vertices of any face. -/
structure ChromaticComplex (V : Type u) (Name : Type v) where
  /-- The underlying simplicial complex. -/
  complex : PreAbstractSimplicialComplex V
  /-- The colouring of the vertices. -/
  col : V → Name
  /-- Vertices of a face have distinct colours. -/
  col_injOn : ∀ s ∈ complex.faces, Set.InjOn col (↑s : Set V)

namespace ChromaticComplex

/-- A vertex of the standard chromatic subdivision: a process together with the view it
obtained, which is a face of the complex containing the process itself. -/
structure ChrVertex (C : ChromaticComplex V Name) : Type u where
  /-- The process this vertex belongs to. -/
  proc : V
  /-- What the process saw. -/
  view : Finset V
  /-- A view is a face of the complex. -/
  view_mem : view ∈ C.complex.faces
  /-- A process sees itself. -/
  proc_mem : proc ∈ view

namespace ChrVertex

variable {C : ChromaticComplex V Name}

@[ext]
theorem ext {a b : ChrVertex C} (hp : a.proc = b.proc) (hv : a.view = b.view) : a = b := by
  cases a; cases b; simp_all

end ChrVertex

/-- The conditions defining a simplex of the standard chromatic subdivision: views are totally
ordered by inclusion, and if one process sees another then it sees all that the other saw. -/
def IsChrFace (C : ChromaticComplex V Name) (T : Finset (ChrVertex C)) : Prop :=
  (∀ a ∈ T, ∀ b ∈ T, a.view ⊆ b.view ∨ b.view ⊆ a.view) ∧
    (∀ a ∈ T, ∀ b ∈ T, b.proc ∈ a.view → b.view ⊆ a.view)

variable {C : ChromaticComplex V Name}

theorem IsChrFace.mono {S T : Finset (ChrVertex C)} (hST : S ⊆ T) (hT : IsChrFace C T) :
    IsChrFace C S :=
  ⟨fun a ha b hb => hT.1 a (hST ha) b (hST hb),
   fun a ha b hb => hT.2 a (hST ha) b (hST hb)⟩

/-- Within a simplex of the subdivision, a process determines the vertex: two vertices with the
same process see each other, so by immediacy their views agree.

This is what makes the subdivision chromatic — one vertex per process in each simplex. -/
theorem ChrVertex.eq_of_proc_eq {T : Finset (ChrVertex C)} (hT : IsChrFace C T)
    {a b : ChrVertex C} (ha : a ∈ T) (hb : b ∈ T) (h : a.proc = b.proc) : a = b := by
  refine ChrVertex.ext h (Finset.Subset.antisymm ?_ ?_)
  · exact hT.2 b hb a ha (h ▸ b.proc_mem)
  · exact hT.2 a ha b hb (h ▸ a.proc_mem)

/-- Vertices of a simplex of the subdivision carry distinct colours: of two such vertices, the
larger view contains both processes, and `C` is chromatic on it. -/
theorem col_proc_injOn {T : Finset (ChrVertex C)} (hT : IsChrFace C T) :
    Set.InjOn (fun a : ChrVertex C => C.col a.proc) (↑T : Set (ChrVertex C)) := by
  intro a ha b hb hcol
  have key : ∀ x y : ChrVertex C, x ∈ T → y ∈ T → x.view ⊆ y.view →
      C.col x.proc = C.col y.proc → x = y := by
    intro x y hx hy hxy hc
    refine ChrVertex.eq_of_proc_eq hT hx hy ?_
    exact C.col_injOn y.view y.view_mem (Finset.mem_coe.mpr (hxy x.proc_mem))
      (Finset.mem_coe.mpr y.proc_mem) hc
  rcases hT.1 a ha b hb with h | h
  · exact key a b ha hb h hcol
  · exact (key b a hb ha h hcol.symm).symm

/-- The **standard chromatic subdivision** of a chromatic complex: the complex of one-round
immediate snapshot executions, again chromatic with the same colours. -/
def Chr (C : ChromaticComplex V Name) : ChromaticComplex (ChrVertex C) Name where
  complex :=
    { faces := {T | T.Nonempty ∧ IsChrFace C T}
      isRelLowerSet_faces := fun {_} h => ⟨h.1, fun _ hST hne => ⟨hne, h.2.mono hST⟩⟩ }
  col a := C.col a.proc
  col_injOn _ hT := col_proc_injOn hT.2

@[simp]
theorem Chr_faces (C : ChromaticComplex V Name) :
    (Chr C).complex.faces = {T | T.Nonempty ∧ IsChrFace C T} := rfl

@[simp]
theorem Chr_col (C : ChromaticComplex V Name) (a : ChrVertex C) :
    (Chr C).col a = C.col a.proc := rfl

theorem mem_Chr_faces_iff {T : Finset (ChrVertex C)} :
    T ∈ (Chr C).complex.faces ↔ T.Nonempty ∧ IsChrFace C T := Iff.rfl

/-- Every pair `(process, view)` is a vertex of the subdivision: a single pair satisfies the
ordering and immediacy conditions trivially. -/
theorem singleton_mem_Chr_faces (a : ChrVertex C) :
    ({a} : Finset (ChrVertex C)) ∈ (Chr C).complex.faces := by
  refine ⟨Finset.singleton_nonempty a, ?_, ?_⟩
  · intro x hx y hy
    rw [Finset.mem_singleton] at hx hy
    subst hx; subst hy
    exact Or.inl (Finset.Subset.refl _)
  · intro x hx y hy _
    rw [Finset.mem_singleton] at hx hy
    subst hx; subst hy
    exact Finset.Subset.refl _

/-! ### Iterated chromatic subdivision -/

/-- The `n`-th chromatic subdivision, carrying its vertex type along. The colour type is fixed
throughout: subdivision never renames processes. -/
def chrIterSigma (C : ChromaticComplex V Name) :
    ℕ → Σ W : Type u, ChromaticComplex W Name
  | 0 => ⟨V, C⟩
  | n + 1 => ⟨ChrVertex (chrIterSigma C n).2, Chr (chrIterSigma C n).2⟩

/-- The vertex type of the `n`-th chromatic subdivision. -/
abbrev ChrVertexIter (C : ChromaticComplex V Name) (n : ℕ) : Type u := (chrIterSigma C n).1

/-- The `n`-th chromatic subdivision of `C`. -/
abbrev chrIter (C : ChromaticComplex V Name) (n : ℕ) :
    ChromaticComplex (ChrVertexIter C n) Name := (chrIterSigma C n).2

@[simp]
theorem chrIter_zero (C : ChromaticComplex V Name) : chrIter C 0 = C := rfl

@[simp]
theorem chrIter_succ (C : ChromaticComplex V Name) (n : ℕ) :
    chrIter C (n + 1) = Chr (chrIter C n) := rfl

end ChromaticComplex
