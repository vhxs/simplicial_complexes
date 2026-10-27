# SimplicialComplexes

Combinatorial and geometric simplicial complexes in Lean 4, built on Mathlib.

The main result is the **simplicial approximation theorem**, which is not in Mathlib: every
continuous map between the geometric realizations of finite simplicial complexes is homotopic
to the realization of a simplicial map defined on an iterated barycentric subdivision.

Everything builds with no `sorry`, and the main results depend on no axioms beyond
`propext`, `Classical.choice` and `Quot.sound`.

## Main results

```lean
theorem exists_homotopy_of_fintype [Fintype V] [Fintype W] [Nonempty W]
    {K : PreAbstractSimplicialComplex V} {L : PreAbstractSimplicialComplex W}
    (f : C(K.geometricRealization.space, L.geometricRealization.space)) :
    ∃ (n : ℕ) (g : SimplicialMap (sdComplex K n) L),
      Nonempty (ContinuousMap.Homotopy
        (g.realizeMap.comp (sdRealizeIterSymmCM K n)) f)
```

Along the way:

| Result | File |
| --- | --- |
| `geometricRealization` as a `Geometry.SimplicialComplex`, and `\|K\|` compact | `GeometricRealization.lean` |
| `sdRealizeMap_isHomeomorph` — `\|sd K\| ≅ \|K\|` | `BarycentricSubdivision.lean` |
| Open stars and the carrier of a point | `Star.lean` |
| Centroid shrinkage: `‖q - centroid p s‖ ≤ (1 - 1/n)·diam` | `Mesh.lean` |
| Iterated subdivision, `diam ≤ (1 - 1/N)^n·m`, `\|sd^n K\| ≅ \|K\|` | `IteratedSubdivision.lean` |
| The star condition, the theorem, and the straight-line homotopy | `SimplicialApproximation.lean` |

The development builds on Mathlib's `PreAbstractSimplicialComplex` and produces Mathlib's
`Geometry.SimplicialComplex`, so it composes with the existing library rather than duplicating
it.

### Scope and caveats

* **Finite complexes only.** Both vertex types are assumed finite. The classical theorem needs
  only `K` finite; the extra `[Fintype W]` comes from `SimplicialMap.realizeMap` being built on
  `FunOnFinite.linearMap`, not from the mathematics.
* `[Nonempty W]` excludes only the degenerate case where `L` has no faces and `|L|` is empty.
* The theorem is stated for `K.geometricRealization`, the canonical placement of an abstract
  complex at standard basis vectors. Transferring it to an arbitrary geometric complex in `ℝⁿ`
  is not formalized.

## Work in progress: towards the asynchronous computability theorem

The following is **groundwork, not a proof of the ACT**. It defines the vocabulary and the
standard chromatic subdivision; the substantial theorems are not done.

| Content | File |
| --- | --- |
| Chromatic complexes, `Chr`, iterated `Chr` | `ChromaticSubdivision.lean` |
| Carrier maps, chromatic maps, tasks | `Task.lean` |
| Subdivisions via carriers; `Chr` is one | `Subdivision.lean` |
| Links, skeleta, purity | `Basic.lean` |

Known gaps in this part:

* `|Chr σ| ≅ |σ|` (Kozlov) is not proved. His argument is geometric, via Schlegel diagrams, and
  Mathlib has no polytope theory.
* `Subdivision` is axiomatized by its carrier map and does **not** require `|D| = |K|`, so
  statements quantifying over "some subdivision" are weaker than their geometric counterparts.
* Solvability is not defined operationally — there is no model of wait-free shared memory here.
  Stating the ACT itself requires one, since with solvability defined combinatorially the
  theorem is a tautology.

## Building

```sh
lake exe cache get   # fetch Mathlib's prebuilt oleans
lake build
```

Pinned to Lean and Mathlib `v4.35.0` (see `lean-toolchain` and `lakefile.toml`).

## References

* J. R. Munkres, *Elements of Algebraic Topology* — simplicial approximation.
* M. Herlihy, D. Kozlov, S. Rajsbaum, *Distributed Computing Through Combinatorial Topology*.
* D. N. Kozlov, *Chromatic subdivision of a simplicial complex*, Homology, Homotopy and
  Applications **14** (2012), no. 2.
* V. Saraph, M. Herlihy, E. Gafni, *An Algorithmic Approach to the Asynchronous Computability
  Theorem*, [arXiv:1703.08525](https://arxiv.org/abs/1703.08525).
