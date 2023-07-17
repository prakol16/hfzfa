# Hereditarily Finite Sets with Atoms

This is a Lean implementation of [hereditarily finite sets](https://en.wikipedia.org/wiki/Hereditarily_finite_set) with [atoms](https://en.wikipedia.org/wiki/Urelement).
That is, the type `HFSet atoms` is morally equivalent to the inductive type:

```lean
inductive HFSet (atoms : Type _)
| atom : atoms → HFSet atoms
| ofFinset : Finset (HFSet atoms) → HFSet atoms
```

However, this definition does not quite work because `Finset` is not an inductive type but a quotient of an inductive type, which is not supported by the Lean kernel.

Instead, we take the approach from Mathlib's [implementation of ZF set theory](https://leanprover-community.github.io/mathlib4_docs/Mathlib/SetTheory/ZFC/Basic.html#PSet)
(indeed, this is largely copy-pasted from there with modifications for finiteness and to support atoms) and define a `PreHFSet` which are hereditarily finite lists of atoms, and
quotient by the equivalence relation which forgets their order.

By proving that `∈` is well founded on `HFSet`, we can do recursion just like we would for an inductive datatype. See `Examples.lean` for the definition of `flatten`, which takes
an HFSet (e.g. `{{3, 2}, {4, {5}}, 1}`) and returns the `Finset atoms` of atoms recursively contained in it (`{1, 2, 3, 4, 5}`).
