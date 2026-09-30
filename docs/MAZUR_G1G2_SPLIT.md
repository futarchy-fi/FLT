# First construction leaves after M1-H

Scope: the first three source-lemma leaves toward G1's generalized elliptic
curves. These construct cyclic rotations of a supplied polygon realization.
They do not construct that realization, its smooth locus, or its group scheme.
G2 and A1–A5 remain construction gates; the final paragraph records their order.

Checked 2026-09-30 against the local checkout containing M1-G and M1-H.
Recheck the anchors with `rg -n` for the declaration names below in the named
files; `rg --files FLT/Mazur | rg 'Polygon.*(Rotation|Action)|CyclicPinching'`
found no existing modules for these leaves. The signatures below are proposed
contracts, not typechecked implementations. Caps include headers and helpers.

Source: [DR II.1.1 and II.1.12](https://www.math.uni-bonn.de/people/rapoport/myalggeom/preprints/Lesschemas.pdf),
printed pp. 173 and 178 (PDF pp. 31 and 36); transcriptions and context are in
[DR_SOURCE_LEDGER](DR_SOURCE_LEDGER.md). II.1.1 gives cyclic pinching, while
II.1.12(c) requires rotations of the component graph. The following lemmas
construct the discrete rotations explicitly. They do not identify them with
translations by points of the as-yet-unconstructed smooth group scheme.

Common Lean context (all new names below are in `FLT.Mazur.PolygonPinching`):

```lean
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
variable (K : Type) [Field K] {n : ℕ} [NeZero n]
variable (hn : 0 < n)
```

## R1 — equivariant cyclic pinching span, cap 350, ready

New `FLT/Mazur/CyclicPinchingRotation.lean`; import `PolygonPinchingDiagram`
and `Mathlib.Data.ZMod.Basic`. Construct, rather than assume, these maps:

```lean
def rotateIndex (a : ZMod n) (i : Fin n) : Fin n :=
  (ZMod.finEquiv n).symm (ZMod.finEquiv n i + a)
def componentsRotation (a : ZMod n) : components K n ⟶ components K n
def branchesRotation (a : ZMod n) : branches K n ⟶ branches K n
def nodesRotation (a : ZMod n) : nodes K n ⟶ nodes K n
theorem rotateIndex_next (a : ZMod n) (i : Fin n) :
    rotateIndex a (next hn i) = next hn (rotateIndex a i)
theorem componentι_rotation (a : ZMod n) (i : Fin n) :
    componentι K n i ≫ componentsRotation K a =
      componentι K n (rotateIndex a i)
theorem branchι_rotation (a : ZMod n) (i : Fin n) (b : Bool) :
    branchι K n i b ≫ branchesRotation K a =
      branchι K n (rotateIndex a i) b
theorem nodeι_rotation (a : ZMod n) (i : Fin n) :
    nodeι K n i ≫ nodesRotation K a = nodeι K n (rotateIndex a i)
theorem rotation_toComponents (a : ZMod n) :
    branchesRotation K a ≫ toComponents K n hn =
      toComponents K n hn ≫ componentsRotation K a
theorem rotation_toNodes (a : ZMod n) :
    branchesRotation K a ≫ toNodes K n =
      toNodes K n ≫ nodesRotation K a
```

Also prove zero and addition laws for all three maps; for example:
`componentsRotation K (a + b) = componentsRotation K a ≫ componentsRotation K b`.
Use `Sigma.desc` with the displayed inclusions, leaving the Boolean branch
label unchanged. Commutation with `next` is essential at infinity; permutation
of components alone does not define a map of the pinching span.

Anchors: `PolygonPinching.{next,toComponents,toNodes}` and
`branchι_toComponents_zero`, `branchι_toComponents_infinity`, `branchι_toNodes`
in `FLT/Mazur/PolygonPinchingDiagram.lean`; `ZMod.finEquiv`, `ZMod.val_add`
in Mathlib `Data/ZMod/Basic.lean`; `Sigma.desc`, `Sigma.ι_comp_desc`,
`Sigma.hom_ext` in Mathlib `CategoryTheory/Limits/Shapes/Products.lean`.
Source: the explicit cyclic identifications in DR II.1.1.
Unblocks R2. Include `n = 1` in checks; do not impose `1 < n`.

## R2 — rotations on a realized polygon, cap 250, after R1

New `FLT/Mazur/NeronPolygonRotation.lean`; import R1 and `NeronPolygonPredicate`.
Retain a specified pushout cocone, so the construction preserves its marking:

```lean
variable {C : Over (Spec (CommRingCat.of K))}
variable (p : components K n ⟶ C) (q : nodes K n ⟶ C)
variable (h : IsPushout (toComponents K n hn) (toNodes K n) p q)
def polygonRotation (a : ZMod n) : C ⟶ C
theorem components_polygonRotation (a : ZMod n) :
    p ≫ polygonRotation K hn p q h a = componentsRotation K a ≫ p
theorem nodes_polygonRotation (a : ZMod n) :
    q ≫ polygonRotation K hn p q h a = nodesRotation K a ≫ q
theorem polygonRotation_zero : polygonRotation K hn p q h 0 = 𝟙 C
theorem polygonRotation_add (a b : ZMod n) :
    polygonRotation K hn p q h (a + b) =
      polygonRotation K hn p q h a ≫ polygonRotation K hn p q h b
def polygonRotationIso (a : ZMod n) : C ≅ C
```

Define the map by `h.desc (componentsRotation K a ≫ p)
(nodesRotation K a ≫ q)` using R1 and `h.w`. Prove the two laws by
`h.hom_ext`; use rotation by `-a` for the inverse. Expose the iso's hom as
the constructed map. No global `HasPushout` instance may be assumed or added.

Anchors: `IsPushout.desc`, `inl_desc`, `inr_desc`, `hom_ext` in Mathlib
`CategoryTheory/Limits/Shapes/Pullback/IsPullback/Defs.lean`;
`IsNeronNGon` in `FLT/Mazur/NeronPolygonPredicate.lean` supplies precisely
this cocone. Source: cyclic symmetry of DR II.1.1's quotient construction.
Unblocks R3. Acceptance includes the two normalization/node equations, not
only existence of an abstract automorphism.

## R3 — component rotations and natural action on points, cap 250, after R2

New `FLT/Mazur/NeronPolygonRotationAction.lean`; import R2.
Keep R2's `C,p,q,h` context and define postcomposition on scheme-valued points:

```lean
def rotatePoint (a : ZMod n) {U : Over (Spec (CommRingCat.of K))}
    (x : U ⟶ C) : U ⟶ C := x ≫ polygonRotation K hn p q h a
theorem rotatePoint_zero {U : Over (Spec (CommRingCat.of K))} (x : U ⟶ C) :
    rotatePoint K hn p q h 0 x = x
theorem rotatePoint_add (a b : ZMod n)
    {U : Over (Spec (CommRingCat.of K))} (x : U ⟶ C) :
    rotatePoint K hn p q h (a + b) x =
      rotatePoint K hn p q h b (rotatePoint K hn p q h a x)
theorem rotatePoint_precomp (a : ZMod n)
    {U V : Over (Spec (CommRingCat.of K))} (v : V ⟶ U) (x : U ⟶ C) :
    rotatePoint K hn p q h a (v ≫ x) =
      v ≫ rotatePoint K hn p q h a x
theorem componentι_polygonRotation (a : ZMod n) (i : Fin n) :
    componentι K n i ≫ p ≫ polygonRotation K hn p q h a =
      componentι K n (rotateIndex a i) ≫ p
```

Also expose the corresponding equation for `nodeι`, and prove every
`rotatePoint ... a` is bijective using `-a`. These give an actual natural
cyclic action and show its permutation of the marked normalization components.
They do not assert that the markings are irreducible components without a
separate theorem identifying the normalization and dual graph.

Anchors: R1/R2 equations and `Category.assoc`; no new geometric existence
theorem is hidden in this leaf. Source: the rotations used in DR II.1.12(c).
Unblocks comparison with the component action of a future generalized curve.

## Acceptance and subsequent gates

For each leaf: foreground `LEAN_NUM_THREADS=2 lake build MODULE`, then
`LEAN_NUM_THREADS=2 lake exe runLinter MODULE`, then `#print axioms` on every
new theorem. Require only `propext`, `Classical.choice`, `Quot.sound`; no
`sorry`, new axioms, or arithmetic conclusions assumed as record fields.
Register imports in C-sort order in `FLT.lean`. If a cap fails, preserve proved
lemmas and return the exact remaining statement with a smaller split.

These are the first G1 construction leaves, not a subdivision of all Mazur.
Next split polygon existence/genus and the relative smooth group/action,
then ample finite locally free cyclic level structures, before coarse moduli
and cusps. G2 still needs Picard/Jacobian construction, Hecke correspondences,
the completion-kernel quotient and arithmetic finiteness. Do not redispatch
the already-proved `GenericFibers` finite-fiber consumers. A1 (Néron models
and finite-flat rigidity) can be split independently; A2 requires G1/G2 and
odd torsion specialization; A3–A4 require local splitting and the sourced
Herbrand input; A5 requires geometric isogenies and the coarse-point/twist
finiteness argument. None is discharged by these three rotation lemmas.
