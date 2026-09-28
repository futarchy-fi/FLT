# R1i: general Raynaud rigidity is still open

The task is **partial**, not a proof of arbitrary killed-by-three rigidity or
arbitrary three-primary extension. Nothing is pushed.

## New proved work

- `RaynaudClosureFactorization.lean`: a generic factorization of an **already
  integral** morphism through an embedded subgroup extends uniquely to that
  subgroup's flat schematic closure. The factorization induces the prescribed
  generic map. This is proved by killing the closure ideal and descending a
  bialgebra map through its quotient.
- `RaynaudModelArithmetic.lean`: integral zero, addition, and multiplication by
  every natural number, with the expected generic point maps. The existing
  `KilledByPowerOf` predicate is equivalent to integral multiplication vanishing.
- `RaynaudIntegralFiltration.lean`: multiplication maps integrally into the flat
  closure of its generic image **inside the specified model**. The image
  inclusion is a closed immersion, the multiplication-image map is injective
  on coordinate rings and surjective on generic points, and its image has the
  reduced annihilating exponent. The flat torsion closure has the kernel
  universal property against every `FF` test object, both for multiplication
  and for the map to the image closure.
- `RaynaudProductExtension.lean`: every generic morphism from a nonempty finite
  product of order-three models over `ℤ_[3]` extends uniquely to any target.
  The first graph projection is also proved surjective for these sources.
  With `r` factors the source has order `3^r` and is killed by three.
  The factors may differ. No assumption that arbitrary killed-by-three models
  split as products is made.

The new image closure replaces the existential image model for the integral
multiplication map. It does **not** identify that existential model integrally
with the closure.

## Exact remaining gaps

### The killed-by-three arithmetic theorem

For arbitrary `X Y : FF ℤ_[3] ℚ_[3]` with
`∀ x : X.Points, 3 • x = 0` and `∀ y : Y.Points, 3 • y = 0`, and
`f : GenericGaloisHom X Y`, the following still has no proof here:

```lean
Function.Surjective f.graphFst
```

The existing rank-three classification only addresses `Nat.card X.Points = 3`.
Neither it nor the new product theorem decomposes an arbitrary killed-by-three
model into order-three factors. Induction on the exponent cannot avoid this
base case: multiplication by three has zero generic image when the source is
already killed by three, regardless of its rank.

The alternative arithmetic input remains

```lean
Associated (Algebra.discr ℤ_[3] bX) (Algebra.discr ℤ_[3] bG)
```

for integral bases of the source and its graph closure with the same index type.
`GenericGaloisHom.graphFst_surjective_of_discr_associated` would then finish
surjectivity. No new theorem asserts this discriminant association.

### Integral exactness for exponent induction

The new `FF.torsionClosure_kernel` and `FF.multiplyToClosure_kernel` quantify
only over finite flat models. They are not universal properties against all
schemes, and do not identify the entire scheme-theoretic multiplication kernel.
No theorem here proves that this full kernel is flat, or that
`X.multiplyToClosure 3` is faithfully flat. In particular, an injection of
coordinate rings and surjectivity on geometric **generic** points do not imply
faithful flatness over the integral base.

Even after proving the killed-by-three arithmetic theorem, transferring
rigidity through successive integral extensions requires that missing flat
exactness and a descent/lifting argument. Generic kernel/image exactness and
the universal property restricted to `FF` do not establish that transfer.

## Verification

Checked at **2026-09-28 00:21:34 UTC** in `task/r1i`.

- Each of the four new modules passed its targeted `lake build <Module>`.
- All four passed `lake lint -- --no-build <Module>`; the three modules changed
  after the first lint pass also passed a final lint run.
- `lake env lean /tmp/R1iFinalAudit.lean` checked all **42** new named
  declarations (including definitions and the new instance). The output is
  `/tmp/R1i-final-axioms.log`; every dependency set is contained in
  `{propext, Classical.choice, Quot.sound}`.
- The prohibited-token search found no `sorry`, `axiom`, `admit`, or
  `native_decide` in the four new Lean files.
- `git diff --check` passed. `FLT.lean` contains exactly the **639** imports
  corresponding to all 639 files under `FLT/`, sorted in C order.

No full project build was used. The only existing source file changed is the
import list in `FLT.lean`; the preceding worker's proofs are untouched.

To reproduce the Lean checks from the repository root:

```sh
lake build FLT.GroupScheme.RaynaudClosureFactorization FLT.GroupScheme.RaynaudModelArithmetic FLT.GroupScheme.RaynaudIntegralFiltration FLT.GroupScheme.RaynaudProductExtension
lake lint -- --no-build FLT.GroupScheme.RaynaudClosureFactorization FLT.GroupScheme.RaynaudModelArithmetic FLT.GroupScheme.RaynaudIntegralFiltration FLT.GroupScheme.RaynaudProductExtension
lake env lean /tmp/R1iFinalAudit.lean
```
