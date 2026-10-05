# Finite ideal images and ampleness descent

This change advances the first remaining W73 item, finite-surjective ampleness
descent (Stacks 0B5V). It does not prove 0B5V or remove `Mazur_statement`.

## Implemented contracts

| Module | Result | Scope |
| --- | --- | --- |
| `FinitePushforwardCoherent` | `finitePushforward_isFinitePresentation` | Finite maps to locally Noetherian schemes preserve coherent module sheaves. |
| `FinitePushforwardIdealImage` | `iso`, `iso_inclusion`, `iso_sections` | The actual ideal-action image of a finite direct image is the direct image of the pulled-back ideal-action image (01YP). |
| `FinitePushforwardIdealVanishing` | `finitePushforward_ideal_ample_coherent_vanishing` | An ample pullback gives eventual positive-cohomology vanishing for all ideal multiples of coherent finite direct images. |
| `IdealPowerGenericComparison` | `exists_reverse_supported` | A generic comparison can be reversed from an actual ideal power; both errors have strictly smaller support. |
| `EventualTwistVanishing` | `middle`, `right`, `retract`, `of_errors` | The vanishing class is closed under extensions, quotients with vanishing kernel, and retracts. |
| `IdealPowerVanishingTransfer` | `eventualTwistVanishing_of_generic_comparison` | Ideal-multiple vanishing transfers across a generic comparison under the smaller-support induction hypothesis. |

Every new module is below the 240-line cap. Only sorted imports are added to
existing Lean sources. Each module has a separate foreground build and lint run;
an audit checks every declaration originating in these modules against the
allowlist `propext`, `Classical.choice`, `Quot.sound`.

## The actual ideal comparison

For a finite morphism `g : Y ⟶ X`, ideal data `I` on `X`, and coherent `M`
on `Y`, the constructed comparison has type

```lean
GlobalIdealPower.multiple I ((Scheme.Modules.pushforward g).obj M) ≅
  (Scheme.Modules.pushforward g).obj
    (GlobalIdealPower.multiple (I.comap g) M)
```

On an affine target open `V`, the preimage is affine. The inclusion on the
source has range `(I.comap g).ideal (g ⁻¹ V) • ⊤`. Pullback of ideal data is
extension along `g.app V`, and `Ideal.smul_restrictScalars` identifies this
range with `I.ideal V • ⊤` on the target. Equality of the two affine images
constructs the global isomorphism. Its composite with the pushed inclusion
is the original inclusion; its maps are not assumed as input.

The source ideal multiple is coherent. The W73 direct-image vanishing theorem
therefore applies to it, and the comparison transports vanishing to the actual
ideal multiple on `X`. One bound works for all positive cohomological degrees
and all sufficiently large twists, for each fixed coefficient and ideal.

## The support-induction direction

Suppose `a : M ⟶ N` is invertible at `x`, and both supports lie in `Z`.
Take the vanishing ideal of the complement of the comparison open of `a`.
Extend the local inverse using `exists_ideal_power_extension`, obtaining

```lean
b : GlobalIdealPower.power I n N ⟶ M
```

The map `b` is invertible at `x`; its kernel and cokernel have support strictly
smaller than `Z`. If smaller-support sheaves and all ideal multiples of `N`
have eventual twist vanishing, the kernel/image and image/cokernel sequences
prove it for `M`. This uses only quotient and extension closure. It never
infers kernel H¹ vanishing from positive-cohomology vanishing of the other terms.

## Remaining proof obligations, in order

1. Finish support dévissage (01YM): use a finite generic rank, descend vanishing
   from a nonempty finite sum by a retraction, and assemble Noetherian support
   induction. The generic comparison transfer is proved; the complete criterion
   from quantified integral-closed-subscheme witnesses is not.
2. Construct 01YO's witnesses for finite surjective maps: choose a point over the
   generic point, push the structure sheaf of its reduced closure, and prove
   exact support and annihilation by the target generic maximal ideal. No
   residue-dimension-one hypothesis is valid for a general finite cover.
3. Apply this to target ideals and finish 0B5V. For the full Noetherian-base
   statement, also extend W73's cohomological ampleness criterion beyond fields.
4. Then 0B5Y, F3 on smooth and polygon fibres, L1–L2 including arbitrary-base
   0D2S approximation, and A7–A8. None is discharged by the present modules.

The build, lint, audit, root-build, and endpoint evidence is recorded in the
untracked W74 handoff and logs, rather than copied here as a current status.
