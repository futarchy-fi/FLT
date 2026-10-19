/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.VeluKernelRationalDegree
public import FLT.Mazur.WeierstrassCoefficientFieldCover

/-!
# The original rational kernel's actual coefficient cover

The existing geometric comparison supplies a faithfully flat effective cover
of the original rational kernel, preserving its original closed inclusion.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry
open FLT.Mazur.WeierstrassIntegralChart

namespace WeierstrassCurve.Velu

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable (E : WeierstrassCurve ℚ) [E.IsElliptic] (p : ℕ) [Fact p.Prime]
  (q : (E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion p →ₗ[ZMod p] ZMod p)
  (hq : Function.Surjective q)
  (hfixed : ∀ g t, q (E.torsionGaloisRepresentation p g t) = q t)

/-- The original geometric kernel's projection to the original rational kernel. -/
def primeRationalKernelCover : (primeKernelClosedSubgroup E p q hq).carrier.left ⟶
    (primeKernelRationalScheme E p q hq hfixed).left :=
  (primeKernelPullbackIso E p q hq hfixed).hom ≫ pullback.snd _ _

/-- This is the actual original coefficient pullback square. -/
theorem primeRationalKernelCover_isPullback :
    IsPullback (primeRationalKernelCover E p q hq hfixed)
      (primeKernelClosedSubgroup E p q hq).carrier.hom
      (primeKernelRationalScheme E p q hq hfixed).hom
      (Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ)))) :=
  primeKernelRationalScheme_isPullback E p q hq hfixed

/-- The original rational and geometric kernel structure maps agree through the cover. -/
@[reassoc] theorem primeRationalKernelCover_base :
    primeRationalKernelCover E p q hq hfixed ≫
        (primeKernelRationalScheme E p q hq hfixed).hom =
      (primeKernelClosedSubgroup E p q hq).carrier.hom ≫
        Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ))) :=
  (primeRationalKernelCover_isPullback E p q hq hfixed).w

/-- The cover retains exactly the original embedded kernel map. -/
@[reassoc] theorem primeRationalKernelCover_inclusion :
    primeRationalKernelCover E p q hq hfixed ≫ primeKernelRationalMap E p q hq hfixed =
      (primeKernelClosedSubgroup E p q hq).inclusion.left ≫ integralCoefficientMorphism E :=
  (primeKernelRationalMap_geometric E p q hq hfixed).symm

/-- Equality of maps out of the original rational kernel is detected by its actual cover. -/
instance primeRationalKernelCover_effectiveEpi :
    EffectiveEpi (primeRationalKernelCover E p q hq hfixed) := by
  have H := (flat_and_surjective_SpecMap_iff
    (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ)))).mpr
      (RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance)
  let _ : Flat (primeRationalKernelCover E p q hq hfixed) :=
    MorphismProperty.of_isPullback
      (primeRationalKernelCover_isPullback E p q hq hfixed).flip H.1
  let _ : Surjective (primeRationalKernelCover E p q hq hfixed) :=
    MorphismProperty.of_isPullback
      (primeRationalKernelCover_isPullback E p q hq hfixed).flip H.2
  let _ : QuasiCompact (primeRationalKernelCover E p q hq hfixed) :=
    MorphismProperty.of_isPullback
      (primeRationalKernelCover_isPullback E p q hq hfixed).flip
      (inferInstanceAs (QuasiCompact
        (Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ))))))
  infer_instance

end WeierstrassCurve.Velu
