/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.VeluLocalGenericMorphism
public import FLT.FreyCurve.Serre.VeluPrimeRationalKernel
public import FLT.Mazur.WeierstrassLocalGenericKernel

/-!
# The original rational closed kernel on the specified local generic source

The actual rational inclusion is pulled back along the exact local coordinate
projection. It is closed and is the entire Cartesian identity fiber of the
actual local prime quotient, retaining the exact prime degree.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry
open FLT.Mazur.WeierstrassIntegralChart

namespace WeierstrassCurve.Velu

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable (E : WeierstrassCurve ℚ) [E.IsElliptic] (p : ℕ) [Fact p.Prime]
  (q : (E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion p →ₗ[ZMod p] ZMod p)
  [Fintype (torsionKernel E p q)] (hp : Odd p)

local notation "EQ" => E.map (algebraMap ℚ (AlgebraicClosure ℚ))
local notation "GQ" => torsionKernel E p q

/-- Retain the same enumeration of the original geometric kernel. -/
local instance localGenericKernelFintype :
    Fintype (show AddSubgroup (EQ).toAffine.Point from GQ) :=
  inferInstanceAs (Fintype (torsionKernel E p q))

variable (V : WeierstrassCurve ℚ)
  (hcurve : V.map (algebraMap ℚ (AlgebraicClosure ℚ)) =
    @curve (AlgebraicClosure ℚ) inferInstance inferInstance
      (E.map (algebraMap ℚ (AlgebraicClosure ℚ))) (torsionKernel E p q)
      (localGenericKernelFintype E p q))
  (hfixed : ∀ g t, q (E.torsionGaloisRepresentation p g t) = q t)
  (hq : Function.Surjective q)

variable {L R : Type} [Field L] [CommRing R] [Algebra ℚ L] [Algebra R L]
  (W U : WeierstrassCurve R) (C D : VariableChange L)
  (hC : C • E.map (algebraMap ℚ L) = W.map (algebraMap R L))
  (hD : D • V.map (algebraMap ℚ L) = U.map (algebraMap R L))

local notation "i" => primeKernelRationalMap E p q hq hfixed
local notation "iL" => localGenericKernelInclusion E W C hC i
local notation "kL" => iL ≫ integralCurveStructure (W.map (algebraMap R L))
local notation "G" => primeLocalGenericGroupHom E p q hp V hcurve hfixed W U C D hC hD

/-- The original rational closed kernel is exactly the full local Cartesian identity fiber. -/
theorem primeLocalGenericGroupHom_kernel :
    IsPullback iL kL (G).hom.hom.hom.left (integralCurveZero (U.map (algebraMap R L))) := by
  apply localGenericKernel_identityFiber E V W U C D hC hD i
    (primeKernelRationalScheme E p q hq hfixed).hom
    (primeKernelRationalMap_base E p q hq hfixed)
    (primeRationalMorphism E p q hp V hcurve hfixed) (G).hom.hom.hom.left
    (primeLocalGenericGroupHom E p q hp V hcurve hfixed W U C D hC hD).hom.hom.hom.w
  · simpa only [localGenericProjection, Category.assoc] using
      primeLocalGenericGroupHom_rational_square E p q hp V hcurve hfixed W U C D hC hD
  · exact primeRationalMorphism_kernel E p q hp V hcurve hfixed hq

include hp hcurve hD in
/-- The transported original kernel still has the full prime rank over the local field. -/
theorem primeLocalGenericGroupHom_kernel_degree :
    FLT.Mazur.FCurve.FiniteLocallyFreeDegree kL p :=
  FLT.Mazur.FCurve.finiteLocallyFreeDegree_of_isPullback
    (primeLocalGenericGroupHom_kernel E p q hp V hcurve hfixed hq W U C D hC hD) p
    (primeLocalGenericGroupHom_degree E p q hp V hcurve hfixed W U C D hC hD hq)

end WeierstrassCurve.Velu
