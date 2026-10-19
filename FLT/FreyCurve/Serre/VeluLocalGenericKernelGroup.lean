/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.VeluLocalGenericKernel
public import FLT.Mazur.WeierstrassIdentityFiberGroup

/-!
# The exact original prime local kernel as a group scheme

The actual original Cartesian identity fiber carries its constructed group
operations. Its carrier, coefficient structure and original inclusion are retained.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
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
local instance localKernelGroupFintype :
    Fintype (show AddSubgroup (EQ).toAffine.Point from GQ) :=
  inferInstanceAs (Fintype (torsionKernel E p q))

variable (V : WeierstrassCurve ℚ)
  (hcurve : V.map (algebraMap ℚ (AlgebraicClosure ℚ)) =
    @curve (AlgebraicClosure ℚ) inferInstance inferInstance
      (E.map (algebraMap ℚ (AlgebraicClosure ℚ))) (torsionKernel E p q)
      (localKernelGroupFintype E p q))
  (hfixed : ∀ g t, q (E.torsionGaloisRepresentation p g t) = q t)
  (hq : Function.Surjective q)

variable {L R : Type} [Field L] [CommRing R] [Algebra ℚ L] [Algebra R L]
  (W U : WeierstrassCurve R) (C D : VariableChange L)
  (hC : C • E.map (algebraMap ℚ L) = W.map (algebraMap R L))
  (hD : D • V.map (algebraMap ℚ L) = U.map (algebraMap R L))


local notation "i" => primeKernelRationalMap E p q hq hfixed
local notation "iL" => localGenericKernelInclusion E W C hC i

local notation "G" => primeLocalGenericGroupHom E p q hp V hcurve hfixed W U C D hC hD
local notation "PB" =>
  primeLocalGenericGroupHom_kernel E p q hp V hcurve hfixed hq W U C D hC hD

/-- The original transported prime kernel with its constructed commutative group operations. -/
def primeLocalGenericKernelGroup : CommGrp (Over (Spec (.of L))) :=
  FLT.Mazur.WeierstrassIdentityFiber.fiberGroup _ _ _ _ G iL PB

/-- The original generic kernel group's carrier is the exact original transported kernel. -/
theorem primeLocalGenericKernelGroup_carrier :
    (primeLocalGenericKernelGroup E p q hp V hcurve hfixed hq W U C D hC hD).X =
      Over.mk (iL ≫ integralCurveStructure (W.map (algebraMap R L))) := rfl

/-- The exact original local prime inclusion as a morphism of commutative group schemes. -/
def primeLocalGenericKernelGroupInclusion :
    primeLocalGenericKernelGroup E p q hp V hcurve hfixed hq W U C D hC hD ⟶
      integralCurveGroup (W.map (algebraMap R L))
        (primeLocalSource_isElliptic E W C hC).isUnit :=
  FLT.Mazur.WeierstrassIdentityFiber.fiberGroupInclusion _ _ _ _ G iL PB

/-- The bundled subgroup inclusion is exactly the original transported prime inclusion. -/
theorem primeLocalGenericKernelGroupInclusion_left :
    (primeLocalGenericKernelGroupInclusion E p q hp V hcurve hfixed hq W U C D
      hC hD).hom.hom.hom.left = iL := rfl

end WeierstrassCurve.Velu
