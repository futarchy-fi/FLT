/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/

module

public import FLT.FreyCurve.Serre.VeluLocalGenericKernelGroup
public import FLT.Mazur.WeierstrassClosureSmoothGroup

/-!
# The original prime kernel's integral smooth subgroup
Apply dense multiplication descent to the actual original local quotient kernel.
The group carrier and closed inclusion are the original smooth intersection;
the separate full finite flat closure remains unchanged.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
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
local instance integralSmoothKernelGroupFintype :
    Fintype (show AddSubgroup (EQ).toAffine.Point from GQ) :=
  inferInstanceAs (Fintype (torsionKernel E p q))

variable (V : WeierstrassCurve ℚ)
  (hcurve : V.map (algebraMap ℚ (AlgebraicClosure ℚ)) =
    @curve (AlgebraicClosure ℚ) inferInstance inferInstance
      (E.map (algebraMap ℚ (AlgebraicClosure ℚ))) (torsionKernel E p q)
      (integralSmoothKernelGroupFintype E p q))
  (hfixed : ∀ g t, q (E.torsionGaloisRepresentation p g t) = q t)
  (hq : Function.Surjective q)

variable {L R : Type} [Field L] [CommRing R] [Algebra ℚ L] [Algebra R L]
  (W U : WeierstrassCurve R) (C D : VariableChange L)
  (hC : C • E.map (algebraMap ℚ L) = W.map (algebraMap R L))
  (hD : D • V.map (algebraMap ℚ L) = U.map (algebraMap R L))

local notation "i" => primeKernelRationalMap E p q hq hfixed
local notation "iL" => localGenericKernelInclusion E W C hC i

variable [IsFractionRing R L] [IsDomain R] [ValuationRing R]

local notation "G" => primeLocalGenericKernelGroup E p q hp V hcurve hfixed hq W U C D hC hD
local notation "I" =>
  primeLocalGenericKernelGroupInclusion E p q hp V hcurve hfixed hq W U C D hC hD

/-- The actual original prime kernel's smooth intersection is an integral commutative group. -/
def primeIntegralSmoothKernelGroup : CommGrp (Over (Spec (.of R))) := by
  have hd := primeLocalGenericGroupHom_kernel_degree E p q hp V hcurve hfixed hq W U C D hC hD
  let _ : IsClosedImmersion (I).hom.hom.hom.left :=
    inferInstanceAs (IsClosedImmersion iL)
  let _ : Flat ((I).hom.hom.hom.left ≫ integralCurveStructure (W.map (algebraMap R L))) :=
    hd.2.1
  exact genericClosureSmoothGroup W (primeLocalSource_isElliptic E W C hC).isUnit G I

/-- The group retains the original smooth intersection and original coefficient structure. -/
theorem primeIntegralSmoothKernelGroup_carrier :
    (primeIntegralSmoothKernelGroup E p q hp V hcurve hfixed hq W U C D hC hD).X =
      Over.mk (genericClosureSmoothStructure W iL) := rfl

/-- The exact original smooth inclusion is a morphism of integral commutative groups. -/
def primeIntegralSmoothKernelGroupInclusion :
    primeIntegralSmoothKernelGroup E p q hp V hcurve hfixed hq W U C D hC hD ⟶
      integralSmoothGroup W := by
  have hd := primeLocalGenericGroupHom_kernel_degree E p q hp V hcurve hfixed hq W U C D hC hD
  let _ : IsClosedImmersion (I).hom.hom.hom.left :=
    inferInstanceAs (IsClosedImmersion iL)
  let _ : Flat ((I).hom.hom.hom.left ≫ integralCurveStructure (W.map (algebraMap R L))) :=
    hd.2.1
  exact genericClosureSmoothGroupInclusion W (primeLocalSource_isElliptic E W C hC).isUnit G I

/-- The bundled inclusion is exactly the original closed smooth inclusion. -/
theorem primeIntegralSmoothKernelGroupInclusion_left :
    (primeIntegralSmoothKernelGroupInclusion E p q hp V hcurve hfixed hq W U C D
      hC hD).hom.hom.hom.left = genericClosureSmoothInclusion W iL := rfl

/-- Multiplication on the actual prime smooth kernel is the original ambient smooth addition. -/
@[reassoc] theorem primeIntegralSmoothKernelGroup_mul_inclusion :
    μ[(primeIntegralSmoothKernelGroup E p q hp V hcurve hfixed hq W U C D hC hD).X].left ≫
      genericClosureSmoothInclusion W iL =
        genericClosureSmoothAmbientPair W iL ≫ smoothFactorAddition W := by
  have hd := primeLocalGenericGroupHom_kernel_degree E p q hp V hcurve hfixed hq W U C D hC hD
  let _ : IsClosedImmersion (I).hom.hom.hom.left :=
    inferInstanceAs (IsClosedImmersion iL)
  let _ : Flat ((I).hom.hom.hom.left ≫ integralCurveStructure (W.map (algebraMap R L))) :=
    hd.2.1
  exact genericClosureSmoothMultiplication_inclusion W
      (primeLocalSource_isElliptic E W C hC).isUnit G I

end WeierstrassCurve.Velu
