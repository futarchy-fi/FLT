/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/

module

public import FLT.FreyCurve.Serre.VeluLocalIntegralSmoothKernelGroup
public import FLT.FreyCurve.Serre.VeluLocalIntegralSmoothKernel
public import FLT.Mazur.WeierstrassClosureSmoothGoodReduction

/-!
# Retaining the original prime kernel operations and good-reduction degree
The integral group recovers the zero and inverse already constructed from the
original quotient. At good reduction its carrier is the entire retained finite
flat degree-p closure. No finiteness is asserted for its bad-reduction open part.
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
local instance integralSmoothKernelRetentionFintype :
    Fintype (show AddSubgroup (EQ).toAffine.Point from GQ) :=
  inferInstanceAs (Fintype (torsionKernel E p q))

variable (V : WeierstrassCurve ℚ)
  (hcurve : V.map (algebraMap ℚ (AlgebraicClosure ℚ)) =
    @curve (AlgebraicClosure ℚ) inferInstance inferInstance
      (E.map (algebraMap ℚ (AlgebraicClosure ℚ))) (torsionKernel E p q)
      (integralSmoothKernelRetentionFintype E p q))
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

local notation "F" => primeIntegralSmoothKernelGroup E p q hp V hcurve hfixed hq W U C D hC hD
local notation "J" =>
  primeIntegralSmoothKernelGroupInclusion E p q hp V hcurve hfixed hq W U C D hC hD

/-- Keep the exact original generic closed immersion visible through its group bundle. -/
local instance integralSmoothKernelRetention_closed : IsClosedImmersion (I).hom.hom.hom.left :=
  inferInstanceAs (IsClosedImmersion iL)

/-- The constructed integral group retains the previously constructed prime zero section. -/
theorem primeIntegralSmoothKernelGroup_zero_retained :
    η[(F).X].left = primeIntegralSmoothKernelZero E p q hp V hcurve hfixed hq W U C D hC hD := by
  apply (cancel_mono (genericClosureSmoothInclusion W iL)).mp
  rw [primeIntegralSmoothKernelZero_inclusion]
  exact congrArg Over.Hom.left (IsMonHom.one_hom (J).hom.hom.hom)

/-- The constructed integral group retains the previously constructed prime inverse. -/
theorem primeIntegralSmoothKernelGroup_negation_retained :
    ι[(F).X].left =
      primeIntegralSmoothKernelNegation E p q hp V hcurve hfixed hq W U C D hC hD := by
  apply (cancel_mono (genericClosureSmoothInclusion W iL)).mp
  rw [primeIntegralSmoothKernelNegation_inclusion]
  exact congrArg Over.Hom.left (GrpObj.inv_hom (J).hom.hom.hom)

/-- The actual integral multiplication recovers the full original generic kernel multiplication. -/
@[reassoc] theorem primeIntegralSmoothKernelGroup_generic_mul :
    genericClosureSmoothPairMap W (primeLocalSource_isElliptic E W C hC).isUnit iL ≫ μ[(F).X].left =
      genericKernelSmoothPairMultiplication W (primeLocalSource_isElliptic E W C hC).isUnit G I ≫
      genericKernelToClosureSmooth W (primeLocalSource_isElliptic E W C hC).isUnit iL := by
  have hd := primeLocalGenericGroupHom_kernel_degree E p q hp V hcurve hfixed hq W U C D hC hD
  let _ : Flat ((I).hom.hom.hom.left ≫ integralCurveStructure (W.map (algebraMap R L))) :=
    hd.2.1
  exact genericClosureSmoothPairMap_multiplication W
      (primeLocalSource_isElliptic E W C hC).isUnit G I

/-- At good reduction, the actual prime smooth kernel has the full original integral degree p. -/
theorem primeIntegralSmoothKernelGroup_degree_goodReduction [IsNoetherianRing R]
    (hW : IsUnit W.Δ) : FLT.Mazur.FCurve.FiniteLocallyFreeDegree (F).X.hom p := by
  exact genericClosureSmoothStructure_degree_goodReduction W iL hW p
    (primeLocalGenericGroupHom_kernel_degree E p q hp V hcurve hfixed hq W U C D hC hD)

end WeierstrassCurve.Velu
