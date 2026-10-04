/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DivisorClosedCokernel
public import FLT.Mazur.DivisorCohomologicalDegree
public import FLT.Mazur.FiniteSchemeInvertibleSections
public import FLT.Mazur.CurveDivisorLengthSupport
public import FLT.Mazur.ClosedPushforwardCohomology

/-!
# Degree and length of a finite effective Cartier divisor

The canonical cokernel is the closed pushforward of the restricted line.
Affineness of the finite divisor gives positive-degree vanishing. Its line
has a derived tensor inverse, so semilocal freeness computes its H⁰ dimension.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace FLT.Mazur.FCurve

open ModuleSheafTensor

variable {k : Type} [Field k] {X : Scheme}
  (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
  {I : X.IdealSheafData} (hI : EffectiveCartier I) [IsFinite (I.subschemeι ≫ f)]

/-- Pulling back the actual contraction supplies a tensor inverse on the closed divisor. -/
def divisorRestrictedTensorIso :
    tensor ((Scheme.Modules.pullback I.subschemeι).obj (idealModule I))
      ((Scheme.Modules.pullback I.subschemeι).obj (divisorLineBundle I hI)) ≅
      structureModule I.subscheme :=
  (ModuleLineBundleTensorPullback.tensorIso I.subschemeι _ _).symm ≪≫
    (Scheme.Modules.pullback I.subschemeι).mapIso (divisorIdealEvaluationIso hI) ≪≫
    modulePullbackUnitIso I.subschemeι

omit [IsProper f] in
/-- The restricted divisor line has H⁰ dimension equal to the actual finite divisor length. -/
theorem divisorRestricted_h0_finrank :
    Module.finrank k (ModuleScalarH (I.subschemeι ≫ f)
      ((Scheme.Modules.pullback I.subschemeι).obj (divisorLineBundle I hI)) 0) =
        divisorFieldLength f I :=
  finiteScheme_invertible_h0_finrank (I.subschemeι ≫ f) _ _
    (hI.idealModule_locallyFreeRankOne.pullback I.subschemeι)
    (hI.divisorLineBundle_locallyFreeRankOne.pullback I.subschemeι)
    (divisorRestrictedTensorIso hI)

/-- The actual canonical cokernel has no positive-degree cohomology for a finite divisor. -/
theorem finiteDivisor_cokernel_cohomology_subsingleton (n : ℕ) (hn : 0 < n) :
    Subsingleton (ModuleScalarH f (cokernel (divisorSectionMap hI)) n) := by
  have := Chow.source_isNoetherian f
  have : X.IsSeparated := ⟨by rw [← terminal.comp_from f]; infer_instance⟩
  let L := (Scheme.Modules.pullback I.subschemeι).obj (divisorLineBundle I hI)
  have := (hI.divisorLineBundle_locallyFreeRankOne.pullback I.subschemeι).isFinitePresentation
  have : IsAffine I.subscheme := isAffine_of_isAffineHom (I.subschemeι ≫ f)
  have : Subsingleton (ModuleScalarH (I.subschemeι ≫ f) L n) :=
    affine_moduleH_subsingleton L n hn
  let e := ((moduleScalarHFunctor f n).mapIso (divisorCokernelClosedIso hI)).toLinearEquiv
  let d := closedPushforwardScalarHEquiv I.subschemeι L f n
  exact (e.trans d).injective.subsingleton

/-- The canonical cokernel's H⁰ dimension is the actual finite closed-scheme length. -/
theorem finiteDivisor_cokernel_h0_finrank :
    Module.finrank k (ModuleScalarH f (cokernel (divisorSectionMap hI)) 0) =
      divisorFieldLength f I := by
  have := Chow.source_isNoetherian f
  have : X.IsSeparated := ⟨by rw [← terminal.comp_from f]; infer_instance⟩
  let L := (Scheme.Modules.pullback I.subschemeι).obj (divisorLineBundle I hI)
  have := (hI.divisorLineBundle_locallyFreeRankOne.pullback I.subschemeι).isFinitePresentation
  let e := ((moduleScalarHFunctor f 0).mapIso (divisorCokernelClosedIso hI)).toLinearEquiv
  let d := closedPushforwardScalarHEquiv I.subschemeι L f 0
  exact (e.trans d).finrank_eq.trans (divisorRestricted_h0_finrank f hI)

/-- The cohomological degree of O(D) equals the length of its finite effective divisor. -/
theorem divisor_degree_eq_fieldLength :
    curveSheafDegree f (divisorLineBundle I hI) = (divisorFieldLength f I : ℤ) := by
  have := finiteDivisor_cokernel_cohomology_subsingleton f hI 1 (by decide)
  rw [divisor_degree_eq_cokernel_h0 f hI, finiteDivisor_cokernel_h0_finrank f hI]

end FLT.Mazur.FCurve
