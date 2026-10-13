/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module
public import FLT.Mazur.WeierstrassSplitNormalizationInfinityParameter
public import FLT.Mazur.WeierstrassIntegralZeroSection
public import FLT.Mazur.ProjectiveLineEndpoints
/-!
# The full split infinity parameter is open and contains infinity

The original equation chart retains its zero section in the projective parameter.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Polynomial
open scoped LaurentPolynomial
namespace FLT.Mazur
open WeierstrassIntegralChart ProjectiveLine
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {K : Type u} [Field K] (W : WeierstrassCurve K) (a : Kˣ)
  (he : W = splitNodalEquation a)
/-- The full original split infinity parameter is an open immersion. -/
instance splitEquationInfinityParameter_isOpenImmersion :
    IsOpenImmersion (splitEquationInfinityParameter W a he) := by
  subst W
  change IsOpenImmersion ((splitNodalTorusIso a).inv ≫ infinityTorusChart a)
  infer_instance

/-- The original cubic zero section maps to projective infinity. -/
@[reassoc] theorem splitEquationInfinityParameter_zero :
    Spec.map (CommRingCat.ofHom (chartInfinityEvaluation (S := K) W).toRingHom) ≫
        splitEquationInfinityParameter W a he = infinity K := by
  subst W
  change Spec.map _ ≫ (splitNodalTorusIso a).inv ≫ infinityTorusChart a = _
  change Spec.map _ ≫ Spec.map _ ≫ Spec.map _ ≫ right K = chartZero K ≫ right K
  rw [← Category.assoc, ← Category.assoc]
  apply congrArg (fun f => f ≫ right K)
  rw [chartZero, ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro p
  change chartInfinityEvaluation (splitNodalEquation a)
    (splitNodalLaurentToChart a (infinityTorusMap a p)) = eval 0 p
  have h : (chartInfinityEvaluation (S := K) (splitNodalEquation a)).comp
      ((splitNodalLaurentToChart a).comp (infinityTorusMap a)) = aeval (0 : K) := by
    apply Polynomial.algHom_ext
    simp [AlgHom.comp_apply, infinityTorusMap_X, chartInfinityEvaluation_coord]
  exact DFunLike.congr_fun h p
end FLT.Mazur
