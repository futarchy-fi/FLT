/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealAdicRelativeCoefficientLocalization

/-!
# Scalar extension of the actual relative coefficients on principal refinements

The coefficient comparison is an isomorphism over the original relative
restriction. Its pure tensors act on the original restricted coefficients.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open FLT.Mazur.IdealAdicGradedSections
open scoped TensorProduct ChangeOfRings

universe u

namespace FLT.Mazur.IdealAdicGradedPullback

variable {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsAffine Y]
variable (J : Y.IdealSheafData) (f : X ⟶ Y)

attribute [local irreducible] relativeMap relativeRestriction relativeChartScalar

/-- Localization gives scalar extension for the original semilinear module map. -/
def coefficientLocalizationIso {R S : Type u} [CommRing R] [CommRing S]
    (φ : R →+* S) (M : ModuleCat R) (N : ModuleCat S) (r : R)
    (g : M →ₗ[R] (ModuleCat.restrictScalars φ).obj N)
    (hR : let := φ.toAlgebra; IsLocalization.Away r S)
    (hM : IsLocalizedModule.Away r g) : (ModuleCat.extendScalars φ).obj M ≅ N := by
  let := φ.toAlgebra
  let _ : Module S ((ModuleCat.restrictScalars φ).obj N) :=
    inferInstanceAs (Module S N)
  let _ : IsScalarTower R S ((ModuleCat.restrictScalars φ).obj N) :=
    ⟨fun a b n ↦ mul_smul (φ a) b (show N from n)⟩
  let _ := hR
  let _ := hM
  exact (IsLocalizedModule.isBaseChange (.powers r) S g).equiv.toModuleIso

/-- The generic scalar-extension isomorphism uses the original semilinear map on pure tensors. -/
lemma coefficientLocalizationIso_tmul {R S : Type u} [CommRing R] [CommRing S]
    (φ : R →+* S) (M : ModuleCat R) (N : ModuleCat S) (r : R)
    (g : M →ₗ[R] (ModuleCat.restrictScalars φ).obj N)
    (hR : let := φ.toAlgebra; IsLocalization.Away r S)
    (hM : IsLocalizedModule.Away r g) (a : S) (s : M) :
    (coefficientLocalizationIso φ M N r g hR hM).hom (a ⊗ₜ[R,φ] s) =
      a • (show N from g s) := rfl

/-- The actual coefficients on a principal refinement are the original scalar extension. -/
def relativeCoefficientBaseChange (V : X.affineOpens) (r : Γ(X, V.1)) :
    let U : X.affineOpens := ⟨X.basicOpen r, V.2.basicOpen r⟩
    let i : U.1 ⟶ V.1 := homOfLE (X.basicOpen_le r)
    let := closedBaseAlgebra J f V.1
    let := closedBaseAlgebra J f U.1
    (ModuleCat.extendScalars (relativeRestriction J f i).toRingHom).obj
      (relativeChartCoefficient J f V) ≅ relativeChartCoefficient J f U := by
  let U : X.affineOpens := ⟨X.basicOpen r, V.2.basicOpen r⟩
  let i : U.1 ⟶ V.1 := homOfLE (X.basicOpen_le r)
  let := closedBaseAlgebra J f V.1
  let := closedBaseAlgebra J f U.1
  apply coefficientLocalizationIso (relativeRestriction J f i).toRingHom
    (relativeChartCoefficient J f V) (relativeChartCoefficient J f U)
    (relativeChartScalar J f V r) (relativeCoefficientRestrictionLinear J f i)
  · simpa only [relativeChartScalar_apply] using
      relativeRestriction_basicOpen_isLocalization J f V r
  · exact relativeCoefficientRestriction_isLocalized J f V r

/-- Unit tensors retain the original coefficient restriction on the principal refinement. -/
lemma relativeCoefficientBaseChange_one_tmul (V : X.affineOpens) (r : Γ(X, V.1)) :
    let U : X.affineOpens := ⟨X.basicOpen r, V.2.basicOpen r⟩
    let i : U.1 ⟶ V.1 := homOfLE (X.basicOpen_le r)
    let := closedBaseAlgebra J f V.1
    let := closedBaseAlgebra J f U.1
    ∀ s : relativeChartCoefficient J f V,
      (relativeCoefficientBaseChange J f V r).hom
          ((1 : RelativeAlgebra J f U) ⊗ₜ[RelativeAlgebra J f V,
            (relativeRestriction J f i).toRingHom] s) =
        restrictRingHom (J.comap f) U.1 i s := by
  intro U i _ _ s
  have hR : let := (relativeRestriction J f i).toAlgebra
      IsLocalization.Away (relativeChartScalar J f V r) (RelativeAlgebra J f U) := by
    simpa only [relativeChartScalar_apply] using
      relativeRestriction_basicOpen_isLocalization J f V r
  have h := coefficientLocalizationIso_tmul (relativeRestriction J f i).toRingHom
    (relativeChartCoefficient J f V) (relativeChartCoefficient J f U)
    (relativeChartScalar J f V r) (relativeCoefficientRestrictionLinear J f i) hR
    (relativeCoefficientRestriction_isLocalized J f V r) (1 : RelativeAlgebra J f U) s
  exact h.trans (one_smul _ _)

end FLT.Mazur.IdealAdicGradedPullback
