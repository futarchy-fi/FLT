/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticRetainedTrivializedGeometry
public import FLT.Mazur.EllipticResolvedSmoothPoint
public import FLT.Mazur.EllipticFiniteTensorIndex

/-!
# Arithmetic Laurent charts in the original resolved split fiber

The divided data are constructed from the split-depth hypotheses. Earlier
positive and negative punctures retain the arithmetic trivialization in the
actual final coefficient model, with its original proper specialization.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {K : Type u} [Field K] (A : ValuationSubring K)
  {W : WeierstrassCurve A} {π : A} {depth : ℕ} (D : SplitNodeDepth W π depth)
  (r : (ResidueField A)ˣ) (j : ℕ) (hj0 : 0 < j) (hj : j < depth / 2)
local notation "F" => ResidueField A
local notation "data" => splitResolutionData A D
local notation "hπ" => SplitNodeDepth.uniformizer_ne_zero D
local notation "t" => depth / 2 - (j + 1)
local notation "E" => finiteTensorIndexIso A hπ data F
  (j + 1 + t) (depth / 2) (by omega) (le_refl _) (by omega)

/-- The positive arithmetic puncture in the original final split fiber. -/
def resolvedRetainedPositiveChart : Spec (.of F[T;T⁻¹]) ⟶ resolvedSplitFiber A D :=
  retainedTrivializedPositiveChart A hπ data D r j (by omega) t (by omega)
    (by omega) (by omega) ≫ (E).hom

/-- The negative arithmetic puncture in the original final split fiber. -/
def resolvedRetainedNegativeChart : Spec (.of F[T;T⁻¹]) ⟶ resolvedSplitFiber A D :=
  retainedTrivializedNegativeChart A hπ data D r j (by omega) t (by omega)
    (by omega) (by omega) ≫ (E).hom

instance resolvedRetainedPositiveChart_isOpenImmersion :
    IsOpenImmersion (resolvedRetainedPositiveChart A D r j hj0 hj) :=
  inferInstanceAs (IsOpenImmersion (_ ≫ _))

instance resolvedRetainedNegativeChart_isOpenImmersion :
    IsOpenImmersion (resolvedRetainedNegativeChart A D r j hj0 hj) :=
  inferInstanceAs (IsOpenImmersion (_ ≫ _))

/-- The positive final chart retains the original coefficient projection. -/
@[reassoc] theorem resolvedRetainedPositiveChart_structure :
    resolvedRetainedPositiveChart A D r j hj0 hj ≫ resolvedSplitStructure A D =
      (MultiplicativeGroupScheme.gm F).hom := by
  rw [resolvedRetainedPositiveChart, Category.assoc, resolvedSplitStructure,
    finiteTensorIndexIso_structure, retainedTrivializedPositiveChart_structure]

/-- The negative final chart retains the original coefficient projection. -/
@[reassoc] theorem resolvedRetainedNegativeChart_structure :
    resolvedRetainedNegativeChart A D r j hj0 hj ≫ resolvedSplitStructure A D =
      (MultiplicativeGroupScheme.gm F).hom := by
  rw [resolvedRetainedNegativeChart, Category.assoc, resolvedSplitStructure,
    finiteTensorIndexIso_structure, retainedTrivializedNegativeChart_structure]

variable (c₆ : A) (h6 : W.a₆ = π ^ depth * c₆)
  (P : (W.map (algebraMap A K)).toProjective.Point)
  (v : NodePointCoordinates A W π P) (hv : v.depth = j)
local notation "pt" => Spec.map (CommRingCat.ofHom (AlgHom.toRingHom
  (LaurentUnitPoints.evalUnit (R := F) (nodeTrivializedParameter D c₆ h6 r P))))

include hv in
/-- Positive arithmetic coordinates recover the full original resolved specialization. -/
theorem resolvedRetainedPositiveChart_specialization (hb : v.b ∈ maximalIdeal A) :
    pt ≫ resolvedRetainedPositiveChart A D r j hj0 hj =
      finitePointSpecialization A hπ data (depth / 2) (le_refl _) P := by
  rw [resolvedRetainedPositiveChart, ← Category.assoc,
    finitePointSpecialization_retained_trivialized_positive A hπ data D r j
      (by omega) t (by omega) (by omega) (by omega) c₆ h6 P v
      (by simpa only [zero_add] using hv) hb]
  exact finiteCoefficientPointSection_index A hπ data F _ _ _ _ _ P

include hv in
/-- Negative arithmetic coordinates recover the full original resolved specialization. -/
theorem resolvedRetainedNegativeChart_specialization
    (hr : r ^ depth = nodeWrapParameterUnit D c₆ h6) (hb : IsUnit v.b) :
    pt ≫ resolvedRetainedNegativeChart A D r j hj0 hj =
      finitePointSpecialization A hπ data (depth / 2) (le_refl _) P := by
  rw [resolvedRetainedNegativeChart, ← Category.assoc,
    finitePointSpecialization_retained_trivialized_negative A hπ data D r j
      (by omega) t (by omega) (by omega) (by omega) c₆ h6 P v
      (by simpa only [zero_add] using hv) hr hb]
  exact finiteCoefficientPointSection_index A hπ data F _ _ _ _ _ P

end FLT.Mazur.WeierstrassDividedDepth
