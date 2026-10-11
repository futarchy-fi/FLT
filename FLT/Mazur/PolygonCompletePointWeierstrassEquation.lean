/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompletePointCubicRelation
public import FLT.Mazur.WeightedPoleCubicNormalization

/-!
# A normalized Weierstrass equation on the original point complement

The nonzero x³ coefficient simultaneously rescales the two original
functions. The resulting actual functions satisfy the Weierstrass equation
over the specified base field, in every characteristic.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
open FCurve
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
  (L : Type) [Field L] {Y : Scheme}
  (s : Spec (.of L) ⟶ Spec (.of (PowerSeries K)))
  (p : Y ⟶ exactVeroneseProj K n h) (q : Y ⟶ Spec (.of L))
  (hs : IsPullback p q (exactVeroneseProjToBase K n h) s)

/-- Scalars on the actual marked-point complement come from its base morphism. -/
def completeCartesianPointScalar (i : Fin n) :
    L →+* Γ((completeCartesianPointComplement K n h L s p q hs i).toScheme, ⊤) :=
  structureScalarMap ((completeCartesianPointComplement K n h L s p q hs i).ι ≫ q)

/-- The Weierstrass coefficients obtained from the actual degree-six relation. -/
def completeCartesianPointWeierstrass (i : Fin n) : WeierstrassCurve L :=
  WeightedPoleMonomials.cubicCurve (completeCartesianPointCubicCoefficients K n h L s p q hs i)

/-- Simultaneously rescale an original function by the nonzero cubic leading coefficient. -/
def completeCartesianPointNormalize (i : Fin n)
    (z : Γ((completeCartesianPointComplement K n h L s p q hs i).toScheme, ⊤)) :
    Γ((completeCartesianPointComplement K n h L s p q hs i).toScheme, ⊤) :=
  completeCartesianPointScalar K n h L s p q hs i
    (completeCartesianPointCubicCoefficients K n h L s p q hs i (Fin.last 5)) * z

/-- The normalization preserves equality of actual functions. -/
theorem completeCartesianPointNormalize_injective (i : Fin n) :
    Function.Injective (completeCartesianPointNormalize K n h L s p q hs i) :=
  WeightedPoleMonomials.scaled_coordinates_injective
    (completeCartesianPointScalar K n h L s p q hs i) _
    (completeCartesianPointCubicCoefficients_last_ne_zero K n h L s p q hs i)

/-- The normalized original functions satisfy the actual base-field Weierstrass equation. -/
theorem completeCartesianPoint_weierstrassEquation (i : Fin n) :
    ((completeCartesianPointWeierstrass K n h L s p q hs i).map
      (completeCartesianPointScalar K n h L s p q hs i)).toAffine.Equation
      (completeCartesianPointNormalize K n h L s p q hs i
        (completeCartesianPointNewFunction K n h L s p q hs i 1 (by decide)))
      (completeCartesianPointNormalize K n h L s p q hs i
        (completeCartesianPointNewFunction K n h L s p q hs i 2 (by decide))) := by
  let _ := Module.compHom
    Γ((completeCartesianPointComplement K n h L s p q hs i).toScheme, ⊤)
    (completeCartesianPointScalar K n h L s p q hs i)
  apply WeightedPoleMonomials.cubicCurve_equation
  have he := completeCartesianPoint_cubic_sum K n h L s p q hs i
  change ∑ j : Fin 6, completeCartesianPointCubicCoefficients K n h L s p q hs i j •
    WeightedPoleMonomials.monomial
      (completeCartesianPointNewFunction K n h L s p q hs i 1 (by decide))
      (completeCartesianPointNewFunction K n h L s p q hs i 2 (by decide)) j =
        (completeCartesianPointNewFunction K n h L s p q hs i 2 (by decide)) ^ 2 at he
  rw [WeightedPoleMonomials.sum_six] at he
  have hsmul (a : L)
      (z : Γ((completeCartesianPointComplement K n h L s p q hs i).toScheme, ⊤)) :
      a • z = completeCartesianPointScalar K n h L s p q hs i a * z := rfl
  simpa only [hsmul, mul_one] using he.symm

end FLT.Mazur.PolygonInfinitesimalStages
