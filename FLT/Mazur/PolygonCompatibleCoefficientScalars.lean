/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonBoundaryCoefficientScalars
public import FLT.Mazur.PolygonCompatibleCoefficientMap

/-!
# The compatible coefficient map retains the complete-base algebra

Every original stage detects the same power-series action. In particular,
coefficient change fixes the actual compatible smoothing parameter.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.PolygonInfinitesimalStages
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] compatibleCoefficientMap compatibleEval
variable {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (n : ℕ) (h : 2 ≤ n)

/-- The assembled map respects the actual complete coefficient homomorphism. -/
theorem compatibleCoefficientMap_algebraMap (r : PowerSeries R) :
    compatibleCoefficientMap f n h (algebraMap (PowerSeries R) (CompatibleSections R n h) r) =
      algebraMap (PowerSeries S) (CompatibleSections S n h) (PowerSeries.map f r) := by
  apply compatibleEval_ext S n h
  intro m
  rw [compatibleCoefficientMap_eval, compatibleEval_algebraMap, compatibleEval_algebraMap,
    coefficientBoundarySections_series]

/-- The original complete smoothing parameter is retained exactly. -/
theorem compatibleCoefficientMap_parameter :
    compatibleCoefficientMap f n h
      (algebraMap (PowerSeries R) (CompatibleSections R n h) PowerSeries.X) =
        algebraMap (PowerSeries S) (CompatibleSections S n h) PowerSeries.X := by
  rw [compatibleCoefficientMap_algebraMap, PowerSeries.map_X]

/-- The map is semilinear for the actual power-series coefficient substitution. -/
theorem compatibleCoefficientMap_smul (r : PowerSeries R) (s : CompatibleSections R n h) :
    compatibleCoefficientMap f n h (r • s) =
      PowerSeries.map f r • compatibleCoefficientMap f n h s := by
  simp only [Algebra.smul_def, map_mul, compatibleCoefficientMap_algebraMap]

/-- The constructed compatible map as an algebra map over the original complete base. -/
def compatibleCoefficientAlgHom :
    let _ : Algebra (PowerSeries R) (CompatibleSections S n h) :=
      ((algebraMap (PowerSeries S) (CompatibleSections S n h)).comp
        (PowerSeries.map f)).toAlgebra
    CompatibleSections R n h →ₐ[PowerSeries R] CompatibleSections S n h := by
  let _ : Algebra (PowerSeries R) (CompatibleSections S n h) :=
    ((algebraMap (PowerSeries S) (CompatibleSections S n h)).comp
      (PowerSeries.map f)).toAlgebra
  exact { compatibleCoefficientMap f n h with
    commutes' := compatibleCoefficientMap_algebraMap f n h }

end FLT.Mazur.PolygonInfinitesimalStages
