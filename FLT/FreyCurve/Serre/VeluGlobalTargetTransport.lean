/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.VeluGlobalClassicalComparison
public import FLT.FreyCurve.Serre.VeluGlobalDegree

/-!
# The original global Vélu morphism with a named target equation

Transport along equality of equations retains the actual map, its original
point values, its identity section and its finite locally free degree.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open FLT.Mazur.WeierstrassIntegralChart

namespace WeierstrassCurve.Velu

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {K : Type} [Field K] [CharZero K] [IsAlgClosed K] [DecidableEq K]
  (E : WeierstrassCurve K) [E.IsElliptic]
  (G : AddSubgroup E.toAffine.Point) [Fintype G]
  (hodd : ∀ Q : G, Q ≠ 0 → Q ≠ -Q)
  (V : WeierstrassCurve K) (hV : V = curve E G)

/-- The original global map, with its exact named target equation. -/
def veluGlobalToEquation : integralCurve E ⟶ integralCurve V :=
  veluGlobalMorphism E G hodd ≫ eqToHom (congrArg integralCurve hV.symm)

/-- The named target changes no coefficient structure. -/
@[reassoc] theorem veluGlobalToEquation_base :
    veluGlobalToEquation E G hodd V hV ≫ integralCurveStructure V =
      integralCurveStructure E := by
  subst V
  simpa only [veluGlobalToEquation, eqToHom_refl, Category.comp_id] using
    veluGlobalMorphism_base E G hodd

/-- The original identity section maps to the named target identity section. -/
@[reassoc] theorem veluGlobalToEquation_zero :
    integralCurveZero E ≫ veluGlobalToEquation E G hodd V hV = integralCurveZero V := by
  subst V
  simpa only [veluGlobalToEquation, eqToHom_refl, Category.comp_id] using
    veluGlobalMorphism_zero E G hodd

/-- The map to the named target retains the original coordinate point map. -/
@[reassoc] theorem veluGlobalToEquation_pointMap
    (h : ∀ P, P ∉ G → V.toAffine.Nonsingular (xMap E G P) (yMap E G P))
    (P : E.toAffine.Point) :
    (affineSmoothPoint E P ≫ (integralSmoothOpen E).ι) ≫
        veluGlobalToEquation E G hodd V hV =
      affineSmoothPoint V (pointMap E G V h P) ≫ (integralSmoothOpen V).ι := by
  subst V
  simpa only [veluGlobalToEquation, eqToHom_refl, Category.comp_id] using
    veluGlobalMorphism_pointMap E G hodd P

/-- Finiteness is retained on the exact named target. -/
instance veluGlobalToEquation_finite : IsFinite (veluGlobalToEquation E G hodd V hV) := by
  unfold veluGlobalToEquation
  infer_instance

/-- Flatness is retained on the exact named target. -/
instance veluGlobalToEquation_flat : Flat (veluGlobalToEquation E G hodd V hV) := by
  unfold veluGlobalToEquation
  infer_instance

/-- Finite presentation is retained on the exact named target. -/
instance veluGlobalToEquation_lfp :
    LocallyOfFinitePresentation (veluGlobalToEquation E G hodd V hV) := by
  unfold veluGlobalToEquation
  infer_instance

/-- The named target has the same actual finite locally free degree. -/
theorem veluGlobalToEquation_degree :
    FLT.Mazur.FCurve.FiniteLocallyFreeDegree
      (veluGlobalToEquation E G hodd V hV) (Nat.card G) := by
  subst V
  simpa only [veluGlobalToEquation, eqToHom_refl, Category.comp_id] using
    veluGlobalMorphism_degree E G hodd

end WeierstrassCurve.Velu
