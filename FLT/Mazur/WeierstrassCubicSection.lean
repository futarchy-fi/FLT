/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCubicEquationTransition
public import FLT.Mazur.ProjectiveSectionExtensionCoordinates

/-!
# The genuine cubic as a section of O(3)

The actual defining equations in homogeneous-localization charts glue with
the proved weight-three transition. This constructs a section of the existing
twisting sheaf on every open, with its exact local coefficients and restrictions.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial
open FLT.Mazur.ProjectiveSpace
open FLT.Mazur.FCurve.ModuleSheafUnitCocycle

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] MvPolynomial.gradedAlgebra

variable {R : Type} [CommRing R] (W : WeierstrassCurve R)

/-- The actual local defining equation as a regular function on an ambient chart. -/
def cubicEquationSection (j : Fin 3) : Γ(space R (Fin 3), chart R (Fin 3) j) :=
  Proj.awayToSection (grading R (Fin 3)) (X j) (projectiveChartEquation W j)

/-- Restricting the local equation from the first chart is the left overlap map. -/
theorem cubicEquationSection_restrictLeft (j k : Fin 3) :
    res (X := space R (Fin 3)) inf_le_left (cubicEquationSection W j) =
      overlapScalarHom R (Fin 3) j k
        (chartOverlapLeft R (Fin 3) j k (projectiveChartEquation W j)) := by
  rw [overlapScalarHom_eq]
  have h := congrArg (fun f => f.hom (projectiveChartEquation W j))
    (Proj.awayMap_awayToSection (grading R (Fin 3)) (isHomogeneous_X R k) rfl)
  change _ = (space R (Fin 3)).presheaf.map (homOfLE (chart_inf R (Fin 3) j k).le).op
    (Proj.awayToSection (grading R (Fin 3)) (X j * X k)
      (chartOverlapLeft R (Fin 3) j k (projectiveChartEquation W j)))
  change Proj.awayToSection (grading R (Fin 3)) (X j * X k)
    (chartOverlapLeft R (Fin 3) j k (projectiveChartEquation W j)) =
      (space R (Fin 3)).presheaf.map _ (cubicEquationSection W j) at h
  erw [h]
  simp only [← Functor.map_comp_apply]
  rfl

/-- Restricting the local equation from the second chart is the right overlap map. -/
theorem cubicEquationSection_restrictRight (j k : Fin 3) :
    res (X := space R (Fin 3)) inf_le_right (cubicEquationSection W k) =
      overlapScalarHom R (Fin 3) j k
        (chartOverlapRight R (Fin 3) j k (projectiveChartEquation W k)) := by
  rw [overlapScalarHom_eq]
  have h := congrArg (fun f => f.hom (projectiveChartEquation W k))
    (Proj.awayMap_awayToSection (grading R (Fin 3)) (isHomogeneous_X R j)
      (mul_comm (X j) (X k)))
  change _ = (space R (Fin 3)).presheaf.map (homOfLE (chart_inf R (Fin 3) j k).le).op
    (Proj.awayToSection (grading R (Fin 3)) (X j * X k)
      (chartOverlapRight R (Fin 3) j k (projectiveChartEquation W k)))
  change Proj.awayToSection (grading R (Fin 3)) (X j * X k)
    (chartOverlapRight R (Fin 3) j k (projectiveChartEquation W k)) =
      (space R (Fin 3)).presheaf.map _ (cubicEquationSection W k) at h
  erw [h]
  simp only [← Functor.map_comp_apply]
  rfl

/-- The local equations obey precisely the transition of the existing O(3). -/
theorem cubicEquationSection_overlap (j k : Fin 3) :
    res (X := space R (Fin 3)) inf_le_left (cubicEquationSection W j) =
      (twistTransition R (Fin 3) 3 j k : Γ(space R (Fin 3), _)) *
        res inf_le_right (cubicEquationSection W k) := by
  rw [cubicEquationSection_restrictLeft, cubicEquationSection_restrictRight,
    projectiveChartEquation_transition, map_mul]
  congr 1
  exact overlapScalarHom_coordinate_pow R (Fin 3) j k 3

/-- The same coefficient equation holds on every common subopen. -/
theorem cubicEquationSection_transition (j k : Fin 3) (V : (space R (Fin 3)).Opens)
    (hj : V ≤ chart R (Fin 3) j) (hk : V ≤ chart R (Fin 3) k) :
    res hj (cubicEquationSection W j) =
      ((twistCocycle R (Fin 3) 3).unit j k V hj hk : Γ(space R (Fin 3), V)) *
        res hk (cubicEquationSection W k) := by
  have h := congrArg (res (le_inf hj hk)) (cubicEquationSection_overlap W j k)
  simpa only [map_mul, res_res, twistCocycle, Cocycle.ofOverlap, Units.coe_map,
    RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass] using h

/-- The genuine cubic section of O(3), restricted to an arbitrary ambient open. -/
def cubicTwistSection (V : (space R (Fin 3)).Opens) :
    (twistCocycle R (Fin 3) 3).sections V :=
  ⟨fun j => res inf_le_right (cubicEquationSection W j), by
    intro j k U hj hk
    simpa only [res_res] using cubicEquationSection_transition W j k U
      (hj.trans inf_le_right) (hk.trans inf_le_right)⟩

/-- The section has exactly the original cubic coefficient on every chart intersection. -/
@[simp] theorem cubicTwistSection_coordinate (V : (space R (Fin 3)).Opens) (j : Fin 3) :
    (cubicTwistSection W V).val j = res inf_le_right (cubicEquationSection W j) := rfl

/-- Restriction of the constructed cubic section is the same specified section. -/
@[simp] theorem cubicTwistSection_restrict {V U : (space R (Fin 3)).Opens} (h : U ≤ V) :
    (twistCocycle R (Fin 3) 3).restrict h (cubicTwistSection W V) =
      cubicTwistSection W U := by
  apply Subtype.ext
  funext j
  exact res_res _ _ _

end FLT.Mazur.WeierstrassIntegralChart
