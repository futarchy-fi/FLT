/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.NilpotentQuadraticRoot
public import FLT.Mazur.SuccessiveIncidencePolygonChart

/-!
# Constructing a branch on the original arithmetic node chart

When the non-tangent coefficients vanish modulo a nilpotent ideal, Hensel
lifting constructs the slope on the entire incidence chart. Evaluation gives
an actual section of the original successive chart's node projection.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassSuccessiveX
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (s π b3 b4 b6 : R)

/-- The original linear slope coefficient, as a function on the full node chart. -/
def nodeSlopeLinear : SuccessiveIncidence.Coordinate π :=
  algebraMap R _ W.a₁ + algebraMap R _ b3 * SuccessiveIncidence.t π

/-- The original constant side of the slope equation on the full node chart. -/
def nodeSlopeConstant : SuccessiveIncidence.Coordinate π :=
  algebraMap R _ s * SuccessiveIncidence.u π + algebraMap R _ W.a₂ +
    algebraMap R _ b4 * SuccessiveIncidence.t π +
    algebraMap R _ b6 * SuccessiveIncidence.t π ^ 2

variable (I : Ideal R) (hI : IsNilpotent I)

/-- The original nilpotent arithmetic ideal on the incidence chart. -/
def nodeArithmeticIdeal : Ideal (SuccessiveIncidence.Coordinate π) :=
  I.map (algebraMap R _)

include hI in
/-- Nilpotence survives extension to the entire node chart. -/
theorem nodeArithmeticIdeal_nilpotent : IsNilpotent (nodeArithmeticIdeal π I) := by
  obtain ⟨N, hN⟩ := hI
  refine ⟨N, ?_⟩
  rw [nodeArithmeticIdeal, ← Ideal.map_pow, hN]
  exact Ideal.map_bot

variable (ha : IsUnit W.a₁) (hs : s ∈ I) (h2 : W.a₂ ∈ I)
  (h3 : b3 ∈ I) (h4 : b4 ∈ I) (h6 : b6 ∈ I)

include hI ha h3 in
/-- The tangent coefficient is still a unit on every nonreduced node chart. -/
theorem nodeSlopeLinear_unit : IsUnit (nodeSlopeLinear W π b3) := by
  have hm : algebraMap R (SuccessiveIncidence.Coordinate π) b3 *
      SuccessiveIncidence.t π ∈ nodeArithmeticIdeal π I :=
    (nodeArithmeticIdeal π I).mul_mem_right _ (Ideal.mem_map_of_mem _ h3)
  exact (NilpotentQuadraticRoot.element_nilpotent _
    (nodeArithmeticIdeal_nilpotent π I hI) hm).isUnit_add_left_of_commute
      (ha.map (algebraMap R _)) (mul_comm _ _)

include hs h2 h4 h6 in
/-- The constant side vanishes in the original arithmetic special fiber. -/
theorem nodeSlopeConstant_mem : nodeSlopeConstant W s π b4 b6 ∈ nodeArithmeticIdeal π I := by
  apply (nodeArithmeticIdeal π I).add_mem
  · apply (nodeArithmeticIdeal π I).add_mem
    · exact (nodeArithmeticIdeal π I).add_mem
        ((nodeArithmeticIdeal π I).mul_mem_right _ (Ideal.mem_map_of_mem _ hs))
        (Ideal.mem_map_of_mem _ h2)
    · exact (nodeArithmeticIdeal π I).mul_mem_right _ (Ideal.mem_map_of_mem _ h4)
  · exact (nodeArithmeticIdeal π I).mul_mem_right _ (Ideal.mem_map_of_mem _ h6)

/-- The original coefficients construct the actual slope reducing to zero. -/
def nilpotentNodeSlope : SuccessiveIncidence.Coordinate π :=
  NilpotentQuadraticRoot.root (nodeArithmeticIdeal π I)
    (nodeArithmeticIdeal_nilpotent π I hI) (nodeSlopeLinear W π b3)
    (nodeSlopeConstant W s π b4 b6) (nodeSlopeLinear_unit W π b3 I hI ha h3)
    (nodeSlopeConstant_mem W s π b4 b6 I hs h2 h4 h6)

/-- The constructed slope satisfies the exact original equation. -/
theorem nilpotentNodeSlope_equation :
    nilpotentNodeSlope W s π b3 b4 b6 I hI ha hs h2 h3 h4 h6 ^ 2 +
      nodeSlopeLinear W π b3 *
        nilpotentNodeSlope W s π b3 b4 b6 I hI ha hs h2 h3 h4 h6 =
      nodeSlopeConstant W s π b4 b6 :=
  NilpotentQuadraticRoot.root_equation ..

/-- The constructed slope keeps the specified zero branch modulo the original ideal. -/
theorem nilpotentNodeSlope_mem :
    nilpotentNodeSlope W s π b3 b4 b6 I hI ha hs h2 h3 h4 h6 ∈ nodeArithmeticIdeal π I :=
  NilpotentQuadraticRoot.root_mem ..

/-- Evaluation constructs a node-chart section of the original successive model. -/
def nilpotentNodeRetraction : Coordinate W s π b3 b4 b6 →ₐ[R]
    SuccessiveIncidence.Coordinate π :=
  evaluation W s π b3 b4 b6
    ![SuccessiveIncidence.t π,
      nilpotentNodeSlope W s π b3 b4 b6 I hI ha hs h2 h3 h4 h6, SuccessiveIncidence.u π]
    (nilpotentNodeSlope_equation W s π b3 b4 b6 I hI ha hs h2 h3 h4 h6)
    (SuccessiveIncidence.incidence π)

/-- The original three coordinates are evaluated, with no replacement Weierstrass equation. -/
@[simp] theorem nilpotentNodeRetraction_coord (i : Fin 3) :
    nilpotentNodeRetraction W s π b3 b4 b6 I hI ha hs h2 h3 h4 h6
      (coord W s π b3 b4 b6 i) =
      ![SuccessiveIncidence.t π,
        nilpotentNodeSlope W s π b3 b4 b6 I hI ha hs h2 h3 h4 h6, SuccessiveIncidence.u π] i :=
  evaluation_coord ..

/-- The constructed branch is a right inverse of the actual incidence projection. -/
theorem nilpotentNodeRetraction_incidence :
    (nilpotentNodeRetraction W s π b3 b4 b6 I hI ha hs h2 h3 h4 h6).comp
      (incidenceToCoordinate W s π b3 b4 b6) = AlgHom.id R _ := by
  apply SuccessiveIncidence.hom_ext <;>
    simp only [AlgHom.comp_apply, incidenceToCoordinate, SuccessiveIncidence.evaluation_t,
      SuccessiveIncidence.evaluation_u, nilpotentNodeRetraction_coord,
      Matrix.cons_val_zero, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
      AlgHom.id_apply]

end FLT.Mazur.WeierstrassSuccessiveX
