/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityFiniteCoordinates
public import FLT.Mazur.PolygonUniversalEdgeAlgebra

/-!
# The original finite multiplication as an actual coefficient algebra map

Recover the original law's full Laurent coordinate as a unit of the double
Laurent algebra. The remaining law is precisely equality with the product unit.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonInfinitesimal
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic originalStageToCompatibleProj
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n) (m : ℕ)
local notation "A" => Ring K m
local notation "e" => completeIdentityStageTorus K n h i m
local notation "f" => completeIdentityFiniteMulCoordinates K n h i m
local notation "b" => Spec.map (CommRingCat.ofHom (algebraMap (A) (A)[T;T⁻¹]))

/-- The finite coordinate map retains the iterated Laurent algebra's coefficient structure. -/
theorem completeIdentityFiniteMulCoordinates_algebraBase :
    (f) ≫ (b) = Spec.map (CommRingCat.ofHom (algebraMap (A) (A)[T;T⁻¹][T;T⁻¹])) := by
  rw [completeIdentityFiniteMulCoordinates_base, ← Spec.map_comp]
  rfl

/-- The actual original multiplication's coefficient algebra map. -/
def completeIdentityFiniteMulAlgebra : (A)[T;T⁻¹] →ₐ[A] (A)[T;T⁻¹][T;T⁻¹] :=
  LaurentSchemeCoordinates.algebraHom (f)
    (completeIdentityFiniteMulCoordinates_algebraBase K n h i m)

/-- The coefficient map reconstructs the full original finite multiplication coordinates. -/
theorem completeIdentityFiniteMulAlgebra_spec :
    Spec.map (CommRingCat.ofHom (completeIdentityFiniteMulAlgebra K n h i m).toRingHom) =
      (f) := LaurentSchemeCoordinates.algebraHom_spec _ _

/-- The full Laurent unit pulled back by actual original multiplication. -/
def completeIdentityFiniteMulUnit : (A)[T;T⁻¹][T;T⁻¹]ˣ :=
  LaurentUnitPoints.pointUnit (completeIdentityFiniteMulAlgebra K n h i m)

/-- The original law is detected by its one actual coordinate, with all nilpotents retained. -/
theorem completeIdentityFiniteLaw_iff_unit :
    universalEdgeScaling (A) ≫ (e) = completeIdentityFiniteOriginalMul K n h i m ↔
      completeIdentityFiniteMulUnit K n h i m =
        Units.map (LaurentPolynomial.C : (A)[T;T⁻¹] →+* (A)[T;T⁻¹][T;T⁻¹])
          (PolygonUniversalScaling.u (R := A)) * PolygonUniversalScaling.u := by
  have hu := universalEdgeAlgebra_coordinate (A)
  constructor
  · intro he
    have hf := completeIdentityFiniteMulCoordinates_unique K n h i m
      (universalEdgeScaling (A)) he (by
        rw [universalEdgeScaling_base, ← Spec.map_comp]
        rfl)
    rw [universalEdgeScaling_spec, ← completeIdentityFiniteMulAlgebra_spec] at hf
    have ha := congrArg CommRingCat.Hom.hom (Spec.map_injective hf)
    have ha' : universalEdgeAlgebra (A) = completeIdentityFiniteMulAlgebra K n h i m :=
      AlgHom.coe_ringHom_injective ha
    rw [completeIdentityFiniteMulUnit, ← ha', hu]
  · intro he
    have ha : completeIdentityFiniteMulAlgebra K n h i m = universalEdgeAlgebra (A) := by
      apply (LaurentUnitPoints.pointsEquiv (R := A)).injective
      exact he.trans hu.symm
    have hf : (f) = universalEdgeScaling (A) := by
      rw [← completeIdentityFiniteMulAlgebra_spec, ha, universalEdgeScaling_spec]
    rw [← hf, completeIdentityFiniteMulCoordinates_original]

end FLT.Mazur.PolygonInfinitesimalStages
