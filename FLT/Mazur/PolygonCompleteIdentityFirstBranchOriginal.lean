/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityFirstActionCoordinate

/-!
# The retained-parameter branch is the original finite multiplication

Identify the full Laurent branch substitution with the original geometric
multiplication after the specified coefficient map. In particular its cubic
contraction is the original action target on the original finite edge.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing PolygonInfinitesimal LaurentPolynomial LaurentUnitPoints
open PolygonScalingNaturality LaurentFirstStageParameter LaurentPairNaturality
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic originalStageToCompatibleProj
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
local notation "A" => Ring K 1
local notation "S" => Ring K[T;T⁻¹] 1
local notation "c" => stageCoefficientMap (C : K →+* K[T;T⁻¹]) 1
local notation "U" => completeIdentityFirstActionUnit K n h i
local notation "q" => Spec.map (CommRingCat.ofHom (coeffMap (parameterEval K)))
local notation "b" => Spec.map (CommRingCat.ofHom (coeffMap (c)))
local notation "a" => Spec.map (CommRingCat.ofHom (AlgHom.toRingHom (evalUnit (U))))

/-- The entire original multiplication algebra survives moving its parameter into the base. -/
theorem completeIdentityFirstActionUnit_originalAlgebra :
    (evalUnit (U)).toRingHom.comp (coeffMap (c)) =
      (coeffMap (parameterEval K)).comp
        (completeIdentityFiniteMulAlgebra K n h i 1).toRingHom := by
  have hf : (evalUnit (completeIdentityFiniteMulUnit K n h i 1)).toRingHom =
      (completeIdentityFiniteMulAlgebra K n h i 1).toRingHom :=
    congrArg AlgHom.toRingHom (evalUnit_pointUnit _)
  rw [← hf]
  change (eval₂ (C : (S) →+* (S)[T;T⁻¹]) (U)).comp (coeffMap (c)) =
    (coeffMap (parameterEval K)).comp (eval₂ (algebraMap (A) (A)[T;T⁻¹][T;T⁻¹]) _)
  rw [eval₂_coeffMap, eval₂_map]
  congr 1
  apply RingHom.ext
  intro r
  change C ((c) r) = coeffMap (parameterEval K) (C (C r))
  rw [coeffMap_C, parameterEval_C]

/-- The retained branch substitution is the full original coordinate morphism. -/
@[reassoc] theorem completeIdentityFirstActionUnit_originalCoordinates :
    (a) ≫ (b) = (q) ≫ completeIdentityFiniteMulCoordinates K n h i 1 := by
  rw [← completeIdentityFiniteMulAlgebra_spec, ← Spec.map_comp, ← Spec.map_comp]
  exact congrArg Spec.map (CommRingCat.hom_ext
    (completeIdentityFirstActionUnit_originalAlgebra K n h i))

/-- The branch is actual original group multiplication, with its coefficient map unchanged. -/
@[reassoc] theorem completeIdentityFirstActionUnit_originalMul :
    (a) ≫ (b) ≫ completeIdentityStageTorus K n h i 1 =
      (q) ≫ completeIdentityFiniteOriginalMul K n h i 1 := by
  rw [← Category.assoc, completeIdentityFirstActionUnit_originalCoordinates,
    Category.assoc, completeIdentityFiniteMulCoordinates_original]

/-- The original punctured branch satisfies the original complete cubic action equation. -/
@[reassoc] theorem completeIdentityFirstActionUnit_originalCubic :
    (a) ≫ (b) ≫ completeIdentityStageTorus K n h i 1 ≫
        (completePointIdentityOpen K n h i).ι ≫ completePointToIntegralCubic K n h i =
      (q) ≫ edge (A)[T;T⁻¹] (C (parameter K 1)) n h i ≫
        completeIdentityFiniteInput K n h i 1 ≫ completeIdentityActionTarget K n h i := by
  rw [completeIdentityFirstActionUnit_originalMul_assoc,
    completeIdentityFiniteOriginalMul_cubic]

end FLT.Mazur.PolygonInfinitesimalStages
