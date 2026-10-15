/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityFiniteAlgebra
public import FLT.Mazur.PolygonCompleteIdentityFiniteUnits

/-!
# Exact coefficient specializations of the original finite multiplication unit

Setting either variable to one in the actual original coefficient map is
the identity algebra map. Thus both specializations of its full unit are
the surviving universal Laurent variable, including all nilpotent coefficients.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic originalStageToCompatibleProj
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n) (m : ℕ)
local notation "A" => Ring K m
local notation "f" => completeIdentityFiniteMulAlgebra K n h i m
local notation "v" => completeIdentityFiniteMulUnit K n h i m
local notation "ε₁" => PolygonScalingNaturality.coeffMap
  (AlgHom.toRingHom (LaurentUnitPoints.evalUnit (R := A) (1 : (A)ˣ)))
local notation "ε₂" => AlgHom.toRingHom (LaurentUnitPoints.evalUnit
  (R := (A)[T;T⁻¹]) (1 : (A)[T;T⁻¹]ˣ))

/-- The original coefficient law becomes the identity when its first variable is one. -/
theorem completeIdentityFiniteMulAlgebra_firstUnit :
    (ε₁).comp (f).toRingHom = RingHom.id (A)[T;T⁻¹] := by
  have he := completeIdentityFiniteMulCoordinates_firstUnit K n h i m
  rw [← completeIdentityFiniteMulAlgebra_spec] at he
  change Spec.map (CommRingCat.ofHom (ε₁)) ≫ Spec.map (CommRingCat.ofHom (f).toRingHom) =
    𝟙 (Spec (.of (A)[T;T⁻¹])) at he
  rw [← Spec.map_comp, ← Spec.map_id] at he
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective he)

/-- The original coefficient law becomes the identity when its second variable is one. -/
theorem completeIdentityFiniteMulAlgebra_secondUnit :
    (ε₂).comp (f).toRingHom = RingHom.id (A)[T;T⁻¹] := by
  have he := completeIdentityFiniteMulCoordinates_secondUnit K n h i m
  rw [← completeIdentityFiniteMulAlgebra_spec] at he
  change Spec.map (CommRingCat.ofHom (ε₂)) ≫ Spec.map (CommRingCat.ofHom (f).toRingHom) =
    𝟙 (Spec (.of (A)[T;T⁻¹])) at he
  rw [← Spec.map_comp, ← Spec.map_id] at he
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective he)

/-- The full original Laurent multiplication unit has the correct first unit specialization. -/
theorem completeIdentityFiniteMulUnit_firstUnit :
    Units.map (ε₁).toMonoidHom (v) = PolygonUniversalScaling.u := by
  apply Units.ext
  change (ε₁) ((f).toRingHom (LaurentPolynomial.T 1)) =
    LaurentPolynomial.C (1 : A) * LaurentPolynomial.T 1
  have he := congrArg (fun g : (A)[T;T⁻¹] →+* (A)[T;T⁻¹] ↦ g (LaurentPolynomial.T 1))
    (completeIdentityFiniteMulAlgebra_firstUnit K n h i m)
  simpa only [RingHom.comp_apply, RingHom.id_apply, map_one, one_mul] using he

/-- The full original Laurent multiplication unit has the correct second unit specialization. -/
theorem completeIdentityFiniteMulUnit_secondUnit :
    Units.map (ε₂).toMonoidHom (v) = PolygonUniversalScaling.u := by
  apply Units.ext
  change (ε₂) ((f).toRingHom (LaurentPolynomial.T 1)) =
    LaurentPolynomial.C (1 : A) * LaurentPolynomial.T 1
  have he := congrArg (fun g : (A)[T;T⁻¹] →+* (A)[T;T⁻¹] ↦ g (LaurentPolynomial.T 1))
    (completeIdentityFiniteMulAlgebra_secondUnit K n h i m)
  simpa only [RingHom.comp_apply, RingHom.id_apply, map_one, one_mul] using he

end FLT.Mazur.PolygonInfinitesimalStages
