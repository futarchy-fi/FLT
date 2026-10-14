/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.NodeTangentRootEvaluation
public import FLT.Mazur.WeierstrassCoefficientShearSpecializationTransport
public import FLT.Mazur.WeierstrassCoefficientShearTangentConjugation

/-!
# Actual chosen-root fibers of the integral tangent model

Evaluation at either companion root specializes the entire original tangent
model. Its genuine conjugation exchanges these fibers via the independent
root-change morphism, before any polygon identification is chosen.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (S : Type) [CommRing S] [Algebra R S] (r : S)
  (hr : r ^ 2 + algebraMap R S W.a₁ * r - algebraMap R S W.a₂ = 0)
  (j : ℕ) (hj : j ≤ n)
local notation "A" => AdjoinRoot (nodeTangentPolynomial W)
local notation "root" => AdjoinRoot.root (nodeTangentPolynomial W)
local notation "e" => nodeTangentRootEvaluation W S r hr
local notation "σ" => coefficientShearTangentConjugation hπ data j hj
local notation "gA" => coefficientShearGluedStructure hπ data A root j hj

/-- The full equation model at an actual chosen root maps into the integral tangent model. -/
def coefficientShearTangentRootSpecialization :=
  coefficientShearSpecialization hπ data A S root r j hj e
local notation "M" => coefficientShearTangentRootSpecialization hπ data S r hr j hj

/-- The chosen-root fiber is the actual cartesian fiber of the integral tangent model. -/
theorem coefficientShearTangentRootSpecialization_isPullback :
    IsPullback M (coefficientShearGluedStructure hπ data S r j hj) gA
      (Spec.map (CommRingCat.ofHom (e).toRingHom)) :=
  coefficientShearSpecialization_isPullback hπ data A S root r j hj e

/-- The original integral tangent conjugation is its actual coefficient specialization. -/
theorem coefficientShearTangentConjugation_eq_specialization :
    σ = coefficientShearSpecialization hπ data A A root root j hj
      (nodeTangentConjugation W).toAlgHom := by
  apply (coefficientShearGlued_isPullback hπ data A root j hj).hom_ext
  · rw [coefficientShearTangentConjugation_structure, coefficientShearSpecialization_structure]
    rfl
  · rw [coefficientShearTangentConjugation_projection, coefficientShearSpecialization_projection]

variable (t : S)
  (ht : t ^ 2 + algebraMap R S W.a₁ * t - algebraMap R S W.a₂ = 0)
  (hrt : r + t = -algebraMap R S W.a₁)
include hrt

/-- Whole-model root change is exactly the actual integral conjugation between evaluated fibers. -/
@[reassoc] theorem coefficientShearTangentRootSpecialization_conjugation :
    M ≫ σ = (coefficientShearRootChange hπ data S r t j hj).hom ≫
      coefficientShearTangentRootSpecialization hπ data S t ht j hj := by
  rw [coefficientShearTangentConjugation_eq_specialization,
    coefficientShearTangentRootSpecialization, coefficientShearSpecialization_comp,
    nodeTangentRootEvaluation_companion W S r hr t ht hrt,
    coefficientShearTangentRootSpecialization, coefficientShearSpecialization_sourceRoot]

/-- The comparison retains the original integral-model projection on every test scheme. -/
@[reassoc] theorem coefficientShearTangentRootSpecialization_original_conjugation :
    M ≫ (coefficientShearGluedIso hπ data A root j hj).hom ≫
        finiteGlobalTangentConjugation hπ data j hj =
      (coefficientShearRootChange hπ data S r t j hj).hom ≫
        coefficientShearTangentRootSpecialization hπ data S t ht j hj ≫
          (coefficientShearGluedIso hπ data A root j hj).hom := by
  rw [← coefficientShearTangentConjugation_reconstruction,
    ← Category.assoc, coefficientShearTangentRootSpecialization_conjugation
    hπ data S r hr j hj t ht hrt, Category.assoc]

end FLT.Mazur.WeierstrassDividedDepth
