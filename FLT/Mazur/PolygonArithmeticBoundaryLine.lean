/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticBoundaryDivisor
public import FLT.Mazur.PolygonInfinitesimalStageLine

/-!
# Positive boundary lines over the original arithmetic coefficients

The Cartier boundary supplies an actual locally free rank-one sheaf at each
order. Its canonical pullback comparisons preserve the divisor sections on
every transition and under the original integral specialization.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.PolygonArithmeticStages
open FCurve
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (A : Type u) [CommRing A] (π : A) (m n : ℕ) (h : 2 ≤ n)

/-- The positive line of the original full arithmetic boundary. -/
def boundaryLine : (family A π m n h).left.Modules :=
  divisorLineBundle (boundaryIdeal A π m n h) (boundaryIdeal_cartier A π m n h).1

/-- Every arithmetic boundary line is locally free of rank one. -/
theorem boundaryLine_rankOne : LocallyFreeRankOne (boundaryLine A π m n h) :=
  (boundaryIdeal_cartier A π m n h).1.divisorLineBundle_locallyFreeRankOne

variable {a b : ℕ} (f : a ⟶ b)

/-- Nonflat arithmetic restriction preserves the actual invertible ideal module. -/
instance boundaryIdeal_systemMap_isIso :
    IsIso (idealModulePullbackHom (boundaryIdeal A π b n h)
      ((stageSystem A π n h).map f)) := by
  apply idealModulePullbackHom_isIso_of_cartier _ (boundaryIdeal_cartier A π b n h).1
  rw [boundaryIdeal_systemMap]
  exact (boundaryIdeal_cartier A π a n h).1

/-- Canonical comparison of boundary lines on every arithmetic transition. -/
def boundaryLineSystemIso :
    (pullback ((stageSystem A π n h).map f)).obj (boundaryLine A π b n h) ≅
      boundaryLine A π a n h := by
  let _ := boundaryIdeal_systemMap_isIso A π n h f
  exact divisorLinePullbackIsoOfEq _ (boundaryIdeal_cartier A π b n h).1
    (boundaryIdeal_cartier A π a n h).1 (boundaryIdeal_systemMap A π n h f)

/-- Every arithmetic line comparison preserves the original canonical divisor section. -/
theorem boundaryLineSystemIso_section :
    (pullback ((stageSystem A π n h).map f)).map
        (divisorSectionMap (boundaryIdeal_cartier A π b n h).1) ≫
          (boundaryLineSystemIso A π n h f).hom =
      (modulePullbackUnitIso ((stageSystem A π n h).map f)).hom ≫
        divisorSectionMap (boundaryIdeal_cartier A π a n h).1 := by
  let _ := boundaryIdeal_systemMap_isIso A π n h f
  exact divisorLinePullbackIsoOfEq_section _ (boundaryIdeal_cartier A π b n h).1
    (boundaryIdeal_cartier A π a n h).1 (boundaryIdeal_systemMap A π n h f)

/-- The original integral specialization also preserves the invertible ideal module. -/
instance boundaryIdeal_specialization_isIso :
    IsIso (idealModulePullbackHom (PolygonInfinitesimalStages.boundaryIdeal A m n h)
      (specializationFamily A π m n h)) := by
  apply idealModulePullbackHom_isIso_of_cartier _
    (PolygonInfinitesimalStages.boundaryIdeal_cartier A m n h).1
  rw [boundaryIdeal_specializationFamily]
  exact (boundaryIdeal_cartier A π m n h).1

/-- Arithmetic boundary lines are the actual specialized integral universal lines. -/
def boundaryLineSpecializationIso :
    (pullback (specializationFamily A π m n h)).obj
        (PolygonInfinitesimalStages.boundaryLine A m n h) ≅ boundaryLine A π m n h :=
  divisorLinePullbackIsoOfEq _ (PolygonInfinitesimalStages.boundaryIdeal_cartier A m n h).1
    (boundaryIdeal_cartier A π m n h).1 (boundaryIdeal_specializationFamily A π m n h)

/-- Integral specialization retains the section cutting out the entire original boundary. -/
theorem boundaryLineSpecializationIso_section :
    (pullback (specializationFamily A π m n h)).map
        (divisorSectionMap (PolygonInfinitesimalStages.boundaryIdeal_cartier A m n h).1) ≫
          (boundaryLineSpecializationIso A π m n h).hom =
      (modulePullbackUnitIso (specializationFamily A π m n h)).hom ≫
        divisorSectionMap (boundaryIdeal_cartier A π m n h).1 :=
  divisorLinePullbackIsoOfEq_section _
    (PolygonInfinitesimalStages.boundaryIdeal_cartier A m n h).1
    (boundaryIdeal_cartier A π m n h).1 (boundaryIdeal_specializationFamily A π m n h)

end FLT.Mazur.PolygonArithmeticStages
