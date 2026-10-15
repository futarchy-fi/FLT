/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticGradedParameter

/-!
# Actual homogeneous section modules over the integral base

Restrict the existing homogeneous modules along the original integral-base
structural scalar maps. Every original adjacent transition is linear over
this one coefficient ring, as required for compatible scalar division.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.PolygonArithmeticStages

open SectionGradedSum

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

attribute [local irreducible] boundaryLine family boundaryIntegralScalars

variable (A : Type) [CommRing A] (π : A) (n : ℕ) (h : 2 ≤ n)

/-- Original integral-base coefficients as structural sections of a stage. -/
def boundaryIntegralScalarMap (m : ℕ) : A →+* Γ((family A π m n h).left, ⊤) :=
  (stageScalars A π m n h).comp (Ideal.Quotient.mk (ideal A π ^ (m + 1)))

/-- The actual structural scalar map agrees with the original graded-ring scalar map. -/
theorem boundaryIntegralScalarMap_algebraMap (m : ℕ) (r : A) :
    algebraMap Γ((family A π m n h).left, ⊤) (boundaryGradedSections A π n h m)
      (boundaryIntegralScalarMap A π n h m r) = boundaryIntegralScalars A π n h m r := by
  rw [boundaryIntegralScalars_stage]
  rfl

/-- One actual homogeneous module, with scalars restricted from the integral base. -/
def boundaryIntegralDegree (m d : ℕ) : ModuleCat A :=
  (ModuleCat.restrictScalars (boundaryIntegralScalarMap A π n h m)).obj
    (ModuleCat.of Γ((family A π m n h).left, ⊤) (grade (boundaryLine A π m n h) ⊤ d))

/-- The restricted action is multiplication by the original integral-base scalar. -/
theorem boundaryIntegralDegree_smul_val (m d : ℕ) (r : A)
    (s : boundaryIntegralDegree A π n h m d) :
    (r • s).val = boundaryIntegralScalars A π n h m r * s.val := by
  change boundaryIntegralScalarMap A π n h m r • s.val = _
  rw [Algebra.smul_def, boundaryIntegralScalarMap_algebraMap]

/-- The original adjacent homogeneous transition is linear over the integral base. -/
def boundaryIntegralDegreeTransition (m d : ℕ) :
    boundaryIntegralDegree A π n h (m + 1) d →ₗ[A]
      boundaryIntegralDegree A π n h m d where
  toFun s := ⟨boundarySectionsMap A π n h (homOfLE (Nat.le_succ m)) s.val,
    boundarySectionsMap_mem_grade A π n h (homOfLE (Nat.le_succ m)) s.property⟩
  map_add' s t := Subtype.ext (map_add _ _ _)
  map_smul' r s := by
    apply Subtype.ext
    let t : boundaryIntegralDegree A π n h m d :=
      ⟨boundarySectionsMap A π n h (homOfLE (Nat.le_succ m)) s.val,
        boundarySectionsMap_mem_grade A π n h (homOfLE (Nat.le_succ m)) s.property⟩
    change boundarySectionsMap A π n h (homOfLE (Nat.le_succ m)) (r • s).val = (r • t).val
    rw [boundaryIntegralDegree_smul_val, boundaryIntegralDegree_smul_val, map_mul]
    have he := DFunLike.congr_fun (boundarySectionsMap_integral A π n h
      (homOfLE (Nat.le_succ m))) r
    exact congrArg (fun a ↦ a * boundarySectionsMap A π n h
      (homOfLE (Nat.le_succ m)) s.val) he

/-- Powers of the parameter retain their original ring multiplication on homogeneous values. -/
theorem boundaryIntegralDegree_parameterPower_val (m d k : ℕ)
    (s : boundaryIntegralDegree A π n h m d) :
    (π ^ k • s).val =
      boundaryIntegralScalars A π n h m π ^ k * s.val := by
  rw [boundaryIntegralDegree_smul_val, map_pow]

end FLT.Mazur.PolygonArithmeticStages
