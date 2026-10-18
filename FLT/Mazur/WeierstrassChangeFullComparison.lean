/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassChangeComparisonScheme
public import FLT.Mazur.WeierstrassVariableChangeFaithful
public import FLT.Mazur.WeierstrassOriginIsomorphismAdmissible
public import FLT.Mazur.WeierstrassVariableChangeZero

/-!
# The comparison scheme classifies actual pointed smooth cubic isomorphisms

Every actual base- and origin-preserving isomorphism of the full proper
cubics is represented by a unique point of the constructed comparison
scheme. This includes arbitrary test algebras and arbitrary characteristics.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry WeierstrassCurve
namespace FLT.Mazur.WeierstrassChangeParameter
open WeierstrassIntegralChart
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] (W V : WeierstrassCurve R)

/-- Actual isomorphisms of the entire proper cubics preserving base and origin. -/
def PointedComparison := {e : integralCurve W ≅ integralCurve V //
  e.hom ≫ integralCurveStructure V = integralCurveStructure W ∧
    integralCurveZero W ≫ e.hom = integralCurveZero V}

/-- A full admissible change constructs an actual pointed comparison. -/
def changePointedComparison (C : VariableChange R) (h : C • V = W) :
    PointedComparison W V :=
  ⟨integralVariableChangeIso V W C h, integralVariableChangeTo_structure V W C h,
    integralVariableChangeIso_zero V W C h⟩

/-- No two changes give the same actual proper curve comparison. -/
theorem changePointedComparison_injective : Function.Injective
    (fun C : {C : VariableChange R // C • V = W} ↦
      changePointedComparison W V C.val C.property) := by
  intro C D h
  apply Subtype.ext
  exact integralVariableChangeIso_faithful V W C.val D.val C.property D.property
    (congrArg Subtype.val h)

/-- Smoothness makes every full pointed isomorphism an admissible coordinate change. -/
theorem changePointedComparison_surjective (hW : IsUnit W.Δ) (hV : IsUnit V.Δ) :
    Function.Surjective (fun C : {C : VariableChange R // C • V = W} ↦
      changePointedComparison W V C.val C.property) := by
  intro e
  obtain ⟨C, hC, he⟩ := originIso_exists_integralVariableChange W V hW hV e.val
    e.property.1 e.property.2
  exact ⟨⟨C, hC⟩, Subtype.ext he.symm⟩

/-- The coefficient conditions classify precisely the actual full pointed smooth comparisons. -/
def changePointedComparisonEquiv (hW : IsUnit W.Δ) (hV : IsUnit V.Δ) :
    {C : VariableChange R // C • V = W} ≃ PointedComparison W V :=
  Equiv.ofBijective _ ⟨changePointedComparison_injective W V,
    changePointedComparison_surjective W V hW hV⟩

/-- The constructed comparison scheme represents all full pointed isomorphisms on affine tests. -/
def fullComparisonSchemePointEquiv (hW : IsUnit W.Δ) (hV : IsUnit V.Δ)
    (A : Type) [CommRing A] [Algebra R A] :
    {f : Spec (.of A) ⟶ comparisonScheme W V //
      f ≫ comparisonStructure W V = Spec.algebraMap R A} ≃
        PointedComparison (W.map (algebraMap R A)) (V.map (algebraMap R A)) :=
  (comparisonSchemePointEquiv W V A).trans
    (changePointedComparisonEquiv _ _
      (by rw [map_Δ]; exact hW.map (algebraMap R A))
      (by rw [map_Δ]; exact hV.map (algebraMap R A)))

/-- Every actual full comparison has exactly one base-preserving parameter morphism. -/
theorem fullComparisonSchemePoint_unique (hW : IsUnit W.Δ) (hV : IsUnit V.Δ)
    (A : Type) [CommRing A] [Algebra R A]
    (e : PointedComparison (W.map (algebraMap R A)) (V.map (algebraMap R A))) :
    ∃! f : {f : Spec (.of A) ⟶ comparisonScheme W V //
        f ≫ comparisonStructure W V = Spec.algebraMap R A},
      fullComparisonSchemePointEquiv W V hW hV A f = e :=
  (fullComparisonSchemePointEquiv W V hW hV A).bijective.existsUnique e

end FLT.Mazur.WeierstrassChangeParameter
