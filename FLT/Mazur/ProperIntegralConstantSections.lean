/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.ProperCoherentCohomology
public import FLT.Mazur.CurveGenus
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Constant sections of a proper integral scheme with a rational point

Proper cohomology finiteness makes the global section domain finite over the
base field, hence a field. Evaluation at the rational point is then injective.
Because evaluation retracts the scalar map, every global section is constant.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.FCurve

variable {K : Type} [Field K] {X : Scheme} (f : X ⟶ Spec (.of K)) [IsProper f]

/-- Properness makes the actual ring of global sections finite over the base field. -/
theorem finiteDimensional_globalSections_of_proper :
    let _ := Module.compHom Γ(X, ⊤) (structureScalarMap f)
    FiniteDimensional K Γ(X, ⊤) := by
  let _ := Module.compHom Γ(X, ⊤) (structureScalarMap f)
  let _ := finiteDimensional_scalarH_of_proper f 0
  exact Module.Finite.equiv (scalarH0Equiv f)

include f in
/-- The global section domain of a proper integral scheme over a field is a field. -/
theorem globalSections_isField_of_proper_integral [AlgebraicGeometry.IsIntegral X] :
    IsField Γ(X, ⊤) := by
  let _ := (structureScalarMap f).toAlgebra
  let _ : Module.Finite K Γ(X, ⊤) := finiteDimensional_globalSections_of_proper f
  exact IsField.of_isDomain_of_finite K Γ(X, ⊤)

/-- A rational section evaluates every global function in the original base field. -/
def sectionEvaluation (s : Spec (.of K) ⟶ X) : Γ(X, ⊤) →+* K :=
  (s.appTop ≫ (Scheme.ΓSpecIso (.of K)).hom).hom

omit [IsProper f] in
/-- Evaluation at a section retracts the specified canonical scalar map. -/
theorem sectionEvaluation_scalar (s : Spec (.of K) ⟶ X) (hs : s ≫ f = 𝟙 _) :
    (sectionEvaluation s).comp (structureScalarMap f) = RingHom.id K := by
  unfold sectionEvaluation structureScalarMap
  change ((Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop ≫ s.appTop ≫
    (Scheme.ΓSpecIso (.of K)).hom).hom = _
  rw [← Category.assoc f.appTop, ← Scheme.Hom.comp_appTop, hs]
  simp

/-- Every global section is its constant value at any rational point. -/
theorem scalar_sectionEvaluation [AlgebraicGeometry.IsIntegral X]
    (s : Spec (.of K) ⟶ X) (hs : s ≫ f = 𝟙 _) (a : Γ(X, ⊤)) :
    structureScalarMap f (sectionEvaluation s a) = a := by
  let _ := (globalSections_isField_of_proper_integral f).toField
  apply (sectionEvaluation s).injective
  exact DFunLike.congr_fun (sectionEvaluation_scalar f s hs) (sectionEvaluation s a)

/-- A proper integral scheme with a rational point has exactly the constant global functions. -/
theorem constantGlobalSections_of_proper_integral_section [AlgebraicGeometry.IsIntegral X]
    (s : Spec (.of K) ⟶ X) (hs : s ≫ f = 𝟙 _) : HasConstantGlobalSections f := by
  refine ⟨(structureScalarMap f).injective, fun a => ?_⟩
  exact ⟨sectionEvaluation s a, scalar_sectionEvaluation f s hs a⟩

end FLT.Mazur.FCurve
