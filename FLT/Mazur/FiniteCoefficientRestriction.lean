/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeometricCoefficientAutomorphisms
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-!
# Finite orbits of coefficient restrictions

An infinite coefficient automorphism group has only finitely many restrictions
to a finite extension of the residue field. The result retains whole scheme
morphisms under Spec and hence applies to sections of any original presheaf.
No algebraicity assumption is imposed on the larger coefficient field here.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
namespace FLT.Mazur.FiniteCoefficientRestriction
open GeometricCoefficientAutomorphisms
variable {k L K : Type} [Field k] [Field L] [Field K]
  [Algebra k L] [Algebra k K] [Module.Finite k L] (i : L →ₐ[k] K)

/-- Whole maps to the descended coefficient spectrum have finite orbit. -/
theorem finite_spec_restrictions :
    (Set.range (fun σ : K ≃ₐ[k] K ↦
      (specAction σ).hom ≫ Spec.map (CommRingCat.ofHom i.toRingHom))).Finite := by
  apply (Set.finite_range (fun j : L →ₐ[k] K ↦
    Spec.map (CommRingCat.ofHom j.toRingHom))).subset
  rintro _ ⟨σ, rfl⟩
  refine ⟨σ.symm.toAlgHom.comp i, ?_⟩
  change Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp]
  rfl

/-- Postcomposing a fixed scheme map preserves the finite restriction orbit. -/
theorem finite_spec_restrictions_comp {Z : Scheme} (q : Spec (.of L) ⟶ Z) :
    (Set.range (fun σ : K ≃ₐ[k] K ↦
      (specAction σ).hom ≫ Spec.map (CommRingCat.ofHom i.toRingHom) ≫ q)).Finite := by
  have h := (finite_spec_restrictions i).image (fun r ↦ r ≫ q)
  simpa only [← Set.range_comp', Category.assoc] using h

/-- A section over finite coefficients has finitely many conjugate pullbacks. -/
theorem finite_section_restrictions (F : Schemeᵒᵖ ⥤ Type*) (s : F.obj (op (Spec (.of L)))) :
    (Set.range (fun σ : K ≃ₐ[k] K ↦ F.map
      ((specAction σ).hom ≫ Spec.map (CommRingCat.ofHom i.toRingHom)).op s)).Finite := by
  simpa only [← Set.range_comp'] using
    (finite_spec_restrictions i).image (fun r ↦ F.map r.op s)

end FLT.Mazur.FiniteCoefficientRestriction
