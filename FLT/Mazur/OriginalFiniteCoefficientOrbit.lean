/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteCoefficientRestriction
public import FLT.Mazur.ResidueGeometricConjugacy

/-!
# Finite coefficient descent in the original over category

Coefficient restriction and the full automorphism action are constructed
above the unchanged original scheme. Sections pulled back from a finite
residue-field extension have finite orbits in every original presheaf.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
namespace FLT.Mazur.OriginalFiniteCoefficientOrbit
open GeometricCoefficientAutomorphisms
set_option backward.isDefEq.respectTransparency false
variable {k L K : Type} [Field k] [Field L] [Field K]
  [Algebra k L] [Algebra k K] {S : Scheme} (t : Spec (.of k) ⟶ S)

/-- The geometric coefficient test retains its original base map. -/
abbrev coefficientTest : Over S :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K)) ≫ t)

/-- The coefficient embedding is an actual map of original tests. -/
def restriction (i : L →ₐ[k] K) : coefficientTest (K := K) t ⟶ coefficientTest (K := L) t :=
  Over.homMk (Spec.map (CommRingCat.ofHom i.toRingHom)) (by
    change Spec.map (CommRingCat.ofHom i.toRingHom) ≫
      (Spec.map (CommRingCat.ofHom (algebraMap k L)) ≫ t) =
        Spec.map (CommRingCat.ofHom (algebraMap k K)) ≫ t
    rw [← Category.assoc, ← Spec.map_comp]
    congr 2
    apply CommRingCat.hom_ext
    exact i.comp_algebraMap)

/-- Every residue-coefficient automorphism acts above the original base. -/
def coefficientIso (σ : K ≃ₐ[k] K) : coefficientTest (K := K) t ≅ coefficientTest (K := K) t :=
  Over.isoMk (specAction σ) (ResidueGeometricConjugacy.specAction_original t σ)

variable [Module.Finite k L] (i : L →ₐ[k] K)

/-- Only finitely many whole original test maps occur after restriction to finite coefficients. -/
theorem finite_original_restrictions :
    (Set.range (fun σ : K ≃ₐ[k] K ↦ (coefficientIso t σ).hom ≫ restriction t i)).Finite := by
  apply Set.Finite.of_finite_image (f := fun r ↦ r.left)
  · rw [← Set.range_comp']
    exact FiniteCoefficientRestriction.finite_spec_restrictions i
  · intro a _ b _ h
    exact Over.OverMorphism.ext h

/-- Finite coefficient descent constructs a finite section orbit in the original presheaf. -/
theorem finite_original_section_orbit (F : (Over S)ᵒᵖ ⥤ Type*)
    (s : F.obj (op (coefficientTest (K := L) t))) :
    (Set.range (fun σ : K ≃ₐ[k] K ↦
      F.map (coefficientIso t σ).hom.op (F.map (restriction t i).op s))).Finite := by
  have h := (finite_original_restrictions t i).image (fun r ↦ F.map r.op s)
  rw [← Set.range_comp'] at h
  convert h using 1
  congr 1
  funext σ
  rw [op_comp, F.map_comp]
  rfl

end FLT.Mazur.OriginalFiniteCoefficientOrbit
