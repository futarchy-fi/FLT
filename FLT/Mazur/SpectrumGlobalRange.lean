/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Global function ranges for maps from an affine spectrum

A factorization through another affine spectrum gives explicit elements in
the range of the global function map, expressed in the original source ring.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.SpectrumGlobalRange
universe u
variable {A : CommRingCat.{u}} {X : Scheme.{u}} (f : Spec A ⟶ X)

/-- Pull global functions back to the given coordinate ring of the source spectrum. -/
def ringHom : Γ(X, ⊤) →+* A :=
  (f.appTop ≫ (Scheme.ΓSpecIso A).hom).hom

/-- Changing the affine source pulls the coordinate values back by the specified ring map. -/
theorem ringHom_comp_spec {B : CommRingCat.{u}} (φ : A ⟶ B) :
    ringHom (Spec.map φ ≫ f) = φ.hom.comp (ringHom f) := by
  simp only [ringHom, Scheme.Hom.comp_appTop, Category.assoc,
    Scheme.ΓSpecIso_naturality]
  rfl

/-- An affine factor supplies every value of its coordinate map to the global range. -/
theorem factor_mem {B : CommRingCat.{u}} (g : X ⟶ Spec B) (φ : B ⟶ A)
    (h : f ≫ g = Spec.map φ) (b : B) : φ b ∈ (ringHom f).range := by
  refine ⟨g.appTop ((Scheme.ΓSpecIso B).inv b), ?_⟩
  have he : (Scheme.ΓSpecIso B).inv ≫ g.appTop ≫ f.appTop ≫
      (Scheme.ΓSpecIso A).hom = φ := by
    rw [← Category.assoc g.appTop, ← Scheme.Hom.comp_appTop, h,
      Scheme.ΓSpecIso_naturality,
      Iso.inv_hom_id_assoc]
  exact congrArg (fun k : B ⟶ A ↦ k b) he

/-- Surjectivity in these coordinates is exactly surjectivity on global sections. -/
theorem surjective_iff : Function.Surjective (ringHom f) ↔ Function.Surjective f.appTop := by
  exact Function.Surjective.of_comp_iff'
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso A).hom) _

/-- For an affine target, generating the coordinate ring proves a closed immersion. -/
theorem closedImmersion [IsAffine X] (h : Function.Surjective (ringHom f)) :
    IsClosedImmersion f :=
  IsClosedImmersion.of_surjective_of_isAffine f ((surjective_iff f).mp h)

end FLT.Mazur.SpectrumGlobalRange
