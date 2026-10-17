/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AdicPositiveAffineLift

/-!
# Completion lifts from actual finite affine-valued morphisms

Compatible morphisms on the original quotient spectra supply their own
coordinate maps. The resulting completed map recovers each original morphism.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.AdicAffineMorphismLift
universe u
variable {A : Type u} [CommRing A] (I : Ideal A) (Y : Scheme.{u}) [IsAffine Y]
  (f : ∀ m : ℕ, Spec (.of (A ⧸ I ^ (m + 1))) ⟶ Y)
local notation "d" m => Spec.map (CommRingCat.ofHom
  (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (m + 1)))))
variable (hf : ∀ m : ℕ, Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor
  (S := I ^ (m + 2)) (T := I ^ (m + 1))
  (Ideal.pow_le_pow_right (Nat.le_succ (m + 1))))) ≫ f (m + 1) = f m)

/-- Coordinates are extracted from the actual finite morphisms. -/
def coordinates (m : ℕ) : Γ(Y, ⊤) →+* A ⧸ I ^ (m + 1) :=
  (Spec.preimage (f m ≫ Y.isoSpec.hom)).hom

/-- These coordinates retain exactly the original finite affine-valued morphism. -/
@[reassoc] theorem coordinates_spec (m : ℕ) :
    Spec.map (CommRingCat.ofHom (coordinates I Y f m)) ≫ Y.isoSpec.inv = f m := by
  rw [coordinates, CommRingCat.ofHom_hom, Spec.map_preimage,
    Category.assoc, Iso.hom_inv_id, Category.comp_id]

include hf in
/-- Adjacent coordinate compatibility follows from the actual scheme-map compatibility. -/
theorem coordinates_compatible (m : ℕ) (x : Γ(Y, ⊤)) :
    Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (m + 1)))
        (coordinates I Y f (m + 1) x) = coordinates I Y f m x := by
  have he : CommRingCat.ofHom ((Ideal.Quotient.factor
      (Ideal.pow_le_pow_right (Nat.le_succ (m + 1)))).comp
      (coordinates I Y f (m + 1))) = CommRingCat.ofHom (coordinates I Y f m) := by
    apply Spec.map_injective
    rw [CommRingCat.ofHom_comp, Spec.map_comp]
    apply (cancel_mono Y.isoSpec.inv).mp
    rw [Category.assoc, coordinates_spec, coordinates_spec, hf]
  exact congrArg (fun k ↦ k.hom x) he

/-- The original finite morphisms construct a genuine morphism from the completion. -/
def lift : Spec (.of (AdicCompletion I A)) ⟶ Y :=
  AdicPositiveAffineLift.lift I Y (coordinates I Y f) (coordinates_compatible I Y f hf)

/-- Every positive-order evaluation recovers the entire prescribed scheme morphism. -/
@[reassoc] theorem evaluation_lift (m : ℕ) :
    Spec.map (CommRingCat.ofHom (AdicCompletion.evalₐ I (m + 1)).toRingHom) ≫
        lift I Y f hf = f m := by
  rw [lift, AdicPositiveAffineLift.evaluation_lift, coordinates_spec]

end FLT.Mazur.AdicAffineMorphismLift
