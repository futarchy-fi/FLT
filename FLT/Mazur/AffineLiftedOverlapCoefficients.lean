/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineTripleOverlapPullback

/-!
# Scalar formulas for lifted overlap coefficients

First take a pair coefficient chart through an arbitrary mapped pullback unit.
Specializing that map to the composition comparison gives the normalized
first and second pure-tensor formulas without unfolding the comparison.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct
open Scheme.Modules
open FLT.Mazur FLT.Mazur.AffineOverlapTensor FLT.Mazur.AffineOverlapPullback
open FLT.Mazur.AffineIteratedPullbackSections
universe u
namespace FLT.Mazur.AffineLiftedOverlapCoefficients
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
variable (M : (Spec (.of S)).Modules) [M.IsQuasicoherent]
/-- Restrict the coefficient action to the base. -/
local instance : Module R (coefficients S M) := Module.compHom _ (algebraMap R S)
local instance : IsScalarTower R S (coefficients S M) :=
  IsScalarTower.of_algebraMap_smul (fun _ _ ↦ rfl)
variable {C : CommRingCat.{u}} (p : CommRingCat.of (S ⊗[R] S) ⟶ C)
variable (Q : (Spec C).Modules)
/-- A mapped pullback unit sends the first chart to its scalar multiple. -/
theorem first_mapped (e : (pullback (Spec.map p)).obj
    ((pullback (Spec.map (CommRingCat.ofHom (left R S)))).obj M) ⟶ Q)
    (n : coefficients S M) (s : S) :
    mappedUnit p _ e (firstSections R S M (n ⊗ₜ[R] s)) =
      p (1 ⊗ₜ[R] s) • mappedUnit p _ e
        (specUnit (CommRingCat.ofHom (left R S)) M n) := by
  rw [firstSections_tmul, specUnit_apply]
  exact mappedUnit_smul p _ e _ _

/-- A mapped pullback unit sends the second chart to its scalar multiple. -/
theorem second_mapped (e : (pullback (Spec.map p)).obj
    ((pullback (Spec.map (CommRingCat.ofHom (right R S)))).obj M) ⟶ Q)
    (n : coefficients S M) (s : S) :
    mappedUnit p _ e (secondSections R S M (s ⊗ₜ[R] n)) =
      p (s ⊗ₜ[R] 1) • mappedUnit p _ e
        (specUnit (CommRingCat.ofHom (right R S)) M n) := by
  rw [secondSections_tmul, specUnit_apply]
  exact mappedUnit_smul p _ e _ _

/-- Normalized lifting of the first chart applies the pair map to its scalar. -/
theorem first_normalized {D : Type u} [CommRing D] (q : S ⊗[R] S →+* D)
    (i : S →+* D) (hi : q.comp (left R S) = i) (n : coefficients S M) (s : S) :
    mappedUnit (CommRingCat.ofHom q) _ (comparison (left R S) q i hi M).hom
      (firstSections R S M (n ⊗ₜ[R] s)) =
        q (1 ⊗ₜ[R] s) • specUnit (CommRingCat.ofHom i) M n := by
  have h := first_mapped R S M (CommRingCat.ofHom q) _
    (comparison (left R S) q i hi M).hom n s
  apply h.trans
  apply congrArg (q (1 ⊗ₜ[R] s) • ·)
  rw [← liftSections_eq_mappedUnit, liftSections_unit]
/-- Normalized lifting of the second chart applies the pair map to its scalar. -/
theorem second_normalized {D : Type u} [CommRing D] (q : S ⊗[R] S →+* D)
    (i : S →+* D) (hi : q.comp (right R S) = i) (n : coefficients S M) (s : S) :
    mappedUnit (CommRingCat.ofHom q) _ (comparison (right R S) q i hi M).hom
      (secondSections R S M (s ⊗ₜ[R] n)) =
        q (s ⊗ₜ[R] 1) • specUnit (CommRingCat.ofHom i) M n := by
  have h := second_mapped R S M (CommRingCat.ofHom q) _
    (comparison (right R S) q i hi M).hom n s
  apply h.trans
  apply congrArg (q (s ⊗ₜ[R] 1) • ·)
  rw [← liftSections_eq_mappedUnit, liftSections_unit]

end FLT.Mazur.AffineLiftedOverlapCoefficients
