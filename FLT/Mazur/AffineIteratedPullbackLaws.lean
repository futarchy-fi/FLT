/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineCoefficientUnitLaws

/-!
# Laws for normalized affine coefficient lifting

The normalized lifting preserves units, transforms scalars by the ring map,
and intertwines conjugated pullbacks of sheaf morphisms.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.AffineIteratedPullbackSections
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
variable (i : A →+* B) (p : B →+* C) (j : A →+* C) (w : p.comp i = j)
variable (N : (Spec (.of A)).Modules)

/-- Express the existing lifting through the generic coefficient construction. -/
theorem liftSections_eq_mappedUnit : liftSections i p j w N =
    mappedUnit (CommRingCat.ofHom p)
      ((pullback (Spec.map (CommRingCat.ofHom i))).obj N) (comparison i p j w N).hom := rfl

/-- Evaluate normalized lifting directly as a comparison after a pullback unit. -/
theorem liftSections_apply
    (x : moduleSpecΓFunctor.obj ((pullback (Spec.map (CommRingCat.ofHom i))).obj N)) :
    liftSections i p j w N x =
      (comparison i p j w N).hom.app ⊤
        (((pullbackPushforwardAdjunction (Spec.map (CommRingCat.ofHom p))).unit.app
          ((pullback (Spec.map (CommRingCat.ofHom i))).obj N)).app ⊤ x) :=
  mappedUnit_apply (CommRingCat.ofHom p) _ (comparison i p j w N).hom x

/-- Normalized lifting takes an iterated unit section to the direct unit section. -/
theorem liftSections_unit (n : moduleSpecΓFunctor.obj N) :
    liftSections i p j w N (specUnit (CommRingCat.ofHom i) N n) =
      specUnit (CommRingCat.ofHom j) N n := by
  rw [liftSections_apply, specUnit_apply, specUnit_apply]
  exact comparison_unit i p j w N n

/-- Normalized lifting transforms arbitrary coefficient scalars by the pair map. -/
theorem liftSections_smul (b : B)
    (x : moduleSpecΓFunctor.obj ((pullback (Spec.map (CommRingCat.ofHom i))).obj N)) :
    liftSections i p j w N (b • x) = p b • liftSections i p j w N x := by
  rw [liftSections_eq_mappedUnit]
  exact mappedUnit_ringHom_smul p _ (comparison i p j w N).hom b x

/-- Scalar multiples of a unit transform by the pair ring map. -/
theorem liftSections_smul_unit (b : B) (n : moduleSpecΓFunctor.obj N) :
    liftSections i p j w N
      (b • specUnit (CommRingCat.ofHom i) N n) =
        p b • specUnit (CommRingCat.ofHom j) N n := by
  rw [liftSections_smul, liftSections_unit]

/-- Naturality of the normalized affine coefficient maps. -/
theorem liftSections_map {i' : A →+* B} {j' : A →+* C} (w' : p.comp i' = j')
    (e : (pullback (Spec.map (CommRingCat.ofHom i))).obj N ⟶
      (pullback (Spec.map (CommRingCat.ofHom i'))).obj N)
    (x : moduleSpecΓFunctor.obj ((pullback (Spec.map (CommRingCat.ofHom i))).obj N)) :
    moduleSpecΓFunctor.map ((comparison i p j w N).inv ≫
      (pullback (Spec.map (CommRingCat.ofHom p))).map e ≫
        (comparison i' p j' w' N).hom) (liftSections i p j w N x) =
      liftSections i' p j' w' N (moduleSpecΓFunctor.map e x) := by
  rw [liftSections_eq_mappedUnit, liftSections_eq_mappedUnit]
  exact mappedUnit_map (CommRingCat.ofHom p) _
    (comparison i p j w N) (comparison i' p j' w' N) e x

end FLT.Mazur.AffineIteratedPullbackSections
