/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffinePairPullbackSections
public import FLT.Mazur.AffineTripleOverlapPullback

/-!
# Third-coordinate sections of the triple overlap

Iterating the second projection comparison gives an injective coefficient
chart with source `S ⊗[R] (S ⊗[R] N)`. The normalization uses the actual
pullback composition isomorphism.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct
open Scheme.Modules
universe u
namespace FLT.Mazur.AffineTripleOverlapCoefficients
open AffineOverlapTensor AffineOverlapPullback AffineTripleOverlapMaps
open AffineTripleOverlapPullback AffineIteratedPullbackSections
open AffinePairPullbackSections
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
variable (M : (Spec (.of S)).Modules) [M.IsQuasicoherent]
/-- Coefficient scalars restricted to the base ring. -/
local instance coefficientModule : Module R (coefficients S M) := Module.compHom _ (algebraMap R S)
local instance : IsScalarTower R S (coefficients S M) :=
  IsScalarTower.of_algebraMap_smul (fun _ _ ↦ rfl)

/-- The second double-overlap projection sheaf. -/
abbrev secondSheaf := (pullback (Spec.map (CommRingCat.ofHom (right R S)))).obj M

local instance : (secondSheaf R S M).IsQuasicoherent :=
  AffineModulePullbackSections.isQuasicoherent_pullback (CommRingCat.ofHom (right R S)) M
/-- Scalar restriction for the intermediate projection sheaf. -/
local instance secondCoefficientModule : Module R (moduleSpecΓFunctor.obj (secondSheaf R S M)) :=
  Module.compHom _ (algebraMap R (S ⊗[R] S))

/-- The three-factor coefficient chart for the last coordinate pullback. -/
def lastSections : S ⊗[R] (S ⊗[R] coefficients S M) ≃+
    moduleSpecΓFunctor.obj (coordinate R S M (coord3 R S)) :=
  (TensorProduct.congr (LinearEquiv.refl R S) (linearSections R S S M)).toAddEquiv.trans
    ((sections R S (S ⊗[R] S) (secondSheaf R S M)).trans
      (moduleSpecΓFunctor.mapIso (comparison (right R S) (pair23 R S).toRingHom
        (coord3 R S) (pair23_right R S) M)).toLinearEquiv.toAddEquiv)

/-- The actual last-coordinate chart is bijective. -/
theorem lastSections_bijective : Function.Bijective (lastSections R S M) :=
  (lastSections R S M).bijective

end FLT.Mazur.AffineTripleOverlapCoefficients
