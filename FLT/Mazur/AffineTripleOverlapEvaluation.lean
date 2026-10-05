/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineTripleOverlapCoefficients

/-!
# Evaluation of the last-coordinate coefficient chart

Retaining the outer additive-equivalence chain fixes the scalar instances
throughout evaluation. The inner unequal-factor chart agrees with the
specified second overlap chart. Pure tensors therefore evaluate to the
iterated pullback-unit expression below.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct
open Scheme.Modules
open FLT.Mazur FLT.Mazur.AffinePairPullbackSections FLT.Mazur.AffineIteratedPullbackSections
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
namespace FLT.Mazur.AffineTripleOverlapEvaluation
open AffineTripleOverlapCoefficients AffineTripleOverlapPullback AffineTripleOverlapMaps
open AffineOverlapTensor AffineOverlapPullback
variable (M : (Spec (.of S)).Modules) [M.IsQuasicoherent]
/-- Restrict coefficient scalars to the base ring. -/
local instance : Module R (coefficients S M) := Module.compHom _ (algebraMap R S)
local instance : IsScalarTower R S (coefficients S M) :=
  IsScalarTower.of_algebraMap_smul (fun _ _ ↦ rfl)
local instance : (secondSheaf R S M).IsQuasicoherent :=
  AffineModulePullbackSections.isQuasicoherent_pullback (CommRingCat.ofHom (right R S)) M
/-- Restrict the intermediate projection coefficients to the base ring. -/
local instance : Module R (moduleSpecΓFunctor.obj (secondSheaf R S M)) :=
  Module.compHom _ (algebraMap R (S ⊗[R] S))
/-- Evaluate the outer tensor while retaining the actual comparison chain. -/
theorem lastSections_outer_apply (s : S) (x : S ⊗[R] coefficients S M) :
    lastSections R S M (s ⊗ₜ[R] x) =
      ((sections R S (S ⊗[R] S) (secondSheaf R S M)).trans
        (moduleSpecΓFunctor.mapIso (comparison (right R S) (pair23 R S).toRingHom
          (coord3 R S) (pair23_right R S) M)).toLinearEquiv.toAddEquiv)
          (s ⊗ₜ[R] linearSections R S S M x) := by
  unfold lastSections
  rw [AddEquiv.trans_apply]
  congr 1

/-- The unequal-factor linear chart agrees with the overlap second chart. -/
theorem linearSections_eq_secondSections (x : S ⊗[R] coefficients S M) :
    linearSections R S S M x = secondSections R S M x := by
  induction x using TensorProduct.inductionOn with
  | tmul s n =>
    exact (sections_tmul R S S M s n).trans (secondSections_tmul R S M s n).symm
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The outer evaluation uses the specified second coefficient chart. -/
theorem lastSections_outer_second (s : S) (x : S ⊗[R] coefficients S M) :
    lastSections R S M (s ⊗ₜ[R] x) =
      ((sections R S (S ⊗[R] S) (secondSheaf R S M)).trans
        (moduleSpecΓFunctor.mapIso (comparison (right R S) (pair23 R S).toRingHom
          (coord3 R S) (pair23_right R S) M)).toLinearEquiv.toAddEquiv)
          (s ⊗ₜ[R] secondSections R S M x) := by
  rw [lastSections_outer_apply, linearSections_eq_secondSections]

/-- Evaluate both coefficient tensors before moving scalars through the comparison. -/
theorem lastSections_tmul_iterated (s t : S) (n : coefficients S M) :
    lastSections R S M (s ⊗ₜ[R] (t ⊗ₜ[R] n)) =
      ((sections R S (S ⊗[R] S) (secondSheaf R S M)).trans
        (moduleSpecΓFunctor.mapIso (comparison (right R S) (pair23 R S).toRingHom
          (coord3 R S) (pair23_right R S) M)).toLinearEquiv.toAddEquiv)
          (s ⊗ₜ[R] ((t ⊗ₜ[R] (1 : S)) • specUnit (CommRingCat.ofHom (right R S)) M n)) := by
  rw [lastSections_outer_second, secondSections_tmul, specUnit_apply]
end FLT.Mazur.AffineTripleOverlapEvaluation
