/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteSchemeLineCohomology
public import FLT.Mazur.AffineModuleGlobalSections
public import FLT.Mazur.ClosedLineProjectionFormula

/-!
# Line twists on finite schemes

A line on a finite scheme over a field is globally trivial. Consequently its
tensor product with any module sheaf is isomorphic to that module sheaf. The
closed projection formula transports this to arbitrary finite closed coefficients.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace FLT.Mazur.FCurve

open ModuleSheafTensor FLT.Mazur.AffineModuleGlobalSections

variable {k : Type} [Field k] {X Z : Scheme}

/-- A line on a finite scheme is trivial, via its actual affine sections. -/
def finiteSchemeLineIso (f : Z ⟶ Spec (CommRingCat.of k)) [IsFinite f]
    {L : Z.Modules} (hL : LocallyFreeRankOne L) : L ≅ structureModule Z := by
  have : IsAffine Z := isAffine_of_isAffineHom f
  have := hL.isFinitePresentation
  have := (structureModule_locallyFreeRankOne (X := Z)).isFinitePresentation
  let e := finiteSchemeSectionsEquiv f (moduleSheafDual L) L hL.dual hL
    (lineSheafDualEvaluationIso hL)
  exact (asIso ((affineAdjunction Z).counit.app L)).symm ≪≫
    (affineTilde Z).mapIso e.toModuleIso ≪≫
    asIso ((affineAdjunction Z).counit.app (structureModule Z))

/-- Twisting any module sheaf on a finite scheme by a line preserves its isomorphism class. -/
def finiteSchemeLineTwistIso (f : Z ⟶ Spec (CommRingCat.of k)) [IsFinite f]
    (M : Z.Modules) {L : Z.Modules} (hL : LocallyFreeRankOne L) : tensor M L ≅ M :=
  congr (Iso.refl M) (finiteSchemeLineIso f hL) ≪≫ rightUnitor M

/-- Every scalar cohomology dimension is unchanged by a line twist on a finite scheme. -/
theorem finiteScheme_lineTwist_finrank (f : Z ⟶ Spec (CommRingCat.of k)) [IsFinite f]
    (M : Z.Modules) {L : Z.Modules} (hL : LocallyFreeRankOne L) (n : ℕ) :
    Module.finrank k (ModuleScalarH f (tensor M L) n) =
      Module.finrank k (ModuleScalarH f M n) :=
  ((moduleScalarHFunctor f n).mapIso
    (finiteSchemeLineTwistIso f M hL)).toLinearEquiv.finrank_eq

/-- A line twist preserves arbitrary coefficients pushed forward from a finite closed scheme. -/
def finiteClosedLineTwistIso (i : Z ⟶ X)
    (f : X ⟶ Spec (CommRingCat.of k)) [IsFinite (i ≫ f)]
    (M : Z.Modules) {L : X.Modules} (hL : LocallyFreeRankOne L) :
    tensor ((pushforward i).obj M) L ≅ (pushforward i).obj M :=
  (ClosedLineProjectionFormula.projectionIso i M L hL).symm ≪≫
    (pushforward i).mapIso (finiteSchemeLineTwistIso (i ≫ f) M (hL.pullback i))

/-- Finite closed coefficients have unchanged scalar cohomology dimensions after a line twist. -/
theorem finiteClosed_lineTwist_finrank (i : Z ⟶ X)
    (f : X ⟶ Spec (CommRingCat.of k)) [IsFinite (i ≫ f)]
    (M : Z.Modules) {L : X.Modules} (hL : LocallyFreeRankOne L) (n : ℕ) :
    Module.finrank k (ModuleScalarH f (tensor ((pushforward i).obj M) L) n) =
      Module.finrank k (ModuleScalarH f ((pushforward i).obj M) n) :=
  ((moduleScalarHFunctor f n).mapIso
    (finiteClosedLineTwistIso i f M hL)).toLinearEquiv.finrank_eq

end FLT.Mazur.FCurve
