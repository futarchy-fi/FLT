/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.ProjectiveLineEndpointReversal
public import FLT.Mazur.ProjectiveLineActionTorus
public import FLT.Mazur.ProjectiveLineProductTorusRestriction
public import FLT.Mazur.PolygonSplitIdentityGroup

/-!
# Endpoint reversal conjugates universal scaling

The identity holds with the full multiplicative group as parameter. Restrict
first to its actual torus multiplication, then extend across both endpoints
by density in the separated projective line.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory MonObj GrpObj
open scoped LaurentPolynomial
namespace FLT.Mazur.ProjectiveLine
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable (K : Type u) [Field K]
local notation "T" => MultiplicativeGroupScheme.gm K
local notation "L" => PolygonPinching.component K
local notation "j" => PolygonPinching.torusToComponent K
local notation "r" => Iso.hom (endpointReversalOverIso K)
local notation "a" => ProjectiveLineUniversalAction.act K

/-- The marked projective reflection restricts to actual group inversion. -/
@[reassoc] theorem torus_endpointReversal : j ≫ r = ι[T] ≫ j := by
  apply Over.OverMorphism.ext
  change (overlapLeft K ≫ left K) ≫ endpointReversal K = ι[T].left ≫ _
  rw [Category.assoc, left_endpointReversal]
  have hi : ι[T].left = (inversion K).hom :=
    PolygonSplitGroup.reciprocalGroupIso_left K
  rw [hi]
  exact endpointReversal_overlap K

/-- Reverse both the universal parameter and coordinate before scaling. -/
@[reassoc] theorem universalAction_endpointReversal :
    a ≫ r = (ι[T] ⊗ₘ r) ≫ a := by
  let _ : IsSeparated (L).hom := (PolygonProper.projectiveLine K).toIsSeparated
  change a ≫ r = (ι[T] ⊗ₘ r) ≫ a
  apply ProjectiveLineProductCharts.product_hom_ext_torus K K[T;T⁻¹]
  change T ◁ j ≫ a ≫ r = T ◁ j ≫ (ι[T] ⊗ₘ r) ≫ a
  rw [ProjectiveLineActionTorus.torus_act_assoc,
    whiskerLeft_comp_tensorHom_assoc, torus_endpointReversal,
    ← tensorHom_comp_whiskerLeft_assoc, ProjectiveLineActionTorus.torus_act]
  simpa only [Category.assoc] using congrArg (· ≫ j) (IsMonHom.mul_hom ι[T])

/-- Conjugation on the whole projective line inverts the universal parameter. -/
theorem endpointReversal_conjugate_universalAction :
    T ◁ r ≫ a ≫ r = ι[T] ▷ L ≫ a := by
  rw [universalAction_endpointReversal, whiskerLeft_comp_tensorHom_assoc]
  have hr : r ≫ r = 𝟙 L := (endpointReversalOverIso K).hom_inv_id
  rw [hr, tensorHom_id]

end FLT.Mazur.ProjectiveLine
