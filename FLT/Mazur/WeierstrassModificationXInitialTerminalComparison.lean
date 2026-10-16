/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXInitialTerminalNodeBoundary
public import FLT.Mazur.WeierstrassModificationXArithmeticPunctureCover

/-!
# Full initial puncture coordinates on the original terminal transition

The original standard D(p) restriction and terminal Laurent evaluation
agree after the constructed initial parameter isomorphism, on every function.
-/

@[expose] public noncomputable section
open Polynomial AlgebraicGeometry CategoryTheory
open scoped LaurentPolynomial TensorProduct
namespace FLT.Mazur.WeierstrassModificationX
open PolygonArithmeticStages WeierstrassSuccessiveX
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
universe u
variable {R : Type u} [CommRing R] (π : R) (m : ℕ)
  (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (ha : IsUnit W.a₁) (hs : π ∣ s) (h2 : π ∣ W.a₂)
  (h3 : π ∣ b3) (h4 : π ∣ b4) (h6 : π ∣ b6) (opposite : Bool)
local notation "Q" => Quotient R π m
local notation "q" => algebraMap R Q
local notation "U" => W.map q
local notation "J" => ideal Q (parameter R π m)
local notation "hJ" => arithmeticParameterIdeal_nilpotent π m
local notation "r" => WeierstrassDilatation.terminalTangentRoot U (q s) J hJ (ha.map q)
  (arithmeticCoefficient_mem π m hs) (arithmeticCoefficient_mem π m h2)
local notation "hrI" => WeierstrassDilatation.terminalTangentRoot_mem U (q s) J hJ (ha.map q)
  (arithmeticCoefficient_mem π m hs) (arithmeticCoefficient_mem π m h2)
local notation "hr" => WeierstrassDilatation.terminalTangentRoot_equation U (q s) J hJ (ha.map q)
  (arithmeticCoefficient_mem π m hs) (arithmeticCoefficient_mem π m h2)
local notation "h4₀" => arithmeticCoefficient_mem π m h4
local notation "h6₀" => arithmeticCoefficient_mem π m h6
local notation "v" => laurentBranchSlope U (q s) (q b3) (q b4) (q b6) J hJ (ha.map q)
  (arithmeticCoefficient_mem π m hs) (arithmeticCoefficient_mem π m h2)
  (arithmeticCoefficient_mem π m h3) h4₀ h6₀ opposite
local notation "hv" => laurentBranchSlope_equation U (q s) (q b3) (q b4) (q b6) J hJ
  (ha.map q) (arithmeticCoefficient_mem π m hs) (arithmeticCoefficient_mem π m h2)
  (arithmeticCoefficient_mem π m h3) h4₀ h6₀ opposite
local notation "G" => tensorInitialTerminalLaurent W s b3 b4 b6 Q v hv
local notation "c" => WeierstrassDilatation.arithmeticTerminalSmoothing π m W s
  b3 b4 b6 ha hs h2 h4 h6
local notation "e" => WeierstrassDilatation.arithmeticTerminalNodeIso π m W s
  b3 b4 b6 ha hs h2 h4 h6

local notation "E" => initialTerminalArithmeticNodeEvaluation
  π m W s b3 b4 b6 ha hs h2 h3 h4 h6 opposite
local notation "P" => arithmeticInitialPunctureIso π m W s b3 b4 b6 ha hs h2 h3 h4 h6
local notation "u" => arithmeticInitialPunctureToTensorBoundary
  π m W s b3 b4 b6 ha h2 h3 h4 h6 opposite hs
local notation "t₀" => t W s b3 b4 b6
local notation "x" => WeierstrassDilatation.x W s b3 b4 b6
local notation "a" => overlapEquiv W s b3 b4 b6
local notation "i" => PrincipalOpenTensor.inclusion Q t₀
local notation "B" => Iso.hom (PrincipalOpenTensor.transitionIso Q x t₀ a) ≫
  PrincipalOpenTensor.inclusion Q x
local notation "L" => tensorInitialLaurentLocalization W s b3 b4 b6 Q v hv

attribute [local irreducible] arithmeticInitialPunctureIso
  arithmeticInitialPunctureToTensorBoundary tensorInitialLaurentLocalization
  initialTerminalArithmeticNodeEvaluation

/-- The puncture isomorphism retains the full original tensor boundary restriction. -/
@[reassoc] theorem arithmeticInitialPunctureIso_tensor_boundary :
    (P).hom ≫ u = Spec.map (CommRingCat.ofHom (L).toRingHom) := by
  apply (cancel_mono i).mp
  rw [Category.assoc, arithmeticInitialPunctureToTensorBoundary_comp,
    ← Category.assoc, arithmeticInitialPunctureIso_boundary,
    tensorInitialLaurentLocalization_spec]
  cases opposite
  · exact arithmeticInitialTensorNode_boundary π m W s b3 b4 b6 ha h2 h3 h4 h6 hs
  · exact arithmeticOppositeInitialTensorNode_boundary π m W s b3 b4 b6 ha h2 h3 h4 h6 hs

/-- The constructed initial parameter retains the whole normalized terminal morphism. -/
@[reassoc] theorem arithmeticInitialPunctureIso_terminal_boundary :
    (P).hom ≫ u ≫ B ≫ (e).inv = Spec.map (CommRingCat.ofHom (E).toRingHom) := by
  apply (cancel_mono (e).hom).mp
  rw [Category.assoc, Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id,
    ← Category.assoc, arithmeticInitialPunctureIso_tensor_boundary,
    initialTerminalArithmeticNodeEvaluation_boundary]
  exact (tensorInitialTerminalLaurent_spec W s b3 b4 b6 Q v hv).symm

/-- The full normalized original initial boundary is an open immersion. -/
theorem initialTerminalArithmeticNodeEvaluation_isOpenImmersion :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom (E).toRingHom)) := by
  rw [← arithmeticInitialPunctureIso_terminal_boundary π m W s b3 b4 b6 ha hs h2 h3 h4 h6]
  infer_instance

end FLT.Mazur.WeierstrassModificationX
