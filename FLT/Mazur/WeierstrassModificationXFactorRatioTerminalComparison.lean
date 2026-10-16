/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXArithmeticFactorRatioPuncture
public import FLT.Mazur.WeierstrassModificationXInitialTerminalComparison

/-!
# The corrected initial parameter on the original terminal tensor transition

The full squared-factor Laurent reparametrization is carried through both
original tensor branches. The terminal smoothing is retained in its entirety.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped LaurentPolynomial TensorProduct
namespace FLT.Mazur.WeierstrassModificationX
open PolygonArithmeticStages WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
universe u
variable {R : Type u} [CommRing R] (π : R) (m : ℕ)
  (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (ha : IsUnit W.a₁) (hs : π ∣ s) (h2 : π ∣ W.a₂)
  (h3 : π ∣ b3) (h4 : π ∣ b4) (h6 : π ∣ b6) (opposite : Bool)
local notation "Q" => Quotient R π m
local notation "q" => algebraMap R Q
local notation "J" => ideal Q (parameter R π m)
local notation "c" => WeierstrassDilatation.arithmeticTerminalSmoothing π m W s
  b3 b4 b6 ha hs h2 h4 h6
local notation "e" => WeierstrassDilatation.arithmeticTerminalNodeIso π m W s
  b3 b4 b6 ha hs h2 h4 h6
local notation "E" => initialTerminalArithmeticNodeEvaluation
  π m W s b3 b4 b6 ha hs h2 h3 h4 h6 opposite
local notation "F" => factorRatioLaurentEquiv (W.map q) (ha.map q)
  (q s) (q b3) (q b4) (q b6) J (arithmeticParameterIdeal_nilpotent π m)
  (arithmeticCoefficient_mem π m hs) (arithmeticCoefficient_mem π m h2)
  (arithmeticCoefficient_mem π m h3) (arithmeticCoefficient_mem π m h4)
  (arithmeticCoefficient_mem π m h6)
local notation "f" => arithmeticFactorRatioLaurentIso π m W s b3 b4 b6 ha hs h2 h3 h4 h6
local notation "P" => arithmeticFactorRatioPunctureIso π m W s b3 b4 b6 ha hs h2 h3 h4 h6
local notation "u" => arithmeticInitialPunctureToTensorBoundary
  π m W s b3 b4 b6 ha h2 h3 h4 h6 opposite hs
local notation "t₀" => t W s b3 b4 b6
local notation "x" => WeierstrassDilatation.x W s b3 b4 b6
local notation "a" => overlapEquiv W s b3 b4 b6
local notation "B" => Iso.hom (PrincipalOpenTensor.transitionIso Q x t₀ a) ≫
  PrincipalOpenTensor.inclusion Q x
attribute [local irreducible] arithmeticInitialPunctureIso
  arithmeticInitialPunctureToTensorBoundary initialTerminalArithmeticNodeEvaluation
  factorRatioLaurentEquiv

/-- The original terminal evaluation with the complete corrected initial Laurent parameter. -/
def factorRatioTerminalEvaluation : NodalFiber.Coordinate c →ₐ[Q] Q[T;T⁻¹] :=
  (F).symm.toAlgHom.comp E
local notation "E'" => factorRatioTerminalEvaluation
  π m W s b3 b4 b6 ha hs h2 h3 h4 h6 opposite

/-- The corrected terminal boundary is the original boundary after the exact inverse correction. -/
@[reassoc] theorem factorRatioTerminalEvaluation_spec :
    Spec.map (CommRingCat.ofHom (E').toRingHom) =
      (f).inv ≫ Spec.map (CommRingCat.ofHom (E).toRingHom) := by
  change Spec.map _ = Spec.map (CommRingCat.ofHom (F).symm.toRingHom) ≫ Spec.map _
  rw [← Spec.map_comp]
  rfl

/-- Both original tensor transition squares retain the full corrected initial parameter. -/
@[reassoc] theorem arithmeticFactorRatioPunctureIso_terminal_boundary :
    (P).hom ≫ u ≫ B ≫ (e).inv = Spec.map (CommRingCat.ofHom (E').toRingHom) := by
  rw [factorRatioTerminalEvaluation_spec]
  change ((f).inv ≫
    (arithmeticInitialPunctureIso π m W s b3 b4 b6 ha hs h2 h3 h4 h6).hom) ≫ _ = _
  rw [Category.assoc, arithmeticInitialPunctureIso_terminal_boundary]

/-- Reparametrization preserves the whole terminal smoothing, with no reduction or truncation. -/
theorem factorRatioTerminalEvaluation_product :
    E' (NodalFiber.p c) * E' (NodalFiber.q c) = algebraMap Q Q[T;T⁻¹] c := by
  rw [← map_mul, NodalFiber.relation, AlgHom.commutes]

/-- The corrected full terminal boundary remains an open immersion. -/
theorem factorRatioTerminalEvaluation_isOpenImmersion :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom (E').toRingHom)) := by
  rw [factorRatioTerminalEvaluation_spec]
  let _ := initialTerminalArithmeticNodeEvaluation_isOpenImmersion
    π m W s b3 b4 b6 ha hs h2 h3 h4 h6 opposite
  infer_instance

end FLT.Mazur.WeierstrassModificationX
