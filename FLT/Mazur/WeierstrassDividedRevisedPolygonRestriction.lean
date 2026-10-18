/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedRevisedPolygon
public import Mathlib.CategoryTheory.Functor.OfSequence

/-!
# The revised target over the original arithmetic quotient system

Every full node restriction is the actual coefficient substitution. The
terminal's changed smoothing follows its proved quotient square, and no
higher-order normalization of the original atlas is asserted here.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [IsDomain R] {W : WeierstrassCurve R} {π : R}
  (hπ : π ≠ 0) {n : ℕ} (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "p" => fun m ↦ arithmeticRevisedPolygonParameter data H m j hj u hu
local notation "τ" => fun m ↦ arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m
local notation "σ" => fun m ↦ arithmeticTerminalChangedSmoothing data H m j hj u hu
local notation "N" => 2 * (j + 1) + 3

/-- The revised global target retains the original adjacent quotient homomorphism. -/
def arithmeticRevisedPolygonRestriction (m : ℕ) :
    arithmeticRevisedPolygon data H m j hj u hu ⟶
      arithmeticRevisedPolygon data H (m + 1) j hj u hu :=
  PolygonVariableSmoothing.parameterProjection (restriction R π m).toRingHom N
    (p (m + 1)) (p m)
    (arithmeticRevisedPolygonParameter_restriction data H m j hj u hu hπ) (by omega)

local notation "q" => arithmeticRevisedPolygonRestriction hπ data H j hj u hu

/-- The full common terminal square uses its actual changed-parameter coefficient map. -/
@[reassoc] theorem arithmeticRevisedPolygonTerminalChart_restriction (m : ℕ) :
    arithmeticRevisedPolygonTerminalChart data H m j hj u hu ≫ q m =
      Spec.map (CommRingCat.ofHom (ringMap (restriction R π m).toRingHom
        (σ (m + 1)) (σ m)
        (arithmeticTerminalChangedSmoothing_restriction data H m j hj u hu hπ))) ≫
      arithmeticRevisedPolygonTerminalChart data H (m + 1) j hj u hu :=
  PolygonVariableSmoothing.chartWithParameter_projection _ N (p (m + 1)) (by omega)
    (restriction R π m).toRingHom (p m) _ 0 _ _ _ _ _

/-- Every full retained node square keeps the unchanged original normalized parameter. -/
@[reassoc] theorem arithmeticRevisedPolygonRetainedChart_restriction
    (m : ℕ) (a : Fin (j + 1)) (b : Bool) :
    arithmeticRevisedPolygonRetainedChart data H m j hj u hu a b ≫ q m =
      Spec.map (CommRingCat.ofHom (ringMap (restriction R π m).toRingHom
        (τ (m + 1)) (τ m)
        (arithmeticInitialMobiusSmoothing_restriction W H.a1_unit (π ^ 1) π m))) ≫
      arithmeticRevisedPolygonRetainedChart data H (m + 1) j hj u hu a b :=
  PolygonVariableSmoothing.chartWithParameter_projection _ N (p (m + 1)) (by omega)
    (restriction R π m).toRingHom (p m) _ _ _ _ _ _ _

/-- Both original initial node squares keep the same exact coefficient map. -/
@[reassoc] theorem arithmeticRevisedPolygonInitialChart_restriction (m : ℕ) (b : Bool) :
    arithmeticRevisedPolygonInitialChart data H m j hj u hu b ≫ q m =
      Spec.map (CommRingCat.ofHom (ringMap (restriction R π m).toRingHom
        (τ (m + 1)) (τ m)
        (arithmeticInitialMobiusSmoothing_restriction W H.a1_unit (π ^ 1) π m))) ≫
      arithmeticRevisedPolygonInitialChart data H (m + 1) j hj u hu b :=
  PolygonVariableSmoothing.chartWithParameter_projection _ N (p (m + 1)) (by omega)
    (restriction R π m).toRingHom (p m) _ _ _ _ _ _ _

/-- The independently constructed target and its full quotient sequence. -/
def arithmeticRevisedPolygonSystem : ℕ ⥤ Scheme := Functor.ofSequence q

/-- Its quotient maps preserve the actual arithmetic base. -/
@[reassoc] theorem arithmeticRevisedPolygonRestriction_base (m : ℕ) :
    q m ≫ arithmeticRevisedPolygonToBase data H (m + 1) j hj u hu =
      arithmeticRevisedPolygonToBase data H m j hj u hu ≫
        Spec.map (CommRingCat.ofHom (restriction R π m).toRingHom) :=
  PolygonVariableSmoothing.parameterProjection_base (restriction R π m).toRingHom N
    (p (m + 1)) (p m) _ (by omega)

end FLT.Mazur.WeierstrassDividedDepth
