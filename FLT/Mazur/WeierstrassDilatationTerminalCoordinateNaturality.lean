/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDilatationTangentCoefficientNaturality
public import FLT.Mazur.WeierstrassDilatationInverseNaturality
public import FLT.Mazur.DifferenceNodeCorrectionNaturality
public import FLT.Mazur.NilpotentQuadraticDifferenceTowerNaturality

/-!
# Both full terminal node coordinates commute with coefficient extension

The actual cubic coefficient map preserves the inverse polynomial, critical
translation and complete quadratic correction of the normalization.
-/

@[expose] public noncomputable section
open Polynomial
namespace FLT.Mazur.WeierstrassDilatation
variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  (W : WeierstrassCurve R) (s b3 b4 b6 : R) (r : R[X])
  (I : Ideal R) (hI : IsNilpotent I) (J : Ideal S) (hJ : IsNilpotent J)
  (hf : I ≤ J.comap (algebraMap R S)) (hrI : r ∈ I.map C) (ha : IsUnit W.a₁)
  (h4 : b4 ∈ I) (h6 : b6 ∈ I)
local notation "f" => algebraMap R S
local notation "U" => W.map f
local notation "A" => ExtendedCoordinate W s b3 b4 b6 S
local notation "g" => coefficientMap W s b3 b4 b6 S
local notation "hrJ" => terminalPolynomialIdeal_map f I J hf hrI
local notation "F" => terminalInversePolynomial W r I hI hrI ha
local notation "H" => terminalProductCorrection b3 b4 b6 r F
local notation "hH" => terminalProductCorrection_mem b3 b4 b6 r F I h4 h6 hrI
local notation "K" => DifferenceNode.normalCorrection H b3 I hI hH
local notation "hK" => DifferenceNode.normalCorrection_mem H b3 I hI hH
local notation "a" => DifferenceNode.criticalSlope H b3 I hI hH

/-- The complete first corrected coordinate restricts with the original cubic coefficients. -/
theorem terminalNodeSmall_coefficients :
    g (terminalNodeSmall W s b3 b4 b6 r I hI hrI ha h4 h6) =
      terminalNodeSmall U (f s) (f b3) (f b4) (f b6) (r.map f)
        J hJ hrJ (ha.map f) (hf h4) (hf h6) := by
  rw [terminalNodeSmall_map, terminalSmallTangent_coefficients,
    terminalOppositeTangent_coefficients]
  rw [IsScalarTower.algebraMap_eq R S A,
    NilpotentQuadraticDifference.smallFactor_tower f (algebraMap S A) K I hI J hJ hf hK]
  have hKmap := DifferenceNode.normalCorrection_map f H b3 I hI J hJ hf hH
  have hamap := DifferenceNode.criticalSlope_map f H b3 I hI J hJ hf hH
  simp only [terminalConstructedCorrection_map f W r I hI J hJ hf hrI ha b3 b4 b6]
    at hKmap hamap
  simp only [RingHom.comp_apply, hamap, hKmap, terminalNodeSmall]

/-- The complete opposite corrected coordinate restricts with the same coefficients. -/
theorem terminalNodeOpposite_coefficients :
    g (terminalNodeOpposite W s b3 b4 b6 r I hI hrI ha h4 h6) =
      terminalNodeOpposite U (f s) (f b3) (f b4) (f b6) (r.map f)
        J hJ hrJ (ha.map f) (hf h4) (hf h6) := by
  rw [terminalNodeOpposite_map, terminalSmallTangent_coefficients,
    terminalOppositeTangent_coefficients]
  rw [IsScalarTower.algebraMap_eq R S A,
    NilpotentQuadraticDifference.oppositeFactor_tower f (algebraMap S A) K I hI J hJ hf hK]
  have hKmap := DifferenceNode.normalCorrection_map f H b3 I hI J hJ hf hH
  have hamap := DifferenceNode.criticalSlope_map f H b3 I hI J hJ hf hH
  simp only [terminalConstructedCorrection_map f W r I hI J hJ hf hrI ha b3 b4 b6]
    at hKmap hamap
  simp only [RingHom.comp_apply, hamap, hKmap, terminalNodeOpposite]

end FLT.Mazur.WeierstrassDilatation
