/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSmoothDividedTerminalCharacter

/-!
# The complete actual terminal tensor output is Laurent scaling

Scalar extension retains the constructed integral input and output. The original
vertical coordinate determines both complete tensor maps at equality depth.
-/

@[expose] public noncomputable section
open IsLocalRing
namespace FLT.Mazur.WeierstrassIntegralChart
open WeierstrassDilatation
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {depth k : ℕ} (D : SplitNodeDepth W π depth)
  (d : WeierstrassDividedDepth.Data W π k) (hk0 : 0 < k) (hk : 2 * k ≤ depth)
  (hp : 2 * k = depth)
local notation "𝕂" => ResidueField R
local notation "C" => SmoothHorizontalResidueRing D
local notation "H" => WeierstrassDilatation.Coordinate W (π ^ k) d.b3 d.b4 d.b6
local notation "A" => ScalarExtension W (π ^ k) d.b3 d.b4 d.b6 𝕂
local notation "e" => smoothDividedSecantResidue D d hk0 hk hp
local notation "hs" => IsRegular.of_ne_zero (pow_ne_zero k D.uniformizer_ne_zero)
local notation "τ" => smoothHorizontalTangentUnit D
local notation "z" => smoothHorizontalConicUnit D
local notation "point" => terminalTensorLaurentPoint D k hk0 hk d.b3 d.b4 d.b6
  d.factor3 d.factor4 d.factor6 hp

/-- Scalar extension of the actual integral divided input on the secant residue source. -/
def smoothDividedTerminalTensorInput : A →ₐ[𝕂] C :=
  AlgHom.liftEquiv R 𝕂 H C ((e).comp (smoothDividedSecantInput d))

/-- Scalar extension of the constructed genuine integral divided output. -/
def smoothDividedTerminalTensorOutput : A →ₐ[𝕂] C :=
  AlgHom.liftEquiv R 𝕂 H C ((e).comp (smoothDividedIntegralOutput d hs))

/-- The entire original input tensor map is evaluation at the independent vertical unit. -/
theorem smoothDividedTerminalTensorInput_eq :
    smoothDividedTerminalTensorInput D d hk0 hk hp = point z := by
  apply terminalTensorLaurentPoint_hom_ext D k hk0 hk d.b3 d.b4 d.b6
    d.factor3 d.factor4 d.factor6 hp
  rw [terminalTensorLaurentPoint_y]
  simp only [smoothDividedTerminalTensorInput, tensorY,
    Algebra.TensorProduct.includeRight_apply]
  erw [AlgHom.liftEquiv_tmul]
  rw [one_smul]
  change e (smoothDividedSecantInput d (y W (π ^ k) d.b3 d.b4 d.b6)) = _
  exact smoothDividedTerminal_input_y D d hk0 hk hp

/-- The entire genuine output tensor map is the positive Laurent-character substitution. -/
theorem smoothDividedTerminalTensorOutput_eq :
    smoothDividedTerminalTensorOutput D d hk0 hk hp = point (τ * z) := by
  apply terminalTensorLaurentPoint_eq_of_character D k hk0 hk d.b3 d.b4 d.b6
    d.factor3 d.factor4 d.factor6 hp
  simp only [smoothDividedTerminalTensorOutput, tensorY,
    Algebra.TensorProduct.includeRight_apply]
  erw [AlgHom.liftEquiv_tmul]
  rw [one_smul]
  change e (smoothDividedIntegralOutput d hs (y W (π ^ k) d.b3 d.b4 d.b6)) = _
  exact smoothDividedTerminal_output_y D d hk0 hk hp

end FLT.Mazur.WeierstrassIntegralChart
