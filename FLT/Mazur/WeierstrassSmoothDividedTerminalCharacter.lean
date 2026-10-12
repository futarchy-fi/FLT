/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSmoothDividedSecantResidue
public import FLT.Mazur.WeierstrassSplitDepthNormalizedDividedAction
public import FLT.Mazur.WeierstrassSmoothHorizontalLaurentEvaluation

/-!
# The actual terminal output has the positive tangent character

Apply the original conormal calculation to the constructed integral divided
input, genuine output lift and actual secant residue factor. No action equality
or output-coordinate formula is supplied as a hypothesis.
-/

@[expose] public noncomputable section
open IsLocalRing
namespace FLT.Mazur.WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {depth k : ℕ} (D : SplitNodeDepth W π depth)
  (d : WeierstrassDividedDepth.Data W π k) (hk0 : 0 < k) (hk : 2 * k ≤ depth)
  (hp : 2 * k = depth)
local notation "C" => SmoothHorizontalResidueRing D
local notation "S" => SmoothDividedProductRing W (π ^ k) d.b3 d.b4 d.b6
local notation "T" => SmoothDividedSecantRing d
local notation "a" => smoothDividedLeft W (π ^ k) d.b3 d.b4 d.b6
local notation "c" => smoothDividedRight W (π ^ k) d.b3 d.b4 d.b6
  d.factor3 d.factor4 d.factor6
local notation "v" => smoothDividedY W (π ^ k) d.b3 d.b4 d.b6
local notation "e" => smoothDividedSecantResidue D d hk0 hk hp
local notation "hs" => IsRegular.of_ne_zero (pow_ne_zero k D.uniformizer_ne_zero)
local notation "L" => smoothDividedSecantInput d
local notation "M" => smoothDividedIntegralOutput d hs
local notation "dx" => WeierstrassDilatation.x W (π ^ k) d.b3 d.b4 d.b6
local notation "dy" => WeierstrassDilatation.y W (π ^ k) d.b3 d.b4 d.b6
local notation "τ" => smoothHorizontalTangentUnit D

/-- Both actual integral output tangent coordinates have the original reciprocal characters. -/
theorem smoothDividedTerminal_normalized :
    e (M dy) = (τ : C) * e (L dy) ∧
      e (M dy + algebraMap R T W.a₁ * M dx) =
        (↑τ⁻¹ : C) * e (L dy + algebraMap R T W.a₁ * L dx) := by
  apply splitDepthDivided_normalized D d hk false (smoothDividedSecantPresentation d)
    (AlgHom.id R T) (smoothDividedSecant_base_regular d hs) L M
    (by simpa only [AlgHom.id_comp] using smoothDividedSecantInput_original d)
    (by simpa only [AlgHom.id_comp, smoothDividedSecantOutput] using
      smoothDividedIntegralOutput_original d hs)
    (e).toRingHom
    (by rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes]
        exact smoothDividedResidue_scale D hk0)
    (by change (maximalIdeal R).map (algebraMap R T) ≤ RingHom.ker (e).toRingHom
        exact smoothDividedSecantResidue_maximal D d hk0 hk hp)
    (by omega) (fun i => e (algebraMap S T (v (coord W 1 i))))
    (secantPairSmooth_cross W a c v
      (smoothDivided_common W (π ^ k) d.b3 d.b4 d.b6) (e).toRingHom) τ
  change (τ : C) = 1 + e (algebraMap R T W.a₁) *
    e (algebraMap S T (v (coord W 1 0)))
  rw [AlgHom.commutes, smoothDividedSecantResidue_base]
  exact smoothDividedProductResidue_tangent D d hk0 hk hp

/-- The retained divided input has the independent original Laurent unit. -/
theorem smoothDividedTerminal_input_y :
    e (L dy) = (smoothHorizontalConicUnit D : C) := by
  change e (algebraMap S T (smoothDividedInput W (π ^ k) d.b3 d.b4 d.b6 dy)) = _
  rw [smoothDividedSecantResidue_base, smoothDividedProductResidue_input,
    smoothDividedTerminalResidue_y, smoothHorizontalConicUnit_val]

/-- The constructed output's original divided vertical coordinate has the positive character. -/
theorem smoothDividedTerminal_output_y :
    e (M dy) = (τ : C) * (smoothHorizontalConicUnit D : C) := by
  rw [(smoothDividedTerminal_normalized D d hk0 hk hp).1,
    smoothDividedTerminal_input_y]

end FLT.Mazur.WeierstrassIntegralChart
