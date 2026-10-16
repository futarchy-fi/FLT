/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXInitialTerminalImages

/-!
# Full initial Laurent boundaries are the selected standard terminal punctures

The isomorphism preserves every function of the original normalized terminal
boundary. The original Laurent evaluation gives its actual parameter map.
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
local notation "δ" => ite (opposite = true) (NodalFiber.p c) (NodalFiber.q c)
local notation "D" => Localization.Away δ
local notation "i" => Spec.map (CommRingCat.ofHom (algebraMap (NodalFiber.Coordinate c) D))
local notation "B" => Spec.map (CommRingCat.ofHom (AlgHom.toRingHom E))

attribute [local irreducible] initialTerminalArithmeticNodeEvaluation

/-- Identify each full original initial Laurent boundary with its standard terminal puncture. -/
def initialTerminalArithmeticPunctureIso : Spec (.of Q[T;T⁻¹]) ≅ Spec (.of D) := by
  let _ := initialTerminalArithmeticNodeEvaluation_isOpenImmersion
    π m W s b3 b4 b6 ha hs h2 h3 h4 h6 opposite
  let _ : IsOpenImmersion i := IsOpenImmersion.of_isLocalization δ
  apply IsOpenImmersion.isoOfRangeEq B i
  exact (initialTerminalArithmeticNodeEvaluation_range
    π m W s b3 b4 b6 ha hs h2 h3 h4 h6 opposite).trans
      (PrimeSpectrum.localization_away_comap_range D δ).symm

/-- The standard terminal identification retains the entire original initial boundary. -/
@[reassoc] theorem initialTerminalArithmeticPunctureIso_boundary :
    (initialTerminalArithmeticPunctureIso π m W s b3 b4 b6 ha hs h2 h3 h4 h6 opposite).hom ≫
      i = B := by
  let _ := initialTerminalArithmeticNodeEvaluation_isOpenImmersion
    π m W s b3 b4 b6 ha hs h2 h3 h4 h6 opposite
  let _ : IsOpenImmersion i := IsOpenImmersion.of_isLocalization δ
  exact IsOpenImmersion.isoOfRangeEq_hom_fac B i
    ((initialTerminalArithmeticNodeEvaluation_range
      π m W s b3 b4 b6 ha hs h2 h3 h4 h6 opposite).trans
        (PrimeSpectrum.localization_away_comap_range D δ).symm)

/-- The actual parameter map localizes the original full normalized initial boundary evaluation. -/
def initialTerminalArithmeticPunctureEvaluation : D →ₐ[Q] Q[T;T⁻¹] :=
  IsLocalization.Away.liftAlgHom δ (f := E)
    (initialTerminalArithmeticSelected_unit π m W s b3 b4 b6 ha hs h2 h3 h4 h6 opposite)
local notation "F" => initialTerminalArithmeticPunctureEvaluation
  π m W s b3 b4 b6 ha hs h2 h3 h4 h6 opposite

/-- Every original terminal function is retained in the complete puncture parameter map. -/
theorem initialTerminalArithmeticPunctureEvaluation_base (z : NodalFiber.Coordinate c) :
    F (algebraMap (NodalFiber.Coordinate c) D z) = E z := by
  rw [initialTerminalArithmeticPunctureEvaluation, IsLocalization.Away.liftAlgHom_apply,
    IsLocalization.Away.lift_eq]
  rfl

/-- The full parameter evaluation is precisely the standard terminal puncture isomorphism. -/
theorem initialTerminalArithmeticPunctureEvaluation_spec :
    Spec.map (CommRingCat.ofHom (F).toRingHom) =
      (initialTerminalArithmeticPunctureIso π m W s b3 b4 b6 ha hs h2 h3 h4 h6 opposite).hom := by
  let _ : IsOpenImmersion i := IsOpenImmersion.of_isLocalization δ
  apply (cancel_mono i).mp
  rw [initialTerminalArithmeticPunctureIso_boundary, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  exact RingHom.ext (initialTerminalArithmeticPunctureEvaluation_base
    π m W s b3 b4 b6 ha hs h2 h3 h4 h6 opposite)

end FLT.Mazur.WeierstrassModificationX
