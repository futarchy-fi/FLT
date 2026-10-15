/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticTerminalPunctureIso

/-!
# The exact parameter change on each complete terminal puncture

The puncture comparison is the localization of the original normalized
Laurent evaluation. Every original function, and hence both corrected factors,
is retained; the Laurent parameter is not replaced by a residue monomial.
-/

@[expose] public noncomputable section
open Polynomial AlgebraicGeometry CategoryTheory
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages WeierstrassSuccessiveX
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
variable {R : Type} [CommRing R]
  {W : WeierstrassCurve R} {π : R} {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (m : ℕ)
local notation "Q" => Quotient R π m
local notation "q" => algebraMap R Q

variable (j : ℕ) (hj : j + 1 ≤ n)
local notation "d" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "x" => WeierstrassDilatation.x W (π ^ (start + j + 1))
  (Data.b3 d) (Data.b4 d) (Data.b6 d)
local notation "t" => coord W (π ^ (start + j)) π (Data.b3 d) (Data.b4 d) (Data.b6 d) 0
local notation "a" => depthOverlapEquiv W π (start + j) (Data.b3 d) (Data.b4 d) (Data.b6 d)

variable (ha : IsUnit W.a₁) (hs : π ∣ π ^ (start + j)) (h2 : π ∣ W.a₂)
  (h3 : π ∣ (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b3)
  (h4 : π ∣ (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b4)
  (h6 : π ∣ (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6) (opposite : Bool)
local notation "s" => π ^ (start + j + 1)
local notation "U" => W.map q
local notation "J" => ideal Q (parameter R π m)
local notation "hJ" => arithmeticParameterIdeal_nilpotent π m
local notation "hs₂" => dvd_pow_self π (Nat.succ_ne_zero (start + j))
local notation "r" => WeierstrassDilatation.terminalTangentRoot U (q s) J hJ (ha.map q)
  (arithmeticCoefficient_mem π m hs₂) (arithmeticCoefficient_mem π m h2)
local notation "hrI" => WeierstrassDilatation.terminalTangentRoot_mem U (q s) J hJ (ha.map q)
  (arithmeticCoefficient_mem π m hs₂) (arithmeticCoefficient_mem π m h2)
local notation "hr" => WeierstrassDilatation.terminalTangentRoot_equation U (q s) J hJ (ha.map q)
  (arithmeticCoefficient_mem π m hs₂) (arithmeticCoefficient_mem π m h2)
local notation "h4₀" => arithmeticCoefficient_mem π m h4
local notation "h6₀" => arithmeticCoefficient_mem π m h6
local notation "v" => arithmeticBranchSlope π m W (π ^ (start + j))
  (Data.b3 d) (Data.b4 d) (Data.b6 d) ha hs h2 h3 h4 h6 opposite
local notation "hv" => arithmeticBranchSlope_equation π m W (π ^ (start + j))
  (Data.b3 d) (Data.b4 d) (Data.b6 d) ha hs h2 h3 h4 h6 opposite
local notation "G" => tensorTerminalLaurent W π (start + j)
  (Data.b3 d) (Data.b4 d) (Data.b6 d) Q v hv
local notation "c" => WeierstrassDilatation.arithmeticTerminalSmoothing π m W s
  (Data.b3 d) (Data.b4 d) (Data.b6 d) ha hs₂ h2 h4 h6
local notation "e" => WeierstrassDilatation.arithmeticTerminalNodeIso π m W s
  (Data.b3 d) (Data.b4 d) (Data.b6 d) ha hs₂ h2 h4 h6

local notation "E" => terminalArithmeticNodeEvaluation data m j hj ha hs h2 h3 h4 h6
local notation "δ" => ite (opposite = true) (NodalFiber.p c) (NodalFiber.q c)

local notation "B" => Spec.map (CommRingCat.ofHom (AlgHom.toRingHom (E opposite)))
local notation "L" => Localization.Away δ
local notation "i" => Spec.map (CommRingCat.ofHom (algebraMap (NodalFiber.Coordinate c) L))

/-- Localize the original full boundary evaluation at its actual invertible node coordinate. -/
def terminalArithmeticPunctureEvaluation : L →ₐ[Q] Q[T;T⁻¹] :=
  IsLocalization.Away.liftAlgHom δ (f := E opposite)
    (terminalArithmeticSelected_unit data m j hj ha hs h2 h3 h4 h6 opposite)
local notation "F" => terminalArithmeticPunctureEvaluation data m j hj ha hs h2 h3 h4 h6 opposite

/-- The complete puncture parameter change retains every original node function. -/
theorem terminalArithmeticPunctureEvaluation_base (z : NodalFiber.Coordinate c) :
    F (algebraMap (NodalFiber.Coordinate c) L z) = E opposite z := by
  rw [terminalArithmeticPunctureEvaluation, IsLocalization.Away.liftAlgHom_apply,
    IsLocalization.Away.lift_eq]
  rfl

/-- The localization map is precisely the entire geometric puncture isomorphism. -/
theorem terminalArithmeticPunctureEvaluation_spec :
    Spec.map (CommRingCat.ofHom (F).toRingHom) =
      (terminalArithmeticPunctureIso data m j hj ha hs h2 h3 h4 h6 opposite).hom := by
  let _ : IsOpenImmersion i := IsOpenImmersion.of_isLocalization δ
  apply (cancel_mono i).mp
  rw [terminalArithmeticPunctureIso_boundary, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  exact RingHom.ext (terminalArithmeticPunctureEvaluation_base
    data m j hj ha hs h2 h3 h4 h6 opposite)

/-- The standard p coordinate has the full original corrected first-factor parameter. -/
theorem terminalArithmeticPunctureEvaluation_p :
    F (algebraMap (NodalFiber.Coordinate c) L (NodalFiber.p c)) =
      G (WeierstrassDilatation.baseChangeBackward W s (Data.b3 d) (Data.b4 d) (Data.b6 d) Q
        (WeierstrassDilatation.terminalNodeSmall U (q s) (q (Data.b3 d)) (q (Data.b4 d))
          (q (Data.b6 d)) r J hJ hrI (ha.map q) h4₀ h6₀)) := by
  rw [terminalArithmeticPunctureEvaluation_base,
    terminalArithmeticNodeEvaluation_p data m j hj ha hs h2 h3 h4 h6 opposite]

/-- The standard q coordinate also retains its full original corrected parameter. -/
theorem terminalArithmeticPunctureEvaluation_q :
    F (algebraMap (NodalFiber.Coordinate c) L (NodalFiber.q c)) =
      G (WeierstrassDilatation.baseChangeBackward W s (Data.b3 d) (Data.b4 d) (Data.b6 d) Q
        (WeierstrassDilatation.terminalNodeOpposite U (q s) (q (Data.b3 d)) (q (Data.b4 d))
          (q (Data.b6 d)) r J hJ hrI (ha.map q) h4₀ h6₀)) := by
  rw [terminalArithmeticPunctureEvaluation_base,
    terminalArithmeticNodeEvaluation_q data m j hj ha hs h2 h3 h4 h6 opposite]

end FLT.Mazur.WeierstrassDividedDepth
