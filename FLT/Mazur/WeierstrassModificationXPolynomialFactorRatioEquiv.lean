/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXPolynomialFactorRatioReduction
public import FLT.Mazur.NilpotentAlgebraEquivalence

/-!
# The full corrected factor-ratio equivalence

The factor-ratio map is inverted by finite nilpotent correction of the full
Möbius equivalence. No inverse or injectivity is supplied as a hypothesis.
-/

@[expose] public noncomputable section
open Polynomial
namespace FLT.Mazur.WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (ha : IsUnit W.a₁)
  (s τ : R) (hτ : s = W.a₁ ^ 2 * τ) (b3 b4 b6 : R)
  (r : R[X]) (hr : r ^ 2 + polynomialSlopeLinear W b3 * r =
    polynomialSlopeConstant W b4 b6)
  (I : Ideal R) (hI : IsNilpotent I) (hrI : r ∈ I.map C) (h3 : b3 ∈ I)
local notation "L" => PolynomialNodeOpen W s
local notation "M" => NodalFiber.TangentOpen τ (-1 : R)
local notation "O" => PolynomialInitialOpen W s b3 b4 b6 r
local notation "F" => polynomialFactorRatioMap W ha s τ hτ b3 b4 b6 r hr I hI hrI h3

/-- The corrected map is bijective on every localized node function. -/
theorem polynomialFactorRatioMap_bijective : Function.Bijective F :=
  NilpotentAlgebraEquivalence.bijective I hI
    (NodalFiber.tangentMobiusEquiv s τ (zeroInitialTangentUnit W ha) hτ) F
    (polynomialFactorRatioMap_sub_mem W ha s τ hτ b3 b4 b6 r hr I hI hrI h3)

/-- The full corrected equivalence, including its independently constructed inverse. -/
def polynomialFactorRatioEquiv : M ≃ₐ[R] L :=
  AlgEquiv.ofBijective F
    (polynomialFactorRatioMap_bijective W ha s τ hτ b3 b4 b6 r hr I hI hrI h3)

local notation "E" => polynomialFactorRatioEquiv W ha s τ hτ b3 b4 b6 r hr I hI hrI h3

/-- The constructed equivalence preserves the complete original factor-ratio map. -/
theorem polynomialFactorRatioEquiv_toAlgHom : (E).toAlgHom = F := rfl

/-- The corrected equivalence fixes all original normalized functions after inversion. -/
theorem polynomialFactorRatioEquiv_left_inv (z : M) : (E).symm (F z) = z :=
  (E).symm_apply_apply z

/-- The corrected inverse recovers every original node function. -/
theorem polynomialFactorRatioEquiv_right_inv (z : L) : F ((E).symm z) = z :=
  (E).apply_symm_apply z

/-- The entire original initial neighborhood has the corrected normalized coordinates. -/
def polynomialInitialFactorRatioEquiv : M ≃ₐ[R] O :=
  (E).trans (polynomialNodeEquiv W s b3 b4 b6 r hr I hI hrI h3).symm

/-- The original initial coordinate map is exactly the constructed backward node map. -/
theorem polynomialInitialFactorRatioEquiv_toAlgHom :
    (polynomialInitialFactorRatioEquiv W ha s τ hτ b3 b4 b6 r hr I hI hrI h3).toAlgHom =
      (polynomialNodeBackward W s b3 b4 b6 r hr).comp F := rfl

end FLT.Mazur.WeierstrassModificationX
