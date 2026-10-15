/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveNilpotentBranch
public import FLT.Mazur.NilpotentQuadraticRootNaturality
public import FLT.Mazur.SuccessiveIncidenceCoefficientMap

/-!
# The original small slope commutes with coefficient restriction

The actual incidence map preserves the constructed branch by uniqueness in
the extended nilpotent ideal. No compatibility of chosen slopes is assumed.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassSuccessiveX
variable {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
  (W : WeierstrassCurve R) (s π b3 b4 b6 : R)
local notation "F" => SuccessiveIncidence.coefficientRingMap f π

/-- The linear slope coefficient retains the original Weierstrass coefficients. -/
@[simp] theorem nodeSlopeLinear_map :
    F (nodeSlopeLinear W π b3) = nodeSlopeLinear (W.map f) (f π) (f b3) := by
  simp only [nodeSlopeLinear, map_add, map_mul,
    SuccessiveIncidence.coefficientRingMap_algebraMap,
    SuccessiveIncidence.coefficientRingMap_t, WeierstrassCurve.map_a₁]

/-- The constant slope coefficient retains the original divided equation. -/
@[simp] theorem nodeSlopeConstant_map :
    F (nodeSlopeConstant W s π b4 b6) =
      nodeSlopeConstant (W.map f) (f s) (f π) (f b4) (f b6) := by
  simp only [nodeSlopeConstant, map_add, map_mul, map_pow,
    SuccessiveIncidence.coefficientRingMap_algebraMap,
    SuccessiveIncidence.coefficientRingMap_t, SuccessiveIncidence.coefficientRingMap_u,
    WeierstrassCurve.map_a₂]

variable (I : Ideal R) (hI : IsNilpotent I) (J : Ideal S) (hJ : IsNilpotent J)
  (hf : I ≤ J.comap f) (ha : IsUnit W.a₁) (hs : s ∈ I) (h2 : W.a₂ ∈ I)
  (h3 : b3 ∈ I) (h4 : b4 ∈ I) (h6 : b6 ∈ I)

/-- The small root supplied by the original coefficients commutes with restriction. -/
theorem nilpotentNodeSlope_map :
    F (nilpotentNodeSlope W s π b3 b4 b6 I hI ha hs h2 h3 h4 h6) =
      nilpotentNodeSlope (W.map f) (f s) (f π) (f b3) (f b4) (f b6)
        J hJ (ha.map f) (hf hs) (hf h2) (hf h3) (hf h4) (hf h6) := by
  have hm := SuccessiveIncidence.coefficientRingMap_ideal f π I J hf
  have h := NilpotentQuadraticRoot.root_map (nodeArithmeticIdeal π I)
    (nodeArithmeticIdeal_nilpotent π I hI) (nodeArithmeticIdeal (f π) J)
    (nodeArithmeticIdeal_nilpotent (f π) J hJ) (nodeSlopeLinear W π b3)
    (nodeSlopeConstant W s π b4 b6) (nodeSlopeLinear_unit W π b3 I hI ha h3)
    (nodeSlopeConstant_mem W s π b4 b6 I hs h2 h4 h6) F hm
  simpa only [nodeSlopeLinear_map, nodeSlopeConstant_map, nilpotentNodeSlope] using h

end FLT.Mazur.WeierstrassSuccessiveX
