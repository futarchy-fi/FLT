/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXLaurentBranches
public import FLT.Mazur.PolygonScalingNaturality

/-!
# Original initial Laurent branches commute with coefficient change

Uniqueness of the small nilpotent root preserves both full labeled initial
slopes under every coefficient map preserving the arithmetic ideals.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassModificationX
variable {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
  (W : WeierstrassCurve R) (s b3 b4 b6 : R)
local notation "F" => PolygonScalingNaturality.coeffMap f
local notation "U" => W.map f

/-- The initial Laurent linear coefficient retains all original coefficients. -/
theorem laurentSlopeLinear_coefficient :
    F (laurentSlopeLinear W b3) = laurentSlopeLinear U (f b3) := by
  simp only [laurentSlopeLinear, map_add, map_mul, PolygonScalingNaturality.coeffMap_C,
    PolygonScalingNaturality.coeffMap_T_neg_one, WeierstrassCurve.map_a₁]

/-- The initial Laurent constant retains its scale and all divided cubic terms. -/
theorem laurentSlopeConstant_coefficient :
    F (laurentSlopeConstant W s b4 b6) =
      laurentSlopeConstant U (f s) (f b4) (f b6) := by
  simp only [laurentSlopeConstant, map_add, map_mul, map_pow,
    PolygonScalingNaturality.coeffMap_C, PolygonScalingNaturality.coeffMap_T_one,
    PolygonScalingNaturality.coeffMap_T_neg_one, WeierstrassCurve.map_a₂]

variable (I : Ideal R) (J : Ideal S) (hf : I ≤ J.comap f)

include hf in
/-- Arithmetic ideal preservation extends to the complete original Laurent algebra. -/
theorem laurentArithmeticIdeal_coefficient :
    laurentArithmeticIdeal I ≤ (laurentArithmeticIdeal J).comap F := by
  rw [laurentArithmeticIdeal, Ideal.map_le_iff_le_comap]
  intro x hx
  change F (LaurentPolynomial.C x) ∈ laurentArithmeticIdeal J
  rw [PolygonScalingNaturality.coeffMap_C]
  exact Ideal.mem_map_of_mem (algebraMap S S[T;T⁻¹]) (hf hx)

variable (hI : IsNilpotent I) (hJ : IsNilpotent J)
  (ha : IsUnit W.a₁) (hs : s ∈ I) (h2 : W.a₂ ∈ I)
  (h3 : b3 ∈ I) (h4 : b4 ∈ I) (h6 : b6 ∈ I)

/-- The constructed small initial slope, including every correction, is natural in coefficients. -/
theorem nilpotentLaurentSlope_coefficient :
    F (nilpotentLaurentSlope W s b3 b4 b6 I hI ha hs h2 h3 h4 h6) =
      nilpotentLaurentSlope U (f s) (f b3) (f b4) (f b6) J hJ
        (ha.map f) (hf hs) (hf h2) (hf h3) (hf h4) (hf h6) := by
  apply NilpotentQuadraticRoot.root_unique (laurentArithmeticIdeal J)
    (laurentArithmeticIdeal_nilpotent J hJ) (laurentSlopeLinear U (f b3))
    (laurentSlopeConstant U (f s) (f b4) (f b6))
    (laurentSlopeLinear_unit U (f b3) J hJ (ha.map f) (hf h3))
  · exact laurentArithmeticIdeal_coefficient f I J hf
      (nilpotentLaurentSlope_mem W s b3 b4 b6 I hI ha hs h2 h3 h4 h6)
  · exact nilpotentLaurentSlope_mem U (f s) (f b3) (f b4) (f b6) J hJ
      (ha.map f) (hf hs) (hf h2) (hf h3) (hf h4) (hf h6)
  · have he := congrArg F
      (nilpotentLaurentSlope_equation W s b3 b4 b6 I hI ha hs h2 h3 h4 h6)
    simpa only [map_add, map_mul, map_pow, laurentSlopeLinear_coefficient,
      laurentSlopeConstant_coefficient] using he
  · exact nilpotentLaurentSlope_equation U (f s) (f b3) (f b4) (f b6) J hJ
      (ha.map f) (hf hs) (hf h2) (hf h3) (hf h4) (hf h6)

/-- Both original initial labels are preserved by every compatible coefficient map. -/
theorem laurentBranchSlope_coefficient (opposite : Bool) :
    F (laurentBranchSlope W s b3 b4 b6 I hI ha hs h2 h3 h4 h6 opposite) =
      laurentBranchSlope U (f s) (f b3) (f b4) (f b6) J hJ
        (ha.map f) (hf hs) (hf h2) (hf h3) (hf h4) (hf h6) opposite := by
  cases opposite
  · exact nilpotentLaurentSlope_coefficient f W s b3 b4 b6 I J hf hI hJ ha hs h2 h3 h4 h6
  · simp only [laurentBranchSlope, ↓reduceIte,
      QuadraticRootBranchLocalization.oppositeRoot, map_sub, map_neg,
      laurentSlopeLinear_coefficient]
    rw [nilpotentLaurentSlope_coefficient f W s b3 b4 b6 I J hf hI hJ ha hs h2 h3 h4 h6]

end FLT.Mazur.WeierstrassModificationX
