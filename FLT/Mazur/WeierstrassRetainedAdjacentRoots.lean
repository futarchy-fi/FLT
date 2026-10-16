/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassRetainedAdjacentEvaluation
public import FLT.Mazur.WeierstrassRetainedNodeFactorRatioMap

/-!
# Independently constructed roots agree on the entire adjacent edge

Both roots are identified by their full equations and nilpotent reductions.
The next smoothing remains πs and all divided coefficients remain present.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassModificationX
open PolygonSmoothing
set_option backward.isDefEq.respectTransparency false
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (π s c3 c4 c6 : R)
  (I : Ideal R) (hI : IsNilpotent I) (ha : IsUnit W.a₁)
  (hs : s ∈ I) (h2 : W.a₂ ∈ I) (h3 : c3 ∈ I) (h4 : c4 ∈ I) (h6 : c6 ∈ I)
local notation "E" => leftLaurentMap π
local notation "N" => retainedPrecedingEvaluation π
local notation "H3" => I.mul_mem_left π h3
local notation "H4" => I.mul_mem_left π h4
local notation "H6" => I.mul_mem_left (π ^ 2) h6
local notation "HS" => I.mul_mem_left π hs
local notation "L" => laurentArithmeticIdeal I
local notation "r" => retainedConicRoot W π (π * c3) (π * c4) (π ^ 2 * c6)
  I hI ha h2 H3 H4 H6
local notation "r'" => retainedConicRoot W π c3 c4 c6 I hI ha h2 h3 h4 h6
local notation "v" => retainedSlopeRoot W π s (π * c3) (π * c4) (π ^ 2 * c6)
  I hI ha hs h2 H3 H4 H6
local notation "v'" => retainedSlopeRoot W π (π * s) c3 c4 c6 I hI ha HS h2 h3 h4 h6
attribute [local irreducible] retainedConicRoot retainedSlopeRoot

/-- The two independently chosen conic roots agree on the entire original adjacent edge. -/
theorem retainedConicRoot_adjacent : E r = N r' := by
  apply NilpotentQuadraticRoot.root_unique L (laurentArithmeticIdeal_nilpotent I hI)
    (N (retainedSlopeLinear W π c3)) (N (retainedConicConstant W π c4 c6))
    ((retainedSlopeLinear_unit W π c3 I hI ha h3).map N)
  · exact retainedLaurentEvaluation_ideal π I E
      (retainedConicRoot_mem W π (π * c3) (π * c4) (π ^ 2 * c6) I hI ha h2 H3 H4 H6)
  · exact retainedLaurentEvaluation_ideal π I N
      (retainedConicRoot_mem W π c3 c4 c6 I hI ha h2 h3 h4 h6)
  · have he := congrArg E (retainedConicRoot_equation W π (π * c3) (π * c4)
      (π ^ 2 * c6) I hI ha h2 H3 H4 H6)
    simpa only [map_add, map_mul, map_pow, retainedSlopeLinear_adjacent,
      retainedConicConstant_adjacent] using he
  · have he := congrArg N (retainedConicRoot_equation W π c3 c4 c6 I hI ha h2 h3 h4 h6)
    simpa only [map_add, map_mul, map_pow] using he

/-- The full slope roots agree with the next smoothing multiplied by the actual parameter. -/
theorem retainedSlopeRoot_adjacent : E v = N v' := by
  apply NilpotentQuadraticRoot.root_unique L (laurentArithmeticIdeal_nilpotent I hI)
    (N (retainedSlopeLinear W π c3)) (N (retainedSlopeConstant W π (π * s) c4 c6))
    ((retainedSlopeLinear_unit W π c3 I hI ha h3).map N)
  · exact retainedLaurentEvaluation_ideal π I E
      (retainedSlopeRoot_mem W π s (π * c3) (π * c4) (π ^ 2 * c6) I hI ha hs h2 H3 H4 H6)
  · exact retainedLaurentEvaluation_ideal π I N
      (retainedSlopeRoot_mem W π (π * s) c3 c4 c6 I hI ha HS h2 h3 h4 h6)
  · have he := congrArg E (retainedSlopeRoot_equation W π s (π * c3) (π * c4)
      (π ^ 2 * c6) I hI ha hs h2 H3 H4 H6)
    simpa only [map_add, map_mul, map_pow, retainedSlopeLinear_adjacent,
      retainedSlopeConstant_adjacent] using he
  · have he := congrArg N
      (retainedSlopeRoot_equation W π (π * s) c3 c4 c6 I hI ha HS h2 h3 h4 h6)
    simpa only [map_add, map_mul, map_pow] using he

end FLT.Mazur.WeierstrassModificationX
