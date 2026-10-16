/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSplitDepthRetainedComparison
public import FLT.Mazur.WeierstrassSplitDepthPrimitiveTerminal
public import FLT.Mazur.WeierstrassDilatationFixedTerminalPolygon

/-!
# A fixed-target terminal comparison from the original odd split depth

All division data, the primitive terminal unit and the complete smoothing
normalization are constructed. The target is the same polygon used by the
retained family. Compatibility at the two terminal edges remains separate.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages WeierstrassDilatation
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (n : ℕ) (D : SplitNodeDepth W π (2 * (1 + n) + 1))
local notation "d" => splitDepthStartOneData D n (by omega)
local notation "H" => splitDepthStartOneAtlasCoefficients D n (by omega)
local notation "e" => d (Fin.mk n (Nat.lt_succ_self n))
local notation "u" => splitDepthPrimitiveTerminalUnit D e
local notation "hu" => splitDepthPrimitiveTerminalUnit_spec D e

/-- The entire actual terminal node maps into label zero of the retained target polygon. -/
def splitDepthFixedTerminalMap (m : ℕ) :
    arithmeticLabeledAtlasObject D.uniformizer_ne_zero d H m n le_rfl .terminal ⟶
      arithmeticFactorRatioPolygon π m W (π ^ 1) (H).a1_unit (H).scale_div n :=
  fixedTerminalPolygonMap π W (π ^ (1 + n))
    (Data.b3 e) (Data.b4 e) (Data.b6 e) (H).a1_unit ((H).scale n) (H).a2_div
    ((H).b3_div _) ((H).b4_div _) ((H).b6_div _) u hu m n ⟨0, by omega⟩

instance splitDepthFixedTerminalMap_isOpenImmersion (m : ℕ) :
    IsOpenImmersion (splitDepthFixedTerminalMap n D m) := by
  unfold splitDepthFixedTerminalMap
  infer_instance

omit [IsBezout R] in
/-- The terminal comparison preserves its original quotient arrow and fixed target. -/
@[reassoc] theorem splitDepthFixedTerminalMap_restriction (m : ℕ) :
    arithmeticLabeledAtlasRestriction D.uniformizer_ne_zero d H m n le_rfl .terminal ≫
      splitDepthFixedTerminalMap n D (m + 1) =
    splitDepthFixedTerminalMap n D m ≫
      arithmeticFactorRatioPolygonRestriction π m W (π ^ 1) (H).a1_unit (H).scale_div n :=
  fixedTerminalPolygonMap_restriction π W (π ^ (1 + n))
    (Data.b3 e) (Data.b4 e) (Data.b6 e) (H).a1_unit ((H).scale n) (H).a2_div
    ((H).b3_div _) ((H).b4_div _) ((H).b6_div _) u hu D.uniformizer_ne_zero m n ⟨0, by omega⟩

end FLT.Mazur.WeierstrassDividedDepth
