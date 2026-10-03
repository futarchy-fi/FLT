/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.UnramifiedOrderSection
public import FLT.LocalClassFieldTheory.UnramifiedCarryNormalization

/-!
# The multiplicative unramified invariant and positive carry

Normalized order followed by Frobenius coordinates identifies multiplicative
continuous H2 with Q/Z. The actual uniformizer-power image of the positive
integral carry has coordinate +1/n.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

open IsLocalRing CategoryTheory HomologicalComplex

variable (R K C : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [Field C] [Algebra K C] [Algebra R C] [IsScalarTower R K C]
  [Algebra.IsSeparable K C] [Finite (ResidueField R)] [IsSepClosed C]
  [IsAdicComplete (maximalIdeal R) R]

local notation "U" => maximalUnramified R K C
local notation "G" => Gal(U/K)
local notation "ord" => unramifiedUnionOrderMap R K C

attribute [local instance] unramifiedUnionGalois fieldUnitAction
  trivialCoefficientAction trivialCoefficientIntComm trivialCoefficientContinuous
  unramifiedFieldUnitTopology unramifiedFieldUnitDiscrete

/-- The actual multiplicative H2 invariant of the constructed unramified extension. -/
def unramifiedMultiplicativeInvariant :
    continuousCohomology ℤ G (Additive Uˣ) 2 ≃+ AddCircle (1 : ℚ) :=
  (unramifiedContinuousOrderH2Iso R K C).toLinearEquiv.toAddEquiv.trans
    (unramifiedIntegralH2AddEquiv R K C)

variable {π : R} (hπ : Irreducible π)

/-- The coefficient map sends an integer cochain to the corresponding uniformizer powers. -/
theorem unramifiedOrderSection_cochain_apply (i : ℕ)
    (c : (continuousCochains ℤ G ℤ).X i) (g : Fin i → G) :
    (((continuousCoefficientMap (unramifiedOrderSection R K C hπ)).f i).hom c).val g =
      Additive.ofMul (unramifiedUniformizerUnit R K C hπ ^ c.val g) := rfl

/-- Uniformizer powers split order on actual continuous cohomology. -/
theorem unramifiedOrderSection_cohomology (i : ℕ) :
    continuousCoefficientCohomologyMap (unramifiedOrderSection R K C hπ) i ≫
      continuousCoefficientCohomologyMap ord i = 𝟙 _ := by
  unfold continuousCoefficientCohomologyMap
  rw [← homologyMap_comp, ← continuousCoefficientMap_comp,
    unramifiedOrderSection_comp, continuousCoefficientMap_id, homologyMap_id]
  rfl

/-- The multiplicative carry is the coefficient image under actual uniformizer powers. -/
def unramifiedMultiplicativeCarryClass (n : UnramifiedIndex) :
    continuousCohomology ℤ G (Additive Uˣ) 2 :=
  (continuousCoefficientCohomologyMap (unramifiedOrderSection R K C hπ) 2).hom
    (unramifiedCarryClass R K C n)

/-- Applying order recovers the positive integral carry. -/
theorem unramifiedMultiplicativeCarryClass_order (n : UnramifiedIndex) :
    (continuousCoefficientCohomologyMap ord 2).hom
        (unramifiedMultiplicativeCarryClass R K C hπ n) = unramifiedCarryClass R K C n :=
  congrArg (fun f => f.hom (unramifiedCarryClass R K C n))
    (unramifiedOrderSection_cohomology R K C hπ 2)

/-- The normalization is positive: the uniformizer carry has invariant +1/n. -/
theorem unramifiedMultiplicativeCarryClass_coordinate (n : UnramifiedIndex) :
    unramifiedMultiplicativeInvariant R K C (unramifiedMultiplicativeCarryClass R K C hπ n) =
      (↑((1 : ℚ) / n.degree) : AddCircle (1 : ℚ)) := by
  change unramifiedIntegralH2AddEquiv R K C
    ((continuousCoefficientCohomologyMap ord 2).hom _) = _
  rw [unramifiedMultiplicativeCarryClass_order, unramifiedCarryClass_coordinate]

/-- Vanishing of multiplicative H2 is detected by its Q/Z coordinate. -/
theorem unramifiedMultiplicativeInvariant_eq_zero
    (x : continuousCohomology ℤ G (Additive Uˣ) 2) :
    unramifiedMultiplicativeInvariant R K C x = 0 ↔ x = 0 :=
  map_eq_zero_iff _ (unramifiedMultiplicativeInvariant R K C).injective

end LocalClassFieldTheory
