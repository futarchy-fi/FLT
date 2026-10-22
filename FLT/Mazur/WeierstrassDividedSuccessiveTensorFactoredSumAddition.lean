/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedSuccessiveTensorPairAddition
public import FLT.Mazur.WeierstrassDividedNodalFactoredSumNegative
public import FLT.Mazur.WeierstrassDividedUnequalDepthCoverage

/-!
# Normalized sum-depth resolved additions on the full successive tensor pair

Pull the three constructed integral output domains back along both exact
own-depth contractions. The coefficient ring may be an arithmetic thickening.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalStructure
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsNoetherianRing R]
  [IsLocalRing R] {W : WeierstrassCurve R} {π : R} {k l n depth : ℕ}
  (node : SplitNodeDepth W π depth)
  (d : Data W π k) (d' : Data W π (k + 1)) (e : Data W π l) (e' : Data W π (l + 1))
  (S : Type u) [CommRing S] [Algebra R S] (hkl : k ≤ l)
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val))
  (j : ℕ) (hj : j ≤ n) (hstage : k + l ≤ j)
  (hl : k + 2 * l ≤ depth)
local notation "hπ" => node.uniformizer_ne_zero
local notation "P" => SuccessiveTensorPairRing d' e' S
local notation "f" => successiveTensorPairInput hπ d d' e e' S
local notation "input" => Spec.map (CommRingCat.ofHom (f).toRingHom)
local notation "a" => unequalPairLeft d e
local notation "b" => unequalPairRight d e
local notation "O₊" => nodalFactoredSumDomain node d e hkl data (hstage.trans hj) hl a b
local notation "O₋" => nodalFactoredSumNegativeDomain node d e hkl data
  (hstage.trans hj) hl a b
local notation "O₀" => unequalDepthDomain hπ d e hkl data (by omega : l - k ≤ n) a b
local notation "base" => finiteGlobalStructure hπ data j hj
local notation "U" => (base).smoothLocus

/-- The positive sum-depth domain in the entire original tensor pair. -/
def successiveTensorFactoredSumPositiveOpen : (Spec (.of P)).Opens := input ⁻¹ᵁ O₊

/-- The negative sum-depth domain in the same entire original tensor pair. -/
def successiveTensorFactoredSumNegativeOpen : (Spec (.of P)).Opens := input ⁻¹ᵁ O₋

/-- The opposite-branch unequal-depth domain in the same entire tensor pair. -/
def successiveTensorFactoredSumOppositeOpen : (Spec (.of P)).Opens := input ⁻¹ᵁ O₀

local notation "V₊" => successiveTensorFactoredSumPositiveOpen node d d' e e' S hkl data
  j hj hstage hl
local notation "V₋" => successiveTensorFactoredSumNegativeOpen node d d' e e' S hkl data
  j hj hstage hl
local notation "V₀" =>
  successiveTensorFactoredSumOppositeOpen node d d' e e' S hkl data j hj hstage

/-- The positive domain has an actual smooth resolved output. -/
def successiveTensorFactoredSumPositiveAddition : (V₊).toScheme ⟶ (U).toScheme :=
  (input ∣_ O₊) ≫ nodalFactoredSumResolvedAddition node d e hkl data (hstage.trans hj)
    hl a b j hj hstage

/-- The negative domain has an actual smooth resolved output. -/
def successiveTensorFactoredSumNegativeAddition : (V₋).toScheme ⟶ (U).toScheme :=
  (input ∣_ O₋) ≫ nodalFactoredSumNegativeAddition node d e hkl data (hstage.trans hj)
    hl a b j hj hstage

/-- The opposite domain has the actual unequal-depth resolved output. -/
def successiveTensorFactoredSumOppositeAddition : (V₀).toScheme ⟶ (U).toScheme :=
  (input ∣_ O₀) ≫ unequalDepthResolvedAddition hπ d e hkl data (by omega)
    a b j hj (by omega)

/-- The positive output retains the original tensor coefficient point. -/
@[reassoc] theorem successiveTensorFactoredSumPositiveAddition_structure :
    successiveTensorFactoredSumPositiveAddition node d d' e e' S hkl data j hj hstage hl ≫
      (U).ι ≫ base = (V₊).ι ≫ Spec.map (CommRingCat.ofHom (algebraMap R P)) := by
  rw [successiveTensorFactoredSumPositiveAddition, Category.assoc,
    nodalFactoredSumResolvedAddition_structure, morphismRestrict_ι_assoc,
    successiveTensorPairInput_structure]
  rfl

/-- The negative output retains the same original tensor coefficient point. -/
@[reassoc] theorem successiveTensorFactoredSumNegativeAddition_structure :
    successiveTensorFactoredSumNegativeAddition node d d' e e' S hkl data j hj hstage hl ≫
      (U).ι ≫ base = (V₋).ι ≫ Spec.map (CommRingCat.ofHom (algebraMap R P)) := by
  rw [successiveTensorFactoredSumNegativeAddition, Category.assoc,
    nodalFactoredSumNegativeAddition_structure, morphismRestrict_ι_assoc,
    successiveTensorPairInput_structure]
  rfl

/-- The unequal-depth output retains the same original tensor coefficient point. -/
@[reassoc] theorem successiveTensorFactoredSumOppositeAddition_structure :
    successiveTensorFactoredSumOppositeAddition node d d' e e' S hkl data j hj hstage ≫
      (U).ι ≫ base = (V₀).ι ≫ Spec.map (CommRingCat.ofHom (algebraMap R P)) := by
  rw [successiveTensorFactoredSumOppositeAddition, Category.assoc,
    unequalDepthResolvedAddition_structure, morphismRestrict_ι_assoc,
    successiveTensorPairInput_structure]
  rfl

end FLT.Mazur.WeierstrassDividedDepth
