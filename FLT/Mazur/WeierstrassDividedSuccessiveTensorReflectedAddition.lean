/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedSuccessiveTensorPairAddition
public import FLT.Mazur.WeierstrassDividedNodalReflectedNegative
public import FLT.Mazur.WeierstrassDividedUnequalDepthCoverage

/-!
# Reflected resolved additions on the full successive tensor pair

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
  (j : ℕ) (hj : j ≤ n) (hstage : depth - k - l ≤ j)
  (hl : 2 * l ≤ depth) (hm : depth ≤ k + 2 * l)
local notation "hπ" => node.uniformizer_ne_zero
local notation "P" => SuccessiveTensorPairRing d' e' S
local notation "f" => successiveTensorPairInput hπ d d' e e' S
local notation "input" => Spec.map (CommRingCat.ofHom (f).toRingHom)
local notation "a" => unequalPairLeft d e
local notation "b" => unequalPairRight d e
local notation "O₊" => nodalReflectedDomain node d e hkl data (hstage.trans hj) hl hm a b
local notation "O₋" => nodalReflectedNegativeDomain node d e hkl data (hstage.trans hj) hl hm a b
local notation "O₀" => unequalDepthDomain hπ d e hkl data (by omega : l - k ≤ n) a b
local notation "base" => finiteGlobalStructure hπ data j hj
local notation "U" => (base).smoothLocus

/-- The positive reflected-depth domain in the entire original tensor pair. -/
def successiveTensorReflectedPositiveOpen : (Spec (.of P)).Opens := input ⁻¹ᵁ O₊

/-- The negative reflected-depth domain in the same entire original tensor pair. -/
def successiveTensorReflectedNegativeOpen : (Spec (.of P)).Opens := input ⁻¹ᵁ O₋

/-- The opposite-branch unequal-depth domain in the same entire tensor pair. -/
def successiveTensorReflectedOppositeOpen : (Spec (.of P)).Opens := input ⁻¹ᵁ O₀

local notation "V₊" => successiveTensorReflectedPositiveOpen node d d' e e' S hkl data
  j hj hstage hl hm
local notation "V₋" => successiveTensorReflectedNegativeOpen node d d' e e' S hkl data
  j hj hstage hl hm
local notation "V₀" =>
  successiveTensorReflectedOppositeOpen node d d' e e' S hkl data j hj hstage hl

/-- The positive domain has an actual smooth resolved output. -/
def successiveTensorReflectedPositiveAddition : (V₊).toScheme ⟶ (U).toScheme :=
  (input ∣_ O₊) ≫ nodalReflectedResolvedAddition node d e hkl data (hstage.trans hj)
    hl hm a b j hj hstage

/-- The negative domain has an actual smooth resolved output. -/
def successiveTensorReflectedNegativeAddition : (V₋).toScheme ⟶ (U).toScheme :=
  (input ∣_ O₋) ≫ nodalReflectedNegativeAddition node d e hkl data (hstage.trans hj)
    hl hm a b j hj hstage

/-- The opposite domain has the actual unequal-depth resolved output. -/
def successiveTensorReflectedOppositeAddition : (V₀).toScheme ⟶ (U).toScheme :=
  (input ∣_ O₀) ≫ unequalDepthResolvedAddition hπ d e hkl data (by omega)
    a b j hj (by omega)

/-- The positive output retains the original tensor coefficient point. -/
@[reassoc] theorem successiveTensorReflectedPositiveAddition_structure :
    successiveTensorReflectedPositiveAddition node d d' e e' S hkl data j hj hstage hl hm ≫
      (U).ι ≫ base = (V₊).ι ≫ Spec.map (CommRingCat.ofHom (algebraMap R P)) := by
  rw [successiveTensorReflectedPositiveAddition, Category.assoc,
    nodalReflectedResolvedAddition_structure, morphismRestrict_ι_assoc,
    successiveTensorPairInput_structure]
  rfl

/-- The negative output retains the same original tensor coefficient point. -/
@[reassoc] theorem successiveTensorReflectedNegativeAddition_structure :
    successiveTensorReflectedNegativeAddition node d d' e e' S hkl data j hj hstage hl hm ≫
      (U).ι ≫ base = (V₋).ι ≫ Spec.map (CommRingCat.ofHom (algebraMap R P)) := by
  rw [successiveTensorReflectedNegativeAddition, Category.assoc,
    nodalReflectedNegativeAddition_structure, morphismRestrict_ι_assoc,
    successiveTensorPairInput_structure]
  rfl

/-- The unequal-depth output retains the same original tensor coefficient point. -/
@[reassoc] theorem successiveTensorReflectedOppositeAddition_structure :
    successiveTensorReflectedOppositeAddition node d d' e e' S hkl data j hj hstage hl ≫
      (U).ι ≫ base = (V₀).ι ≫ Spec.map (CommRingCat.ofHom (algebraMap R P)) := by
  rw [successiveTensorReflectedOppositeAddition, Category.assoc,
    unequalDepthResolvedAddition_structure, morphismRestrict_ι_assoc,
    successiveTensorPairInput_structure]
  rfl

end FLT.Mazur.WeierstrassDividedDepth
