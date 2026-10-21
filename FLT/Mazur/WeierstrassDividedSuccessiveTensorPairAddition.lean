/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedSuccessiveTensorPair
public import FLT.Mazur.WeierstrassDividedNegativeSumDepthContraction
public import FLT.Mazur.WeierstrassDividedUnequalDepthCoverage

/-!
# Actual resolved additions on the full successive tensor pair

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
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {k l n : ℕ}
  (d : Data W π k) (d' : Data W π (k + 1)) (e : Data W π l) (e' : Data W π (l + 1))
  (S : Type u) [CommRing S] [Algebra R S] (hkl : k ≤ l)
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val))
  (j : ℕ) (hj : j ≤ n) (hsum : k + l ≤ j)
  (dd : Data W π (k + k)) (ee : Data W π (l + l)) (h2 : W.a₂ = 0)
local notation "P" => SuccessiveTensorPairRing d' e' S
local notation "f" => successiveTensorPairInput hπ d d' e e' S
local notation "input" => Spec.map (CommRingCat.ofHom (f).toRingHom)
local notation "a" => unequalPairLeft d e
local notation "b" => unequalPairRight d e
local notation "O₊" => sumDepthDomain hπ d e hkl data (hsum.trans hj) dd ee h2 a b
local notation "O₋" => negativeSumDepthDomain hπ d e hkl data (hsum.trans hj) dd ee h2 a b
local notation "O₀" => unequalDepthDomain hπ d e hkl data (by omega : l - k ≤ n) a b
local notation "base" => finiteGlobalStructure hπ data j hj
local notation "U" => (base).smoothLocus

omit [IsBezout R] [IsNoetherianRing R] in
/-- Both exact tensor contractions retain the original coefficient morphism. -/
@[reassoc] theorem successiveTensorPairInput_structure :
    input ≫ Spec.map (CommRingCat.ofHom (algebraMap R (UnequalPairRing d e))) =
      Spec.map (CommRingCat.ofHom (algebraMap R P)) := by
  rw [← Spec.map_comp]
  congr 1
  ext r
  exact (f).commutes r

/-- The positive sum-depth domain in the entire original tensor pair. -/
def successiveTensorPairPositiveOpen : (Spec (.of P)).Opens := input ⁻¹ᵁ O₊

/-- The negative sum-depth domain in the same entire original tensor pair. -/
def successiveTensorPairNegativeOpen : (Spec (.of P)).Opens := input ⁻¹ᵁ O₋

/-- The opposite-branch unequal-depth domain in the same entire tensor pair. -/
def successiveTensorPairOppositeOpen : (Spec (.of P)).Opens := input ⁻¹ᵁ O₀

local notation "V₊" => successiveTensorPairPositiveOpen hπ d d' e e' S hkl data
  j hj hsum dd ee h2
local notation "V₋" => successiveTensorPairNegativeOpen hπ d d' e e' S hkl data
  j hj hsum dd ee h2
local notation "V₀" => successiveTensorPairOppositeOpen hπ d d' e e' S hkl data j hj hsum

/-- The positive domain has an actual smooth resolved output. -/
def successiveTensorPairPositiveAddition : (V₊).toScheme ⟶ (U).toScheme :=
  (input ∣_ O₊) ≫ sumDepthResolvedAddition hπ d e hkl data (hsum.trans hj)
    dd ee h2 a b j hj hsum

/-- The negative domain has an actual smooth resolved output. -/
def successiveTensorPairNegativeAddition : (V₋).toScheme ⟶ (U).toScheme :=
  (input ∣_ O₋) ≫ negativeSumDepthAddition hπ d e hkl data (hsum.trans hj)
    dd ee h2 a b j hj hsum

/-- The opposite domain has the actual unequal-depth resolved output. -/
def successiveTensorPairOppositeAddition : (V₀).toScheme ⟶ (U).toScheme :=
  (input ∣_ O₀) ≫ unequalDepthResolvedAddition hπ d e hkl data (by omega)
    a b j hj (by omega)

/-- The positive output retains the original tensor coefficient point. -/
@[reassoc] theorem successiveTensorPairPositiveAddition_structure :
    successiveTensorPairPositiveAddition hπ d d' e e' S hkl data j hj hsum dd ee h2 ≫
      (U).ι ≫ base = (V₊).ι ≫ Spec.map (CommRingCat.ofHom (algebraMap R P)) := by
  rw [successiveTensorPairPositiveAddition, Category.assoc,
    sumDepthResolvedAddition_structure, morphismRestrict_ι_assoc,
    successiveTensorPairInput_structure]
  rfl

/-- The negative output retains the same original tensor coefficient point. -/
@[reassoc] theorem successiveTensorPairNegativeAddition_structure :
    successiveTensorPairNegativeAddition hπ d d' e e' S hkl data j hj hsum dd ee h2 ≫
      (U).ι ≫ base = (V₋).ι ≫ Spec.map (CommRingCat.ofHom (algebraMap R P)) := by
  rw [successiveTensorPairNegativeAddition, Category.assoc,
    negativeSumDepthAddition_structure, morphismRestrict_ι_assoc,
    successiveTensorPairInput_structure]
  rfl

/-- The unequal-depth output retains the same original tensor coefficient point. -/
@[reassoc] theorem successiveTensorPairOppositeAddition_structure :
    successiveTensorPairOppositeAddition hπ d d' e e' S hkl data j hj hsum ≫
      (U).ι ≫ base = (V₀).ι ≫ Spec.map (CommRingCat.ofHom (algebraMap R P)) := by
  rw [successiveTensorPairOppositeAddition, Category.assoc,
    unequalDepthResolvedAddition_structure, morphismRestrict_ι_assoc,
    successiveTensorPairInput_structure]
  rfl

end FLT.Mazur.WeierstrassDividedDepth
