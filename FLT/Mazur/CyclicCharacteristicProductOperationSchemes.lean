/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicProductParameterGroupoid

/-!
# Scheme maps for ordered-pair identities and inverses

Classify the universal compatible comparisons to obtain actual scheme maps.
Their source and target equations follow from the classifier's base equation.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.CyclicCharacteristicAtlas
open GeneralizedEllipticCurve GeneralizedEllipticCurve.FiniteSubgroup
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] (b c : Bool)

/-- Source endpoint of an ordered-pair comparison. -/
def productArrowSource : productSubgroupScheme n b c ⟶ normalizedLocus n b :=
  productSubgroupStructure n b c ≫ prod.fst

/-- Target endpoint of an ordered-pair comparison. -/
def productArrowTarget : productSubgroupScheme n b c ⟶ normalizedLocus n c :=
  productSubgroupStructure n b c ≫ prod.snd

/-- An actual parameter retains its specified source. -/
theorem productArrow_source {T : Scheme} {q : T ⟶ normalizedLocus n b}
    {r : T ⟶ normalizedLocus n c} (a : ProductArrow n q r) :
    a.val ≫ productArrowSource n b c = q := by
  rw [productArrowSource, ← Category.assoc, a.property, prod.lift_fst]

/-- An actual parameter retains its specified target. -/
theorem productArrow_target {T : Scheme} {q : T ⟶ normalizedLocus n b}
    {r : T ⟶ normalizedLocus n c} (a : ProductArrow n q r) :
    a.val ≫ productArrowTarget n b c = r := by
  rw [productArrowTarget, ← Category.assoc, a.property, prod.lift_snd]

/-- The tautological arrow on the entire ordered-pair parameter scheme. -/
def productUniversalArrow :
    ProductArrow n (productArrowSource n b c) (productArrowTarget n b c) :=
  ⟨𝟙 _, by
    apply prod.hom_ext <;>
      simp only [Category.id_comp, prod.lift_fst, prod.lift_snd,
        productArrowSource, productArrowTarget]⟩

/-- The identity section is an actual map from the normalized family base. -/
def productIdentityMap : normalizedLocus n b ⟶ productSubgroupScheme n b b :=
  (productArrowId n (𝟙 (normalizedLocus n b))).val

/-- The inversion morphism is classified by the inverse universal comparison. -/
def productInverseMap : productSubgroupScheme n b c ⟶ productSubgroupScheme n c b :=
  (productArrowInv n (productUniversalArrow n b c)).val

/-- The identity section has the required source. -/
@[reassoc] theorem productIdentityMap_source :
    productIdentityMap n b ≫ productArrowSource n b b = 𝟙 _ :=
  productArrow_source n b b (productArrowId n (𝟙 _))

/-- The identity section has the required target. -/
@[reassoc] theorem productIdentityMap_target :
    productIdentityMap n b ≫ productArrowTarget n b b = 𝟙 _ :=
  productArrow_target n b b (productArrowId n (𝟙 _))

/-- Inversion exchanges the source and target maps. -/
@[reassoc] theorem productInverseMap_source :
    productInverseMap n b c ≫ productArrowSource n c b = productArrowTarget n b c :=
  productArrow_source n c b (productArrowInv n (productUniversalArrow n b c))

/-- Inversion exchanges the target and source maps. -/
@[reassoc] theorem productInverseMap_target :
    productInverseMap n b c ≫ productArrowTarget n c b = productArrowSource n b c :=
  productArrow_target n c b (productArrowInv n (productUniversalArrow n b c))

end FLT.Mazur.CyclicCharacteristicAtlas
