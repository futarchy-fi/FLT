/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RationalComponentGenericMaps
public import FLT.GroupScheme.RaynaudQuotientFunctoriality

/-! # Functorial integral morphisms of the original component quotients -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance 2000] IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
  IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion
namespace ThreeAdicPlan.ModelHom
variable {p : ℕ} [Fact p.Prime]
local notation "O" =>
  IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ (LocalCyclotomic.rationalPlace p)
variable {X Y Z : FF ((LocalCyclotomic.rationalPlace p).adicCompletionIntegers ℚ)
  ((LocalCyclotomic.rationalPlace p).adicCompletion ℚ)}

/-- The original map descends to the actual contracted quotient coordinate algebras. -/
def rationalComponentMap (f : ModelHom X Y) :
    ModelHom X.rationalComponentQuotient Y.rationalComponentQuotient :=
  X.rationalComponentGenericProjection.flatQuotientMap Y.rationalComponentGenericProjection
    X.rationalComponentGenericProjection_surjective Y.rationalComponentGenericProjection_surjective
    f f.rationalComponentGenericMap f.rationalComponentGenericMap_naturality

/-- The quotient projections commute with the original morphism. -/
theorem rationalComponentMap_naturality (f : ModelHom X Y) :
    X.rationalComponentProjection.comp f.rationalComponentMap =
      f.comp Y.rationalComponentProjection := by
  ext a
  rfl

/-- The quotient morphism is determined uniquely by its original integral projection square. -/
theorem rationalComponentMap_unique (f : ModelHom X Y)
    (g : ModelHom X.rationalComponentQuotient Y.rationalComponentQuotient)
    (hg : X.rationalComponentProjection.comp g = f.comp Y.rationalComponentProjection) :
    g = f.rationalComponentMap := by
  ext a
  apply Subtype.ext
  exact DFunLike.congr_fun hg a

/-- The induced quotient map retains the specified generic quotient map. -/
theorem rationalComponentMap_genericHom (f : ModelHom X Y) :
    genericHom f.rationalComponentMap = f.rationalComponentGenericMap := by
  ext a
  exact X.rationalComponentGenericProjection.genericHom_flatQuotientMap
    Y.rationalComponentGenericProjection _ _ f f.rationalComponentGenericMap
    f.rationalComponentGenericMap_naturality a

/-- Quotient descent preserves identity maps. -/
theorem rationalComponentMap_id :
    rationalComponentMap (X := X) (Y := X) (BialgHom.id O X.CoordinateRing) =
      BialgHom.id O X.rationalComponentQuotient.CoordinateRing := by
  symm
  apply rationalComponentMap_unique
  ext a
  rfl

/-- Quotient descent preserves composition of the original integral maps. -/
theorem rationalComponentMap_comp (f : ModelHom X Y) (g : ModelHom Y Z) :
    rationalComponentMap (X := X) (Y := Z) (f.comp g) =
      f.rationalComponentMap.comp g.rationalComponentMap := by
  symm
  apply rationalComponentMap_unique
  rw [← BialgHom.comp_assoc, rationalComponentMap_naturality, BialgHom.comp_assoc,
    rationalComponentMap_naturality, ← BialgHom.comp_assoc]

/-- Multiplication on the actual quotient is induced by original multiplication. -/
theorem rationalComponentMap_multiply (X : FF
    ((LocalCyclotomic.rationalPlace p).adicCompletionIntegers ℚ)
    ((LocalCyclotomic.rationalPlace p).adicCompletion ℚ)) (n : ℕ) :
    (X.multiply n).rationalComponentMap = X.rationalComponentQuotient.multiply n := by
  symm
  apply rationalComponentMap_unique
  apply genericHom_injective
  ext x
  simp only [genericHom_comp, FF.genericHom_multiply, map_nsmul]
end ThreeAdicPlan.ModelHom
