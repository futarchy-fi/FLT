/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RationalEtaleSystem
public import FLT.GroupScheme.RationalEtaleTateGalois

/-! # The actual quotient system morphism and its original Tate module -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance 2000] IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
  IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion
namespace ThreeAdicPlan.PDivisibleSystem
variable {p height : ℕ} [Fact p.Prime]
variable (X : PDivisibleSystem ((LocalCyclotomic.rationalPlace p).adicCompletionIntegers ℚ)
  ((LocalCyclotomic.rationalPlace p).adicCompletion ℚ) p height)

/-- The quotient projection is a morphism of systems of the proved complementary height. -/
def rationalEtaleSystemProjection : VariableHeightHom X X.rationalEtaleSystem where
  app := X.rationalEtaleProjection
  inclusion_naturality h := (X.rationalEtaleInclusion_naturality h).symm
  reduction_naturality h := (X.rationalEtaleReduction_naturality h).symm

/-- The quotient system's Tate module is the previously constructed original inverse limit. -/
def rationalEtaleTateEquiv :
    X.rationalEtaleSystem.tateSequences ≃ₗ[ℤ_[p]] X.rationalEtaleTateSequences where
  toFun x := ⟨x.val, x.property⟩
  invFun x := ⟨x.val, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' a x := by
    apply Subtype.ext
    funext n
    rfl

/-- The identified Tate projection is exactly the original levelwise projection. -/
theorem rationalEtaleTateEquiv_projection :
    X.rationalEtaleTateEquiv.toLinearMap.comp X.rationalEtaleSystemProjection.tateMap =
      X.rationalEtaleTateProjectionLinear := by
  ext x
  rfl

/-- The quotient system projection is surjective on its actual Tate module. -/
theorem rationalEtaleSystemProjection_tateMap_surjective :
    Function.Surjective X.rationalEtaleSystemProjection.tateMap := by
  intro y
  obtain ⟨x, hx⟩ := X.rationalEtaleTateProjectionLinear_surjective (X.rationalEtaleTateEquiv y)
  refine ⟨x, X.rationalEtaleTateEquiv.injective ?_⟩
  exact hx

/-- The system-level Tate kernel is precisely the original connected inclusion image. -/
theorem rationalEtaleSystemProjection_tateMap_exact :
    X.rationalEtaleSystemProjection.tateMap.ker = X.rationalConnectedTateInclusion.range := by
  ext x
  change X.rationalEtaleSystemProjection.tateMap x = 0 ↔ _
  rw [← X.rationalEtaleTateEquiv.map_eq_zero_iff]
  exact X.rationalEtaleTateProjection_exact x
end ThreeAdicPlan.PDivisibleSystem
