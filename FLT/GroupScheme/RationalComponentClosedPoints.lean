/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.ModelAugmentationPoints
public import FLT.GroupScheme.RationalComponentMaps

/-! # Closed immersions induce injections on the actual component quotients -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance 2000] IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
  IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion
namespace ThreeAdicPlan.ModelHom
variable {p : ℕ} [Fact p.Prime]
variable {X Y : FF ((LocalCyclotomic.rationalPlace p).adicCompletionIntegers ℚ)
  ((LocalCyclotomic.rationalPlace p).adicCompletion ℚ)}

/-- A closed immersion reflects membership in the connected kernel. -/
theorem rationalComponentProjection_reflect_zero (f : ModelHom X Y)
    (hf : Function.Surjective f) (x : X.Points) :
    Y.rationalComponentGenericProjection (genericHom f x) = 0 ↔
      X.rationalComponentGenericProjection x = 0 := by
  have h : HopfAlgebra.augmentationIdeal (f.comp Y.rationalComponentProjection) =
      HopfAlgebra.augmentationIdeal X.rationalComponentProjection := by
    rw [ModelHom.augmentationIdeal_comp, Y.rationalComponentProjection_kernel,
      X.rationalComponentProjection_kernel]
    exact f.rationalIdentityIdeal_map_of_surjective hf
  have he := ModelHom.genericHom_eq_zero_iff_of_augmentation_eq
    (X := X) (Y := Y.rationalComponentQuotient) (Z := X.rationalComponentQuotient)
    (f.comp Y.rationalComponentProjection) X.rationalComponentProjection h x
  simp only [genericHom_comp, FF.rationalComponentProjection_genericHom] at he
  convert he using 1

/-- The generic quotient of a closed immersion is injective. -/
theorem rationalComponentGenericMap_injective (f : ModelHom X Y)
    (hf : Function.Surjective f) : Function.Injective f.rationalComponentGenericMap := by
  apply (injective_iff_map_eq_zero _).mpr
  intro x hx
  obtain ⟨a, rfl⟩ := X.rationalComponentGenericProjection_surjective x
  apply (f.rationalComponentProjection_reflect_zero hf a).mp
  have hn := DFunLike.congr_fun f.rationalComponentGenericMap_naturality a
  exact hn.trans hx

/-- The integral quotient map of a closed immersion has injective original generic points. -/
theorem rationalComponentMap_generic_injective (f : ModelHom X Y)
    (hf : Function.Surjective f) : Function.Injective (genericHom f.rationalComponentMap) := by
  rw [f.rationalComponentMap_genericHom]
  exact f.rationalComponentGenericMap_injective hf
end ThreeAdicPlan.ModelHom
