/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EtaleAlgebraFiniteBranch
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Actual schemes and maps for finite etale coordinate branches

The branch is an open subscheme of the actual coefficient fiber product.
Its map to the original affine scheme is etale, and its map to the changed
coefficient scheme is finite etale whenever the isolated branch is finite.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct
universe u
namespace FLT.Mazur.EtaleFiniteBranchScheme
set_option backward.isDefEq.respectTransparency false
variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
  [Algebra A B] [Algebra A C] (e : C ⊗[A] B)

/-- The actual affine idempotent branch. -/
def branch : Scheme := Spec (.of (Localization.Away e))

/-- Inclusion in the full coefficient fiber product. -/
def inclusion : branch e ⟶ Spec (.of (C ⊗[A] B)) :=
  Spec.map (CommRingCat.ofHom (algebraMap _ (Localization.Away e)))

/-- The original affine endpoint of the branch. -/
def original : branch e ⟶ Spec (.of B) :=
  inclusion e ≫ Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom)

/-- Projection to the new coefficient scheme. -/
def coefficient : branch e ⟶ Spec (.of C) :=
  Spec.map (CommRingCat.ofHom (algebraMap C (Localization.Away e)))

instance inclusion_isOpenImmersion : IsOpenImmersion (inclusion e) := by
  dsimp only [inclusion]
  infer_instance

/-- The ambient tensor scheme is the full coefficient fiber product. -/
theorem tensor_isPullback :
    IsPullback
      (Spec.map (CommRingCat.ofHom (algebraMap C (C ⊗[A] B))))
      (Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom))
      (Spec.map (CommRingCat.ofHom (algebraMap A C)))
      (Spec.map (CommRingCat.ofHom (algebraMap A B))) :=
  isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct A C B)

/-- The branch's coefficient morphism is induced by the actual tensor projection. -/
@[reassoc]
theorem inclusion_coefficient :
    inclusion e ≫ Spec.map (CommRingCat.ofHom (algebraMap C (C ⊗[A] B))) =
      coefficient e := by
  rw [inclusion, coefficient, ← Spec.map_comp]
  congr 1

/-- The two original base maps agree as scheme morphisms, including their sheaf maps. -/
@[reassoc]
theorem condition :
    original e ≫ Spec.map (CommRingCat.ofHom (algebraMap A B)) =
      coefficient e ≫ Spec.map (CommRingCat.ofHom (algebraMap A C)) := by
  rw [← inclusion_coefficient, Category.assoc, original, Category.assoc]
  exact congrArg (inclusion e ≫ ·) tensor_isPullback.w.symm

instance coefficient_etale [Algebra.Etale A B] : Etale (coefficient e) := by
  let _ := EtaleAlgebraFiniteBranch.localization_etale C e
  exact (HasRingHomProperty.Spec_iff (P := @Etale)).mpr
    (RingHom.etale_algebraMap.mpr inferInstance)

instance coefficient_isFinite [Module.Finite C (Localization.Away e)] :
    IsFinite (coefficient e) :=
  (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)

instance original_etale [Algebra.Etale A C] : Etale (original e) := by
  let _ : Etale (Spec.map (CommRingCat.ofHom (algebraMap A C))) :=
    (HasRingHomProperty.Spec_iff (P := @Etale)).mpr
      (RingHom.etale_algebraMap.mpr inferInstance)
  let _ : Etale
      (Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom) :
        Spec (.of (C ⊗[A] B)) ⟶ Spec (.of B)) :=
    MorphismProperty.of_isPullback tensor_isPullback inferInstance
  exact inferInstanceAs (Etale (inclusion e ≫ _))

/-- Points of the branch retain their exact original prime ideal. -/
theorem original_prime (Q : PrimeSpectrum (Localization.Away e)) :
    ((original e) Q).asIdeal = Q.asIdeal.comap
      ((algebraMap (C ⊗[A] B) (Localization.Away e)).comp
        Algebra.TensorProduct.includeRight.toRingHom) := rfl

/-- Points also retain their exact changed coefficient prime ideal. -/
theorem coefficient_prime (Q : PrimeSpectrum (Localization.Away e)) :
    ((coefficient e) Q).asIdeal =
      Q.asIdeal.comap (algebraMap C (Localization.Away e)) := rfl

end FLT.Mazur.EtaleFiniteBranchScheme
