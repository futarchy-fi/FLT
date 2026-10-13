/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SmoothFiniteCoefficientBranch
public import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!
# Actual translation branches after an etale coefficient change

A principal branch of the changed translation has maps to both the new base
and the original translation. Finiteness is relative to the new base only.
The two maps retain the original base square and the chosen prime.
-/

@[expose] public noncomputable section
open TensorProduct CategoryTheory AlgebraicGeometry
attribute [local instance] Algebra.TensorProduct.rightAlgebra
namespace FLT.Mazur.EtaleTranslationBranch
universe u
set_option backward.isDefEq.respectTransparency false
variable {R S B : Type u} [CommRing R] [CommRing S] [CommRing B]
  [Algebra R S] [Algebra R B] (e : S ⊗[R] B)

/-- The actual affine branch, with its localization coefficients. -/
def source : Scheme := Spec (.of (Localization.Away e))

/-- Its map into the complete coefficient-changed translation. -/
def inclusion : source e ⟶ Spec (.of (S ⊗[R] B)) :=
  Spec.map (CommRingCat.ofHom (algebraMap (S ⊗[R] B) (Localization.Away e)))

/-- The branch structural map to the NEW base. -/
def toBase : source e ⟶ Spec (.of S) :=
  Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away e)))

/-- The actual refinement map to the ORIGINAL translation. -/
def toOriginal : source e ⟶ Spec (.of B) :=
  Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away e)))

instance source_affine : IsAffine (source e) := inferInstanceAs (IsAffine (Spec _))

instance inclusion_isOpenImmersion : IsOpenImmersion (inclusion e) :=
  inferInstanceAs (IsOpenImmersion (Spec.map (CommRingCat.ofHom
    (algebraMap (S ⊗[R] B) (Localization.Away e)))))

/-- The refinement preserves the original structural map, through the changed base. -/
@[reassoc]
theorem base_square :
    toOriginal e ≫ Spec.map (CommRingCat.ofHom (algebraMap R B)) =
      toBase e ≫ Spec.map (CommRingCat.ofHom (algebraMap R S)) := by
  rw [toOriginal, toBase, ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact (IsScalarTower.algebraMap_eq R B (Localization.Away e)).symm.trans
    (IsScalarTower.algebraMap_eq R S (Localization.Away e))

/-- Over the changed base the actual branch is etale whenever the translation is etale. -/
instance toBase_etale [Algebra.Etale R B] : Etale (toBase e) :=
  HasRingHomProperty.Spec_iff.mpr (RingHom.etale_algebraMap.mpr inferInstance)

/-- The map to the original translation is etale for an etale coefficient change. -/
instance toOriginal_etale [Algebra.Etale R S] : Etale (toOriginal e) := by
  let _ := FCurve.etale_coefficient_branch (R := R) e
  exact HasRingHomProperty.Spec_iff.mpr (RingHom.etale_algebraMap.mpr inferInstance)

/-- A finite branch gives an actual finite morphism over the changed base. -/
instance toBase_finite [Module.Finite S (Localization.Away e)] : IsFinite (toBase e) :=
  (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)

/-- Every prime avoiding the branch coefficient lifts through the actual localization map. -/
theorem exists_branch_point (P : Ideal (S ⊗[R] B)) [P.IsPrime] (he : e ∉ P) :
    ∃ x : source e, inclusion e x = (⟨P, inferInstance⟩ : PrimeSpectrum (S ⊗[R] B)) := by
  have hd : Disjoint (Submonoid.powers e : Set (S ⊗[R] B)) (P : Set _) := by
    rwa [Ideal.disjoint_powers_iff_notMem_of_isPrime]
  let Q := P.map (algebraMap (S ⊗[R] B) (Localization.Away e))
  let _ : Q.IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (.powers e) _ P inferInstance hd
  refine ⟨⟨Q, inferInstance⟩, PrimeSpectrum.ext ?_⟩
  exact IsLocalization.under_map_of_isPrime_disjoint (.powers e) _ inferInstance hd

/-- The lifted branch point retains the prescribed ORIGINAL translation point. -/
theorem exists_branch_point_over (P : Ideal (S ⊗[R] B)) [P.IsPrime] (he : e ∉ P)
    (q : PrimeSpectrum B)
    (hP : P.comap Algebra.TensorProduct.includeRight.toRingHom = q.asIdeal) :
    ∃ x : source e, toOriginal e x = q := by
  obtain ⟨x, hx⟩ := exists_branch_point e P he
  refine ⟨x, PrimeSpectrum.ext ?_⟩
  have h := congrArg PrimeSpectrum.asIdeal hx
  change x.asIdeal.comap (algebraMap (S ⊗[R] B) (Localization.Away e)) = P at h
  change x.asIdeal.comap (algebraMap B (Localization.Away e)) = q.asIdeal
  rw [IsScalarTower.algebraMap_eq B (S ⊗[R] B) (Localization.Away e),
    ← Ideal.comap_comap, h]
  exact hP

end FLT.Mazur.EtaleTranslationBranch
