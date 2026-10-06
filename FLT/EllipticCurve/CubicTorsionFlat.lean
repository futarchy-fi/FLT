/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CubicTorsionLocalFree
public import FLT.EllipticCurve.CubicTorsionEtaleFibers
public import Mathlib.RingTheory.Flat.Localization

/-! # Finite flat and étale torsion over integral bases -/

open scoped TensorProduct
open Module IsLocalRing
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
@[expose] public noncomputable section
namespace WeierstrassCurve.CubicCharts
universe u
/-- Constant field-fiber dimension makes a finite module over an integral domain flat. -/
theorem flat_of_field_finrank_constant
    (R M : Type u) [CommRing R] [IsDomain R] [AddCommGroup M]
    [Module R M] [Module.Finite R M] (d : ℕ)
    (h : ∀ (K : Type u) [Field K] [Algebra R K],
      Module.finrank K (K ⊗[R] M) = d) : Module.Flat R M := by
  apply Module.flat_of_localized_maximal
  intro p hp
  let S := Localization.AtPrime p
  have hbase (K : Type u) [Field K] [Algebra S K] :
      Module.finrank K (K ⊗[S] (S ⊗[R] M)) = d := by
    let : Algebra R K := ((algebraMap S K).comp (algebraMap R S)).toAlgebra
    have : IsScalarTower R S K := IsScalarTower.of_algebraMap_eq' rfl
    exact (TensorProduct.AlgebraTensorModule.cancelBaseChange R S K K M).finrank_eq.trans (h K)
  have : Module.Free S (S ⊗[R] M) :=
    free_of_residue_generic_finrank_eq S (S ⊗[R] M) (FractionRing S)
      ((hbase (ResidueField S)).trans (hbase (FractionRing S)).symm)
  have : Module.Flat S (S ⊗[R] M) := inferInstance
  have : Module.Flat R (S ⊗[R] M) := Module.Flat.trans R S _
  exact Module.Flat.of_linearEquiv
    ((LocalizedModule.equivTensorProduct p.primeCompl M).restrictScalars R)

variable {R : Type u} [CommRing R] [IsNoetherianRing R] [IsDomain R]
variable (W : WeierstrassCurve R) [W.IsElliptic]
/-- Invertible-order torsion has a flat coordinate algebra over a noetherian integral base. -/
theorem torsionCoordinate_flat (n : ℕ) [NeZero n] (hn : IsUnit (n : R)) :
    Module.Flat R (torsionCoordinateRing W n) := by
  have : Module.Finite R (torsionCoordinateRing W n) := torsionCoordinateRing_finite W n
  apply flat_of_field_finrank_constant R (torsionCoordinateRing W n) (n ^ 2)
  intro K _ _
  exact torsionCoordinate_field_finrank_of_isUnit W n K
    (by simpa using hn.map (algebraMap R K))

/-- The actual coordinate Hopf algebra is finite flat for invertible torsion order. -/
theorem torsionCoordinate_isFiniteFlat (n : ℕ) [NeZero n] (hn : IsUnit (n : R)) :
    HopfAlgebra.IsFiniteFlat R (torsionCoordinateRing W n) := by
  have := torsionCoordinateRing_finite W n
  have := torsionCoordinate_flat W n hn
  exact ⟨⟩

/-- Invertible-order torsion has an étale coordinate algebra over an integral base. -/
theorem torsionCoordinate_etale (n : ℕ) [NeZero n] (hn : IsUnit (n : R)) :
    Algebra.Etale R (torsionCoordinateRing W n) := by
  have := torsionCoordinateRing_finite W n
  have := torsionCoordinate_flat W n hn
  have := torsionCoordinate_formallyUnramified W n hn
  have : Algebra.FinitePresentation R (torsionCoordinateRing W n) :=
    (Algebra.FinitePresentation.of_finiteType (R := R)).mp inferInstance
  exact Algebra.Etale.of_formallyUnramified_of_flat

/-- The represented torsion kernel is étale when its order is invertible in the integral base. -/
theorem torsionModel_etale (n : ℕ) [NeZero n] (hn : IsUnit (n : R)) :
    AlgebraicGeometry.Etale (torsionModel W n).hom := by
  open AlgebraicGeometry CategoryTheory in
  have hf : Etale (Spec.map (CommRingCat.ofHom
      (algebraMap R (torsionCoordinateRing W n)))) := by
    rw [HasRingHomProperty.Spec_iff (P := @Etale)]
    change (algebraMap R (torsionCoordinateRing W n)).Etale
    rw [RingHom.etale_algebraMap]
    exact torsionCoordinate_etale W n hn
  open AlgebraicGeometry CategoryTheory in
  change Etale (Scheme.Spec.map (Spec.fullyFaithful.preimage
    ((torsionModel W n).left.isoSpec.inv ≫ (torsionModel W n).hom))) at hf
  rw [AlgebraicGeometry.Spec.fullyFaithful.map_preimage] at hf
  exact (CategoryTheory.MorphismProperty.cancel_left_of_respectsIso
    @AlgebraicGeometry.Etale (torsionModel W n).left.isoSpec.inv
      (torsionModel W n).hom).mp hf

end WeierstrassCurve.CubicCharts
