/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeScalarIntegralBadCover
public import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
public import Mathlib.RingTheory.Unramified.Locus

/-!
# Principal rigidity neighborhoods from actual scalar differentials

An annihilator of the relative differential module constructs an unramified
principal open on the unchanged affine source. No Noetherian hypothesis on
the scalar ring is used. Essential finite type makes these neighborhoods
cover precisely the complement of differential support.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.ScalarDifferentialPrincipalRigidity
open SchemeScalarPrincipalNeighborhood
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- A differential annihilator constructs a formally unramified localization. -/
theorem away_formallyUnramified {R A : Type} [CommRing R] [CommRing A] [Algebra R A]
    (a : A) (ha : a ∈ Module.annihilator A (KaehlerDifferential R A)) :
    Algebra.FormallyUnramified R (Localization.Away a) := by
  apply Algebra.basicOpen_subset_unramifiedLocus_iff.mp
  intro P hP
  rw [Algebra.unramifiedLocus_eq_compl_support]
  intro hp
  exact hP (Module.annihilator_le_of_mem_support hp ha)

/-- Every unramified prime has an actual differential annihilator avoiding it. -/
theorem exists_annihilator {R A : Type} [CommRing R] [CommRing A] [Algebra R A]
    [Algebra.EssFiniteType R A] (P : PrimeSpectrum A)
    (hP : P ∈ Algebra.unramifiedLocus R A) :
    ∃ a ∈ Module.annihilator A (KaehlerDifferential R A), a ∉ P.asIdeal := by
  rw [Algebra.unramifiedLocus_eq_compl_support, Module.support_eq_zeroLocus] at hP
  exact Set.not_subset.mp hP

variable {R : Type} [CommRing R] {X : Scheme.{0}} [IsAffine X]
  (s : R →+* Γ(X, ⊤))

/-- Formal unramifiedness of actual scalar coefficients gives scheme rigidity. -/
theorem scalar_formallyUnramified (hs : s.FormallyUnramified) :
    FormallyUnramified (scalarMorphism s) := by
  let _ : FormallyUnramified (Spec.map (CommRingCat.ofHom s)) :=
    (HasRingHomProperty.Spec_iff (P := @FormallyUnramified)).mpr hs
  exact MorphismProperty.comp_mem _ _ _ inferInstance inferInstance

/-- The full scheme principal open inherits the constructed coefficient rigidity. -/
theorem principal_formallyUnramified (a : Γ(X, ⊤))
    (ha : let _ := s.toAlgebra
      a ∈ Module.annihilator Γ(X, ⊤) (KaehlerDifferential R Γ(X, ⊤))) :
    FormallyUnramified ((X.basicOpen a).ι ≫ scalarMorphism s) := by
  let _ := s.toAlgebra
  let U := X.basicOpen a
  let _ : Algebra R Γ(U, ⊤) := (U.ι.appTop.hom.comp s).toAlgebra
  let _ : IsScalarTower R Γ(X, ⊤) Γ(U, ⊤) :=
    IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)
  let _ := away_formallyUnramified a ha
  let e := (IsLocalization.algEquiv (Submonoid.powers a)
    (Localization.Away a) Γ(U, ⊤)).restrictScalars R
  have h : Algebra.FormallyUnramified R Γ(U, ⊤) :=
    Algebra.FormallyUnramified.of_equiv e
  rw [← scalarMorphism_comp]
  exact scalar_formallyUnramified _ h

end FLT.Mazur.ScalarDifferentialPrincipalRigidity
