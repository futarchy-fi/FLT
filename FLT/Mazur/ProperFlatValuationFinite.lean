/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.ProperValuationGenericFinite
public import FLT.Mazur.ValuationFieldFlatCover
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# A proper flat valuation model with finite generic fiber is finite

Pass to a dominating valuation ring in an algebraic closure of the exact fraction
field. The new generic fiber is the base change of the original finite scheme.
Its geometric finiteness descends to the original proper model by finite fibers.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace FLT.Mazur.ProperFlatValuationFinite

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R K : Type} [CommRing R] [IsDomain R] [ValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]
  {X : Scheme} (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f]

/-- The whole proper flat model is finite when its actual generic fiber is finite. -/
theorem finite_of_generic
    [IsFinite (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K))))] :
    IsFinite f := by
  let L := AlgebraicClosure K
  let _ : FaithfulSMul R L := (faithfulSMul_iff_algebraMap_injective R L).mpr (by
    rw [IsScalarTower.algebraMap_eq R K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective R K))
  obtain ⟨A, φ, hφ, _, hfaithful⟩ :=
    ValuationFieldFlatCover.exists_valuation_cover (R := R) (L := L)
  let g := Spec.map (CommRingCat.ofHom φ)
  have hg : Flat g ∧ Surjective g := (flat_and_surjective_SpecMap_iff
    (CommRingCat.ofHom φ)).mpr hfaithful
  let _ : Flat g := hg.1
  let _ : Surjective g := hg.2
  let b := Spec.map (CommRingCat.ofHom (algebraMap R K))
  let c := Spec.map (CommRingCat.ofHom (algebraMap K L))
  let q := Spec.map (CommRingCat.ofHom (algebraMap A L))
  have hsq : q ≫ g = c ≫ b := by
    dsimp only [q, g, c, b]
    rw [← Spec.map_comp, ← Spec.map_comp]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    change A.subtype.comp φ = (algebraMap K L).comp (algebraMap R K)
    rw [hφ, IsScalarTower.algebraMap_eq R K L]
  let _ : IsFinite (pullback.snd (pullback.snd f g) q) :=
    ProperValuationGenericFinite.finite_generic_baseChange f g q b c hsq
  let _ : IsFinite (pullback.snd f g) :=
    ProperValuationGenericFinite.finite_geometric (K := L) (pullback.snd f g)
  exact ProperValuationGenericFinite.finite_of_surjective_baseChange f g

end FLT.Mazur.ProperFlatValuationFinite
