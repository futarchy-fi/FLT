/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SpecMinimalPrimeFiniteOpen
public import FLT.Mazur.AffineGenericFiniteOpen

/-!
# Finite original affine sources near every minimal coefficient prime

The original affine source is transported through its own section algebra.
No component or nilpotent is removed from either side of the Cartesian square.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.AffineMinimalPrimeFiniteOpen
open Approximation SpecMinimalPrimeFiniteOpen
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [IsNoetherianRing R] {X : Scheme}
  (g : X ⟶ Spec (.of R)) [IsAffine X] [LocallyOfFinitePresentation g]
  [LocallyQuasiFinite g]
local instance : IsAffine (Over.mk g).left := inferInstanceAs (IsAffine X)
local instance : LocallyOfFinitePresentation (Over.mk g).hom :=
  inferInstanceAs (LocallyOfFinitePresentation g)
local notation "B" => affineBaseSections R (Over.mk g)

/-- A whole affine source becomes finite on one open containing the original minimal prime. -/
theorem exists_finite_principal (P : PrimeSpectrum R) (hP : P.asIdeal ∈ minimalPrimes R) :
    ∃ r : R, r ∉ P.asIdeal ∧ IsFinite (pullback.snd g (targetMap r)) := by
  let _ := AffineGenericFlatOpen.sectionAlgebra_quasiFinite g
  let _ := affineBaseSections_finitePresentation R (Over.mk g)
  obtain ⟨r, hr, hfin⟩ := SpecMinimalPrimeFiniteOpen.exists_finite_principal
    (algebraMap R B) P hP (RingHom.quasiFinite_algebraMap.mpr inferInstance)
    (RingHom.finiteType_algebraMap.mpr inferInstance)
  refine ⟨r, hr, ?_⟩
  let v := Spec.map (CommRingCat.ofHom (algebraMap R B))
  have hv : X.isoSpec.hom ≫ v = g := affineBaseSectionsSpecIso_over R (Over.mk g)
  let e := pullback.map g (targetMap r) v (targetMap r)
    X.isoSpec.hom (𝟙 _) (𝟙 _) (by simpa using hv.symm) (by simp)
  let _ : IsIso e := inferInstanceAs (IsIso (pullback.map _ _ _ _ _ _ _ _ _))
  let _ : IsFinite (pullback.snd v (targetMap r)) := hfin
  have he : pullback.snd g (targetMap r) = e ≫ pullback.snd v (targetMap r) := by
    simp only [e, pullback.map, pullback.lift_snd, Category.comp_id]
  rw [he]
  infer_instance

end FLT.Mazur.AffineMinimalPrimeFiniteOpen
