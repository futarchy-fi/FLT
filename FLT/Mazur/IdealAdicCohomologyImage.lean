/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealAdicCohomology

/-!
# Images of ideal-power cohomology

The filtration is the image of the actual inclusion on cohomology, with the
specified base-ring action. Exactness identifies it with the kernel of the
actual quotient map; no comparison with the adic topology is assumed.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
open FLT.Mazur.FCurve FLT.Mazur.GlobalIdealPower
open FLT.Mazur.GlobalIdealPowerCompatibility

universe u

namespace FLT.Mazur.IdealAdicQuotient

local instance imageHasExt (X : Scheme.{u}) :
    HasExt.{u + 1} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
  HasExt.standard _

variable {X : Scheme.{u}} [IsLocallyNoetherian X]
  {R : Type u} [CommRing R] (ρ : R →+* Γ(X, ⊤))
  (I : X.IdealSheafData) (M : X.Modules) [M.IsFinitePresentation]

/-- The image of the n-th ideal-power inclusion on base-ring cohomology. -/
def cohomologyImage (q n : ℕ) : Submodule R (ModuleRingH ρ M q) :=
  LinearMap.range ((moduleRingHFunctor ρ q).map (inclusion (I ^ n) M)).hom

omit [IsLocallyNoetherian X] [M.IsFinitePresentation] in
/-- Image membership records a lift through the original power inclusion. -/
lemma mem_cohomologyImage (q n : ℕ) (x : ModuleRingH ρ M q) :
    x ∈ cohomologyImage ρ I M q n ↔
      ∃ y, moduleHMap (inclusion (I ^ n) M) q y = x := Iff.rfl

/-- Increasing the ideal exponent decreases the cohomology image. -/
lemma cohomologyImage_antitone (q : ℕ) : Antitone (cohomologyImage ρ I M q) := by
  intro a b hab x hx
  obtain ⟨y, rfl⟩ := hx
  refine ⟨moduleHMap (transition I M hab) q y, ?_⟩
  change moduleHMap (inclusion (I ^ a) M) q (moduleHMap (transition I M hab) q y) = _
  rw [← LinearMap.comp_apply, ← moduleHMap_comp, transition_comp]
  rfl

/-- The zeroth power image is the whole cohomology module. -/
@[simp]
lemma cohomologyImage_zero (q : ℕ) : cohomologyImage ρ I M q 0 = ⊤ := by
  apply LinearMap.range_eq_top.mpr
  have hi : IsIso (inclusion (I ^ 0) M) := by
    rw [pow_zero, Scheme.IdealSheafData.one_eq_top]
    infer_instance
  exact (ModuleCat.epi_iff_surjective
    ((moduleRingHFunctor ρ q).map (inclusion (I ^ 0) M))).mp inferInstance

/-- Exactness identifies the image with the kernel of the actual quotient map. -/
lemma cohomologyImage_eq_ker (q n : ℕ) :
    cohomologyImage ρ I M q n =
      LinearMap.ker ((moduleRingHFunctor ρ q).map (projection I M n)).hom := by
  let S := ShortComplex.cokernelSequence (inclusion (I ^ n) M)
  have hAb : (moduleAbelianComplex S).ShortExact :=
    CoherentDevissage.moduleToSheaf_shortExact (quotient_shortExact I M n)
  have he : Function.Exact (moduleHMap S.f q) (moduleHMap S.g q) :=
    (ShortComplex.ab_exact_iff_function_exact _).mp (Sheaf.H.longSequence_exact₂' hAb q)
  ext x
  exact (he x).symm

/-- A class lies in the power image precisely when its quotient restriction vanishes. -/
lemma mem_cohomologyImage_iff (q n : ℕ) (x : ModuleRingH ρ M q) :
    x ∈ cohomologyImage ρ I M q n ↔ moduleHMap (projection I M n) q x = 0 := by
  rw [cohomologyImage_eq_ker]
  rfl

end FLT.Mazur.IdealAdicQuotient
