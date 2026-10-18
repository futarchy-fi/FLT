/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteGroupFreeProjective
public import FLT.Mazur.SchemeFiniteGroupFreeBoundary
public import FLT.Mazur.SchemeEffectiveEpiSections
public import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-!
# Faithful descent for free affine finite-group quotients

Field-valued freeness makes the actual quotient finite and faithfully flat.
Every coefficient base change is an effective epimorphism. All coefficients,
including nilpotents, are detected and compatible sections descend uniquely.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open FLT.Mazur.SchemeCoordinateAction
namespace FLT.Mazur.SchemeFiniteGroupQuotient
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {G : Type u} [Group G] [Finite G] {X : Scheme.{u}} [IsAffine X]
  (ρ : G →* Aut X)
  (hfree : ∀ (K : Type u) [Field K] (a : Spec (.of K) ⟶ X) (g : G),
    a ≫ (ρ g).hom = a → g = 1)
include hfree

/-- The free quotient is finite, without any additional finite-type assumption. -/
theorem quotientMap_finite_of_free : IsFinite (quotientMap ρ) := by
  let _ := coordinateAction ρ
  let _ := FiniteGroupQuotient.invariant_module_finite G
    (coordinate_fixedPointIdeal_eq_top ρ hfree)
  let _ : IsFinite (FiniteGroupQuotient.quotientMap G Γ(X, ⊤)) :=
    (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)
  change IsFinite (X.toSpecΓ ≫ FiniteGroupQuotient.quotientMap G Γ(X, ⊤))
  infer_instance

/-- Finite projectivity proves flatness of the actual original quotient. -/
theorem quotientMap_flat_of_free : Flat (quotientMap ρ) := by
  let _ := coordinateAction ρ
  let _ := FiniteGroupQuotient.invariant_module_projective G
    (coordinate_fixedPointIdeal_eq_top ρ hfree)
  let _ : Flat (FiniteGroupQuotient.quotientMap G Γ(X, ⊤)) :=
    Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)
  change Flat (X.toSpecΓ ≫ FiniteGroupQuotient.quotientMap G Γ(X, ⊤))
  infer_instance

variable {B : Scheme.{u}} (b : B ⟶ quotient ρ)
local notation "π" => pullback.snd (quotientMap ρ) b

/-- Every original coefficient base change is a genuine effective descent cover. -/
theorem freeQuotient_baseChange_effectiveEpi : EffectiveEpi π := by
  let _ := quotientMap_finite_of_free ρ hfree
  let _ := quotientMap_flat_of_free ρ hfree
  infer_instance

/-- Pulling functions to the original free quotient chart loses no coefficients. -/
theorem freeQuotient_baseChange_appTop_injective : Function.Injective (π).appTop := by
  let _ := freeQuotient_baseChange_effectiveEpi ρ hfree b
  exact SchemeEffectiveEpiSections.appTop_injective π

/-- Every fixed ideal-power equation reflects at exactly the same exponent. -/
theorem freeQuotient_baseChange_power_iff (J : Ideal Γ(B, ⊤)) (k : ℕ) :
    (J.map (π).appTop.hom) ^ k = ⊥ ↔ J ^ k = ⊥ := by
  rw [← Ideal.map_pow]
  exact Ideal.map_eq_bot_iff_of_injective
    (freeQuotient_baseChange_appTop_injective ρ hfree b)

/-- Compatible chart functions descend to the full coefficient scheme uniquely. -/
theorem freeQuotient_baseChange_sections (t : Γ(pullback (quotientMap ρ) b, ⊤))
    (ht : (pullback.fst π π).appTop t = (pullback.snd π π).appTop t) :
    ∃! u : Γ(B, ⊤), (π).appTop u = t := by
  let _ := freeQuotient_baseChange_effectiveEpi ρ hfree b
  exact SchemeEffectiveEpiSections.sections_existsUnique (IsPullback.of_hasPullback π π) t ht

/-- For affine coefficients this is the actual faithfully flat map of coordinate rings. -/
theorem freeQuotient_baseChange_faithfullyFlat [IsAffine B] :
    (π).appTop.hom.FaithfullyFlat := by
  let _ := quotientMap_finite_of_free ρ hfree
  let _ := quotientMap_flat_of_free ρ hfree
  let _ : IsAffine (pullback (quotientMap ρ) b) := isAffine_of_isAffineHom π
  exact (Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine π).mp
    ⟨inferInstance, inferInstance⟩

end FLT.Mazur.SchemeFiniteGroupQuotient
