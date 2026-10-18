/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationBoundaryRankThickenings
public import FLT.Mazur.FiniteGroupEquivariantOpenBoundary
public import FLT.Mazur.SchemeFiniteGroupFreeFlat
public import FLT.Mazur.IdealSheafFlatDetection
public import FLT.Mazur.IdealSheafPowerPullback

/-!
# Faithful descent from the full original normalized boundary chart

The chart-to-product map itself is finite and faithfully flat, by freeness of
the original normalized frame action. This holds before selecting any rank
stage. It does not assert flatness of the maps from differing rank stages.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames
open AffineScalarBoundaryNilpotence FiniteGroupRestriction SchemeFiniteGroupQuotient
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] source action restrictedAction boundaryProduct
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p]
  (n : ℕ) (o : Fin n) (U : (source p q (Fin n) o).Opens)
  (e : CategoryTheory.EquivalenceRelation p q)
  (hU : ∀ g : Equiv.Perm (Fin n), (action e (Fin n) o g).hom ⁻¹ᵁ U = U)
  [IsAffine U.toScheme]
local notation "ρ" => restrictedAction (action e (Fin n) o) U hU

omit [IsAffine U.toScheme] in
/-- The stable original chart retains the actual field-valued freeness of normalized frames. -/
theorem boundaryChart_action_free (K : Type) [Field K]
    (a : Spec (.of K) ⟶ U.toScheme) (g : Equiv.Perm (Fin n))
    (hg : a ≫ (ρ g).hom = a) : g = 1 := by
  exact restrictedAction_free (action e (Fin n) o) U hU
    (fun _ _ a g hg ↦ action_free e (Fin n) o a g hg) K a g hg

variable {R T : Type} [CommRing R] [CommRing T]
  (s : R →+* invariantCoordinates (restrictedAction (action e (Fin n) o) U hU))
  (κ : R →+* T)
local notation "π" => chartBoundaryProduct n o U e hU s κ

/-- The full original chart cover is finite, before any rank restriction. -/
instance chartBoundaryProduct_finite : IsFinite π := by
  let _ := quotientMap_finite_of_free ρ (boundaryChart_action_free n o U e hU)
  unfold chartBoundaryProduct
  infer_instance

/-- The full original chart cover is flat over every original boundary coefficient ring. -/
instance chartBoundaryProduct_flat : Flat π := by
  let _ := quotientMap_flat_of_free ρ (boundaryChart_action_free n o U e hU)
  unfold chartBoundaryProduct
  infer_instance

/-- Every original scalar product point is covered by this flat chart morphism. -/
instance chartBoundaryProduct_surjective_instance : Surjective π :=
  ⟨chartBoundaryProduct_surjective n o U e hU s κ⟩

/-- The full original product has effective descent along its actual chart cover. -/
instance chartBoundaryProduct_effectiveEpi : EffectiveEpi π := by
  infer_instance

/-- No original scalar product coefficient is lost on the normalized chart. -/
theorem chartBoundaryProduct_appTop_injective : Function.Injective (π).appTop :=
  SchemeEffectiveEpiSections.appTop_injective π

/-- Every ideal-power equation on the full product is detected at the same chart order. -/
theorem chartBoundaryProduct_ideal_power_iff
    (J : Ideal Γ(boundaryProduct s κ, ⊤)) (k : ℕ) :
    (J.map (π).appTop.hom) ^ k = ⊥ ↔ J ^ k = ⊥ := by
  rw [← Ideal.map_pow]
  exact Ideal.map_eq_bot_iff_of_injective
    (chartBoundaryProduct_appTop_injective n o U e hU s κ)

/-- Entire ideal sheaves, including nilpotents, are detected by the original chart. -/
theorem chartBoundaryProduct_idealSheaf_injective :
    Function.Injective (fun J : (boundaryProduct s κ).IdealSheafData ↦ J.comap π) :=
  FCurve.idealSheaf_comap_injective π

/-- Chart pullback reflects a sheaf power equation without changing its exponent. -/
theorem chartBoundaryProduct_sheaf_power_iff
    (J : (boundaryProduct s κ).IdealSheafData) (k : ℕ) :
    J.comap π ^ k = ⊥ ↔ J ^ k = ⊥ := by
  rw [← IdealSheafPowerPullback.comap_pow]
  constructor
  · intro h
    apply chartBoundaryProduct_idealSheaf_injective n o U e hU s κ
    simpa only [Scheme.IdealSheafData.comap_bot] using h
  · intro h
    rw [h, Scheme.IdealSheafData.comap_bot]

/-- The actual kernel pair descends every compatible full chart coefficient uniquely. -/
theorem chartBoundaryProduct_sections (t : Γ(chartBoundary n o U e hU s κ, ⊤))
    (ht : (pullback.fst π π).appTop t = (pullback.snd π π).appTop t) :
    ∃! u : Γ(boundaryProduct s κ, ⊤), (π).appTop u = t :=
  SchemeEffectiveEpiSections.sections_existsUnique (IsPullback.of_hasPullback π π) t ht

end FLT.Mazur.EquivalenceRelationNormalizedFrames
