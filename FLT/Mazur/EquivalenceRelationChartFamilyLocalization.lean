/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationChartFamilyCorrections
public import FLT.Mazur.FiniteLocalizedBoundaryLifts

/-!
# Localized simultaneous corrections on finite normalized chart families

The rings are the actual invariant chart rings, exact boundary rings, and full
mixed relation rings. Localized solutions construct shared original numerators
and invariant boundary-kernel corrections after a common scalar power.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames.MixedFrames.ChartFamily
open SchemeFiniteGroupQuotient FiniteGroupRestriction PrincipalLocalizationMap
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] EquivalenceRelationNormalizedFrames.source
  InvariantBoundary.boundary MixedFrames.relation jointBoundaryTarget
variable {D A B : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p]
  (e : CategoryTheory.EquivalenceRelation p q)
  {ι : Type} (n : ι → ℕ) (o : ∀ a, Fin (n a))
  (U : ∀ a, (source p q (Fin (n a)) (o a)).Opens)
  (hU : ∀ a σ, (action e (Fin (n a)) (o a) σ).hom ⁻¹ᵁ U a = U a)

/-- First pullback from the actual invariant chart ring to the full mixed relation. -/
def firstCoefficientMap (a b : ι) :
    invariantCoordinates (restrictedAction (action e (Fin (n a)) (o a)) (U a) (hU a)) →+*
      Γ((mixedChartOpen (o a) (o b) (U a) (U b)).toScheme, ⊤) :=
  (mixedChartFirst (o a) (o b) (U a) (U b)).appTop.hom.comp
    (Subring.subtype _)

/-- Second pullback retains the independently indexed chart ring. -/
def secondCoefficientMap (a b : ι) :
    invariantCoordinates (restrictedAction (action e (Fin (n b)) (o b)) (U b) (hU b)) →+*
      Γ((mixedChartOpen (o a) (o b) (U a) (U b)).toScheme, ⊤) :=
  (mixedChartSecond (o a) (o b) (U a) (U b)).appTop.hom.comp
    (Subring.subtype _)

variable (i : B ⟶ A)

/-- Exact restriction from invariant chart functions to the original closed chart boundary. -/
def boundaryCoefficientMap (a : ι) :
    invariantCoordinates (restrictedAction (action e (Fin (n a)) (o a)) (U a) (hU a)) →+*
      Γ((InvariantBoundary.inclusion (Fin (n a)) (o a) i ⁻¹ᵁ U a).toScheme, ⊤) :=
  (InvariantBoundary.inclusion (Fin (n a)) (o a) i ∣_ U a).appTop.hom.comp
    (Subring.subtype _)

local notation "F" => firstCoefficientMap e n o U hU
local notation "G" => secondCoefficientMap e n o U hU
local notation "H" => boundaryCoefficientMap e n o U hU i
variable [Finite ι] (r : Sections e n o U hU)
  (hr : ∀ a b, firstCoefficientMap e n o U hU a b (r a) = secondCoefficientMap e n o U hU a b (r b))
  (v : ∀ a, Localization.Away (r a))
  (t : ∀ a, Γ((InvariantBoundary.inclusion (Fin (n a)) (o a) i ⁻¹ᵁ U a).toScheme, ⊤))
  (hb : ∀ a, map (boundaryCoefficientMap e n o U hU i a) (r a)
    (boundaryCoefficientMap e n o U hU i a (r a)) rfl (v a) =
    algebraMap _ (Localization.Away (boundaryCoefficientMap e n o U hU i a (r a))) (t a))
  (he : ∀ a b, map (firstCoefficientMap e n o U hU a b) (r a)
    (firstCoefficientMap e n o U hU a b (r a)) rfl (v a) =
    map (secondCoefficientMap e n o U hU a b) (r b)
      (firstCoefficientMap e n o U hU a b (r a)) (hr a b).symm (v b))

include hb he in
/-- Localized solutions construct compatible numerators with exact scaled boundary values. -/
theorem localized_original_numerators :
    ∃ N : ℕ, ∃ w : Sections e n o U hU,
      (∀ a, H a (w a) = H a (r a) ^ N * t a) ∧
      (∀ a b, F a b (w a) = G a b (w b)) :=
  FiniteLocalizedBoundaryLifts.exists_original_numerators H F G r hr v t hb he

include hb he in
/-- Actual simultaneous invariant kernel corrections are constructed for the scaled lifts. -/
theorem localized_kernel_corrections (s : Sections e n o U hU)
    (hs : ∀ a, H a (s a) = t a) :
    ∃ N : ℕ, ∃ z : Sections e n o U hU,
      (∀ a, H a (z a) = 0) ∧
      (∀ a b, F a b (r a ^ N * s a - z a) = G a b (r b ^ N * s b - z b)) := by
  obtain ⟨N, w, hw, hc⟩ := localized_original_numerators e n o U hU i r hr v t hb he
  refine ⟨N, fun a ↦ r a ^ N * s a - w a, ?_, ?_⟩
  · intro a
    rw [map_sub, map_mul, map_pow, hs a, hw a, sub_self]
  · intro a b
    simpa only [sub_sub_cancel] using hc a b

end FLT.Mazur.EquivalenceRelationNormalizedFrames.MixedFrames.ChartFamily
