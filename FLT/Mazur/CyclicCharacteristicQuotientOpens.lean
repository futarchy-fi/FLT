/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicTransitionSpan

/-!
# Characteristic domains of the actual finite quotient schemes

The required auxiliary integer is invertible on the original normalized
chart and hence on its surjective finite quotient. Pullback of the opposite
characteristic open is the actual transition open. Thus cross-characteristic
gluing is supported on these explicit open subschemes of the quotient targets.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.CyclicCharacteristicAtlas
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-- A surjective scheme morphism reflects units in global functions. -/
theorem isUnit_of_surjective_appTop {X Y : Scheme} (f : X ⟶ Y) [Surjective f]
    (r : Γ(Y, ⊤)) (hr : IsUnit (f.appTop r)) : IsUnit r := by
  apply Y.toRingedSpace.isUnit_of_isUnit_germ
  intro y hy
  obtain ⟨x, rfl⟩ := f.surjective y
  apply (Y.mem_basicOpen_top r (f x)).mp
  change x ∈ f ⁻¹ᵁ Y.basicOpen r
  rw [Scheme.preimage_basicOpen_top, X.basicOpen_of_isUnit hr]
  trivial

variable (n : ℕ) [NeZero n] (b : Bool)

/-- The actual normalized chart inverts its defining auxiliary integer. -/
theorem normalizedLocus_chartInteger_isUnit :
    IsUnit (chartInteger b : Γ(normalizedLocus n b, ⊤)) := by
  cases b
  · let f : normalizedLocus n false ⟶ UniversalWeierstrass.parameterBase :=
      normalizedInclusion n false ≫
        UniversalWeierstrass.cyclicHomUniversalMultiplicationLocusInclusion n ≫
          (UniversalWeierstrass.cyclicHomAuxiliaryScheme n).hom
    have h := (UniversalWeierstrass.parameter_two_isUnit.map
      (Scheme.ΓSpecIso (.of UniversalWeierstrass.ParameterRing)).inv.hom).map f.appTop.hom
    simpa only [chartInteger, Nat.cast_ofNat, map_ofNat] using h
  · let f : normalizedLocus n true ⟶ OddWeierstrassParameter.parameterBase :=
      normalizedInclusion n true ≫
        OddWeierstrassParameter.cyclicHomUniversalMultiplicationLocusInclusion n ≫
          (OddWeierstrassParameter.cyclicHomAuxiliaryScheme n).hom
    have h := (IntegralWeierstrassParameter.oddChart_three_isUnit.map
      (Scheme.ΓSpecIso (.of IntegralWeierstrassParameter.OddChartRing)).inv.hom).map
        f.appTop.hom
    simpa only [chartInteger, Nat.cast_ofNat, map_ofNat] using h

/-- The defining auxiliary integer also descends as a unit on the actual quotient. -/
theorem normalizedQuotient_chartInteger_isUnit :
    IsUnit (chartInteger b : Γ(normalizedQuotient n b, ⊤)) := by
  apply isUnit_of_surjective_appTop (normalizedQuotientMap n b)
  simpa only [map_natCast] using normalizedLocus_chartInteger_isUnit n b

/-- The actual open in the quotient on which the other characteristic is available. -/
def quotientTransitionOpen : (normalizedQuotient n b).Opens :=
  CharacteristicTwoThree.unitOpen (normalizedQuotient n b) (chartInteger (!b))

/-- Its scheme-theoretic open preimage is precisely the original transition domain. -/
theorem quotientTransitionOpen_preimage :
    (normalizedQuotientMap n b) ⁻¹ᵁ quotientTransitionOpen n b = transitionOpen n b := by
  unfold quotientTransitionOpen transitionOpen CharacteristicTwoThree.unitOpen
  rw [Scheme.preimage_basicOpen_top, map_natCast]

end FLT.Mazur.CyclicCharacteristicAtlas
