/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicQuotientOpens

/-!
# Cross-characteristic relation spans on the quotient overlap opens

Both arms of the constructed transition spans factor through the explicit
overlap opens of the finite quotient targets. The source arms cover the
entire quotient overlap. No assertion that these spans are graphs of
isomorphisms, or that the quotient overlaps already glue, is made here.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.CyclicCharacteristicAtlas
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-- An actual scheme map factors through an integer-invertible open when its source inverts it. -/
def integerOpenLift {T S : Scheme} (f : T ⟶ S) (m : ℕ) (hm : IsUnit (m : Γ(T, ⊤))) :
    T ⟶ (CharacteristicTwoThree.unitOpen S m).toScheme :=
  IsOpenImmersion.lift (CharacteristicTwoThree.unitOpen S m).ι f (by
    rintro _ ⟨x, rfl⟩
    refine ⟨⟨f x, ?_⟩, rfl⟩
    change x ∈ f ⁻¹ᵁ S.basicOpen (m : Γ(S, ⊤))
    rw [Scheme.preimage_basicOpen_top, map_natCast, T.basicOpen_of_isUnit hm]
    trivial)

/-- This factorization retains the original scheme morphism. -/
@[reassoc] theorem integerOpenLift_inclusion {T S : Scheme} (f : T ⟶ S) (m : ℕ)
    (hm : IsUnit (m : Γ(T, ⊤))) :
    integerOpenLift f m hm ≫ (CharacteristicTwoThree.unitOpen S m).ι = f :=
  IsOpenImmersion.lift_fac _ _ _

variable (n : ℕ) [NeZero n] (b : Bool) (i : (transitionCover n b).I₀)

/-- The original arm lands in the actual quotient overlap open. -/
def quotientTransitionSource :
    (transitionCover n b).X i ⟶ (quotientTransitionOpen n b).toScheme :=
  integerOpenLift (transitionSource n b i ≫ normalizedQuotientMap n b) _ (by
    have h := (CharacteristicTwoThree.unitOpen_isUnit
      (normalizedLocus n b) (chartInteger (!b))).map ((transitionCover n b).f i).appTop.hom
    simpa only [map_natCast] using h)

/-- The opposite arm lands in the other actual quotient overlap open. -/
def quotientTransitionTarget :
    (transitionCover n b).X i ⟶ (quotientTransitionOpen n (!b)).toScheme :=
  integerOpenLift (transitionTarget n b i ≫ normalizedQuotientMap n (!b)) _ (by
    have h := (normalizedLocus_chartInteger_isUnit n b).map (transitionSource n b i).appTop.hom
    simpa only [map_natCast, Bool.not_not] using h)

/-- The restricted source arm retains the original quotient parameter. -/
@[reassoc] theorem quotientTransitionSource_inclusion :
    quotientTransitionSource n b i ≫ (quotientTransitionOpen n b).ι =
      transitionSource n b i ≫ normalizedQuotientMap n b := integerOpenLift_inclusion _ _ _

/-- The restricted target arm retains the original opposite quotient parameter. -/
@[reassoc] theorem quotientTransitionTarget_inclusion :
    quotientTransitionTarget n b i ≫ (quotientTransitionOpen n (!b)).ι =
      transitionTarget n b i ≫ normalizedQuotientMap n (!b) := integerOpenLift_inclusion _ _ _

/-- The source arms cover every point of the actual quotient overlap open. -/
theorem quotientTransitionSource_covers (y : (quotientTransitionOpen n b).toScheme) :
    ∃ i, y ∈ Set.range (quotientTransitionSource n b i) := by
  obtain ⟨x, hx⟩ := (normalizedQuotientMap n b).surjective y.1
  have hxO : x ∈ transitionOpen n b := by
    rw [← quotientTransitionOpen_preimage]
    change normalizedQuotientMap n b x ∈ quotientTransitionOpen n b
    rw [hx]
    exact y.2
  obtain ⟨i, z, hz⟩ := (transitionSource_covers n b x).mpr hxO
  refine ⟨i, z, ?_⟩
  apply Subtype.ext
  change (quotientTransitionOpen n b).ι (quotientTransitionSource n b i z) = y.1
  rw [← Scheme.Hom.comp_apply, quotientTransitionSource_inclusion]
  change normalizedQuotientMap n b (transitionSource n b i z) = y.1
  rw [hz, hx]

end FLT.Mazur.CyclicCharacteristicAtlas
