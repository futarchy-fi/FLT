/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearInitialFiber
public import FLT.Mazur.WeierstrassCoefficientShearRetainedFiber
public import FLT.Mazur.WeierstrassModificationXConicOverlapGeometry
public import FLT.Mazur.WeierstrassModificationXConicParameterSections

/-!
# Full conic parameter intersections inside the coefficient equation gluing

The initial and retained conics constructed in the coefficient model are
monomorphic. This common construction keeps their full parameter opens and
actual scheme intersections, including the original reciprocal transition.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {S : Type u} [CommRing S] (a c : S) (ha : IsUnit a)
  {X : Scheme.{u}} (f : Spec (.of (ConicCoordinate a c)) ⟶ X)

/-- The full first rational parameter of an actual coefficient-model conic. -/
def coefficientConicFirstParameter :=
  (conicFirstParameterIso a c ha).inv ≫ conicFirstOpenImmersion a c ≫ f

/-- The full opposite parameter, retaining its original tangent ordering. -/
def coefficientConicSecondParameter :=
  (conicSecondParameterIso a c ha).inv ≫ conicSecondOpenImmersion a c ≫ f

/-- Both entire parameter opens cover the entire embedded conic. -/
theorem coefficientConicParameters_cover :
    Set.range (coefficientConicFirstParameter a c ha f) ∪
      Set.range (coefficientConicSecondParameter a c ha f) = Set.range f := by
  ext z
  constructor
  · rintro (⟨p, rfl⟩ | ⟨p, rfl⟩)
    · exact ⟨conicFirstOpenImmersion a c ((conicFirstParameterIso a c ha).inv p), rfl⟩
    · exact ⟨conicSecondOpenImmersion a c ((conicSecondParameterIso a c ha).inv p), rfl⟩
  · rintro ⟨p, rfl⟩
    rcases conicOpenImmersions_cover a c ha p with ⟨t, rfl⟩ | ⟨t, rfl⟩
    · obtain ⟨s, rfl⟩ := (conicFirstParameterIso a c ha).inv.homeomorph.surjective t
      exact Or.inl ⟨s, rfl⟩
    · obtain ⟨s, rfl⟩ := (conicSecondParameterIso a c ha).inv.homeomorph.surjective t
      exact Or.inr ⟨s, rfl⟩

variable [Mono f]
local notation "p₁" => coefficientConicFirstParameter a c ha f
local notation "p₂" => coefficientConicSecondParameter a c ha f
local notation "l" => conicOverlapFirstParameterMap a c ha
local notation "r" => conicOverlapSecondParameterMap a c ha

/-- The original double localization is the full intersection inside the equation gluing. -/
theorem coefficientConicParameters_isPullback : IsPullback l r p₁ p₂ := by
  have h := conicParameterOverlap_isPullback a c ha
  exact IsPullback.of_isLimit (PullbackCone.isLimitOfCompMono _ _ f h.cone h.isLimit)

/-- The full actual parameter intersection has the explicit double-localization algebra. -/
def coefficientConicParameterOverlapIso :
    Spec (.of (ConicParameterOverlap a c)) ≅ pullback p₁ p₂ :=
  (coefficientConicParameters_isPullback a c ha f).isoPullback

/-- The intersection identification retains the entire first parameter projection. -/
@[reassoc] theorem coefficientConicParameterOverlapIso_first :
    (coefficientConicParameterOverlapIso a c ha f).hom ≫ pullback.fst p₁ p₂ = l :=
  (coefficientConicParameters_isPullback a c ha f).isoPullback_hom_fst

/-- The intersection identification retains the entire opposite parameter projection. -/
@[reassoc] theorem coefficientConicParameterOverlapIso_second :
    (coefficientConicParameterOverlapIso a c ha f).hom ≫ pullback.snd p₁ p₂ = r :=
  (coefficientConicParameters_isPullback a c ha f).isoPullback_hom_snd

/-- Both original parameter restrictions give exactly the same whole-model morphism. -/
@[reassoc] theorem coefficientConicParameterOverlap_agreement : l ≫ p₁ = r ≫ p₂ :=
  (coefficientConicParameters_isPullback a c ha f).w

end FLT.Mazur.WeierstrassDividedDepth
