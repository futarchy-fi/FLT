/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OrderedHilbertQuotientTestPullback
public import FLT.Mazur.SmoothHilbertSourceRepresentable

/-!
# An actual common fppf cover of the old and new Picard presentations

The full original test intersection against the old smooth source maps
surjectively to both sources: etale to the old source and smooth to the exact
quotient-defined new source. These are constructed scheme morphisms, ready
for comparison descent into arbitrary locally ringed targets.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.OrderedHilbertPresentationComparison
open HilbertChart CartierAbel SchemePicard FCurve
open OrderedHilbertIdentityQuotientOriginalSection
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
local notation "T" => smoothHilbertSource f
local notation "s" => smoothHilbertSourceSection f hL

/-- The entire mixed old/new intersection over the original Picard sheaf. -/
def common : Over (Spec (.of R)) :=
  OrderedHilbertOriginalTestIntersection.relation f hL T s

/-- The comparison to the exact new scheme source with its quotient-defined coefficient map. -/
def toNew : common f hL ⟶ quotientTest f hL :=
  OrderedHilbertOriginalTestIntersection.quotientFst f hL T s

/-- The comparison to the entire original smooth source. -/
def toOld : common f hL ⟶ T :=
  OrderedHilbertOriginalTestIntersection.snd f hL T s

/-- The common scheme is the full original Picard pullback of the two presentations. -/
theorem isPullback :
    IsPullback (uliftYoneda.{1}.map (toNew f hL)) (uliftYoneda.{1}.map (toOld f hL))
      (quotientMap f hL) (smoothHilbertSourceMap f hL) :=
  OrderedHilbertOriginalTestIntersection.quotient_isPullback f hL T s

instance toOld_etale : Etale (toOld f hL).left :=
  OrderedHilbertOriginalTestIntersection.snd_etale f hL T s

instance toOld_surjective : Surjective (toOld f hL).left :=
  OrderedHilbertOriginalTestIntersection.snd_surjective f hL T s

/-- The other projection is a genuine smooth surjection, on the exact new relative source. -/
theorem toNew_smooth_surjective : Smooth (toNew f hL).left ∧ Surjective (toNew f hL).left :=
  smoothHilbertSourceMap_pullback_smooth_surjective f hL _ _ _ (isPullback f hL).flip

instance toNew_smooth : Smooth (toNew f hL).left := (toNew_smooth_surjective f hL).1

instance toNew_surjective : Surjective (toNew f hL).left := (toNew_smooth_surjective f hL).2

/-- The comparison to the old source is a single actual relative fppf cover. -/
theorem toOld_covering : Sieve.ofArrows (fun _ : Unit ↦ common f hL)
    (fun _ ↦ toOld f hL) ∈ (Scheme.fppfTopology.over (Spec (.of R))) T :=
  RelativeFppfRepresentedCover.covering (toOld f hL)

/-- The comparison to the new source is also a single actual relative fppf cover. -/
theorem toNew_covering : Sieve.ofArrows (fun _ : Unit ↦ common f hL)
    (fun _ ↦ toNew f hL) ∈
      (Scheme.fppfTopology.over (Spec (.of R))) (quotientTest f hL) :=
  RelativeFppfRepresentedCover.covering (toNew f hL)

end FLT.Mazur.OrderedHilbertPresentationComparison
