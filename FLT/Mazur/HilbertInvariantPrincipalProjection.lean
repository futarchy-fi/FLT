/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertInvariantPrincipalEffectiveness

/-!
# Original quotient points in admissible invariant principal charts

The constructed principal quotient chart contains the image of every source
point where its admissible coefficient is nonzero. The map is to the original
unrestricted invariant quotient, with its original projection.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve SchemeEffectiveEpiSections RelativeRelationOrbit
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [IsAffine V.left] [Etale V.hom] [Surjective V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} [IsAffine A.left] (k : A ⟶ variableHilbertTest f d V)
  [IsOpenImmersion k.left]
  (r : compatibleFunctions (fst f hL d V c k).left (snd f hL d V c k).left)
  (hr : r ∈ invariantEnvelopeDenominators f hL d V c k)
local notation "k'" => invariantPrincipalChart f hL d V c k r
local notation "e" => variableChartEquivalenceRelation f hL d V c

/-- The actual affine quotient projection for this admissible principal source. -/
def invariantPrincipalQuotientProjection :
    (invariantPrincipalSource f hL d V c k r).left ⟶
      invariantPrincipalQuotientScheme f hL d V c k r hr :=
  let _ := invariantPrincipal_toEnvelope_isIso f hL d V c k r hr
  fullEnvelopeProjection f hL d V c k'

/-- The principal chart preserves the ORIGINAL unrestricted quotient projection. -/
theorem invariantPrincipalOpenChart_projection
    (x : (invariantPrincipalSource f hL d V c k r).left) :
    (invariantPrincipalOpenChart f hL d V c k r hr).base
      (invariantPrincipalQuotientProjection f hL d V c k r hr x) =
        projection e (k.left x.val) := by
  let _ := invariantPrincipal_toEnvelope_isIso f hL d V c k r hr
  change (fullEnvelopeOpenChart f hL d V c k').base
    (fullEnvelopeProjection f hL d V c k' x) = _
  rw [fullEnvelopeOpenChart_projection]
  unfold invariantPrincipalChart invariantPrincipalSourceMap
  rfl

/-- An actual nonvanishing point lies in the constructed affine open chart image. -/
theorem invariantPrincipalOpenChart_contains (x : A.left) (hx : x ∈ A.left.basicOpen r.val) :
    projection e (k.left x) ∈
      Set.range (invariantPrincipalOpenChart f hL d V c k r hr).base :=
  ⟨invariantPrincipalQuotientProjection f hL d V c k r hr ⟨x, hx⟩,
    invariantPrincipalOpenChart_projection f hL d V c k r hr ⟨x, hx⟩⟩

end FLT.Mazur.HilbertChart.AffineRestriction
