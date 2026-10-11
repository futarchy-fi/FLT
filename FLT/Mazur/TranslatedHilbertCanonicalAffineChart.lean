/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.TranslatedHilbertAffineRestriction

/-!
# The canonical invariant affine comparison is an isomorphism on affine charts

The affine comparison was previously constructed without an isomorphism claim.
On the actual affine refinements it is now an isomorphism, with target the
spectrum of the original invariant ring. Thus the chart ring is intrinsic to
the quotient rather than a replacement parameter ring.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
namespace FLT.Mazur.HilbertChart
open CartierAbel SchemePicard FCurve RelativeRelationOrbit
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R]
  {X : Scheme} (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (i : TranslatedHilbertIndex f)

/-- The canonical global-section map is invertible on an actual affine quotient chart. -/
theorem translatedAffineOrbitOpen_toΓSpec_isIso
    (W : (acyclicHilbertTest f i.1).left.Opens) (hW : IsAffineOpen W) :
    IsIso (invariantOpenSpace (smoothHilbertEquivalenceRelation f hL)
      ((translatedChartOrbitOpens f hL i).obj W)).toΓSpec := by
  let _ : IsAffine W.toScheme := hW
  change IsIso (identityToΓSpec.app _)
  rw [NatTrans.isIso_app_iff_of_iso identityToΓSpec
    (translatedParameterOpenLocallyRingedIso f hL i W)]
  exact inferInstanceAs (IsIso W.toScheme.toSpecΓ.toLRSHom)

/-- The original invariant-ring comparison is an isomorphism on every affine refinement. -/
theorem translatedAffineComparison_isIso
    (W : (acyclicHilbertTest f i.1).left.Opens) (hW : IsAffineOpen W) :
    IsIso (invariantAffineComparison (smoothHilbertEquivalenceRelation f hL)
      ((translatedChartOrbitOpens f hL i).obj W)) := by
  let _ := translatedAffineOrbitOpen_toΓSpec_isIso f hL i W hW
  unfold invariantAffineComparison
  have : IsIso (Spec.locallyRingedSpaceMap
      (invariantOpenSectionsIso (smoothHilbertEquivalenceRelation f hL)
        ((translatedChartOrbitOpens f hL i).obj W)).inv) :=
    inferInstanceAs (IsIso (Spec.toLocallyRingedSpace.map
      (invariantOpenSectionsIso (smoothHilbertEquivalenceRelation f hL)
        ((translatedChartOrbitOpens f hL i).obj W)).inv.op))
  infer_instance

/-- The quotient refinement is canonically the spectrum of its actual invariant functions. -/
def translatedInvariantAffineIso
    (W : (acyclicHilbertTest f i.1).left.Opens) (hW : IsAffineOpen W) :
    invariantOpenSpace (smoothHilbertEquivalenceRelation f hL)
      ((translatedChartOrbitOpens f hL i).obj W) ≅
      (invariantAffineTarget (smoothHilbertEquivalenceRelation f hL)
        ((translatedChartOrbitOpens f hL i).obj W)).toLocallyRingedSpace := by
  let _ := translatedAffineComparison_isIso f hL i W hW
  exact asIso (invariantAffineComparison (smoothHilbertEquivalenceRelation f hL)
    ((translatedChartOrbitOpens f hL i).obj W))

/-- The intrinsic affine isomorphism retains the previously constructed comparison map. -/
theorem translatedInvariantAffineIso_hom
    (W : (acyclicHilbertTest f i.1).left.Opens) (hW : IsAffineOpen W) :
    (translatedInvariantAffineIso f hL i W hW).hom =
      invariantAffineComparison (smoothHilbertEquivalenceRelation f hL)
        ((translatedChartOrbitOpens f hL i).obj W) := rfl

end FLT.Mazur.HilbertChart
