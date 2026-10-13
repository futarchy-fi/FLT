/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeKernelPairPropertyDescent
public import FLT.Mazur.VariableHilbertRelationGeometry
public import FLT.Mazur.VariableHilbertRefinedSchemeModel

/-!
# The descended original projection is fppf, smooth, or etale

The actual refined fppf model supplies a cover of the target. Its full original
kernel pair, rather than a base-diagonal relation, recovers finite presentation
of the descended projection. Smooth or etale translation bases give the stronger
corresponding property. Existence of the refined model remains a separate step.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.VariableHilbertFppfRefinement
open HilbertChart CartierAbel SchemePicard FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) {V W : Over (Spec (.of R))} (b : W ⟶ V)
  (c : (relativeFppfSheaf f).obj.obj (op V))
  [Flat b.left] [LocallyOfFinitePresentation b.left] [Surjective b.left]
  {Z : Over (Spec (.of R))} (π : variableHilbertTest f d W ⟶ Z)
  (H : IsPullback
    (variableChartRelationFst f hL d W ((relativeFppfSheaf f).obj.map b.op c))
    (variableChartRelationSnd f hL d W ((relativeFppfSheaf f).obj.map b.op c)) π π)
  [Flat π.left] [LocallyOfFinitePresentation π.left] [Surjective π.left]
local notation "g" => baseMarkedChartChange f b d
local notation "D" => descendedProjection f hL d b c π H.w

/-- Properties of the original full relation descend along the supplied refined model. -/
theorem descendedProjection_property (P : MorphismProperty Scheme)
    [P.IsStableUnderBaseChange]
    [P.DescendsAlong (@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation)]
    (hp : P (variableChartRelationFst f hL d V c).left) : P (D).left := by
  have he : g ≫ D = π := descendedProjection_source f hL d b c π H.w
  let _ : Flat (g ≫ D).left := he.symm ▸ inferInstanceAs (Flat π.left)
  let _ : Surjective (g ≫ D).left := he.symm ▸ inferInstanceAs (Surjective π.left)
  let _ : LocallyOfFinitePresentation (g ≫ D).left :=
    he.symm ▸ inferInstanceAs (LocallyOfFinitePresentation π.left)
  exact RelativeKernelPairPropertyDescent.property D
    (descendedProjection_isPullback f hL d b c π H) g P hp

theorem descendedProjection_locallyOfFinitePresentation [LocallyOfFinitePresentation V.hom] :
    LocallyOfFinitePresentation (D).left :=
  descendedProjection_property f hL d b c π H _ inferInstance

theorem descendedProjection_smooth [Smooth V.hom] : Smooth (D).left :=
  descendedProjection_property f hL d b c π H _ inferInstance

theorem descendedProjection_etale [Etale V.hom] : Etale (D).left :=
  descendedProjection_property f hL d b c π H _ inferInstance

/-- The original projection itself now supplies an actual singleton fppf cover. -/
theorem descendedProjection_fppf [LocallyOfFinitePresentation V.hom] :
    Presieve.singleton (D).left ∈ Scheme.fppfPrecoverage Z.left := by
  let _ := descendedProjection_locallyOfFinitePresentation f hL d b c π H
  exact Scheme.Hom.singleton_mem_fppfPrecoverage _

end FLT.Mazur.VariableHilbertFppfRefinement
