/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AmpleAffineBase
public import FLT.Mazur.ProperAmpleConverse

/-!
# Arbitrary base change from an affine base

The new base need not be affine. On each of its affine opens the projection to
the original source is affine, so actual pulled-back sections give ampleness.
For proper morphisms this supplies closed power presentations on every affine
open of the new base.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.FCurve
variable {X Y S T : Scheme} {f : X ⟶ S} {g : T ⟶ S}
  {p : Y ⟶ X} {q : Y ⟶ T} {L : X.Modules}

/-- Section ampleness survives every cartesian square with affine original base. -/
theorem RelativelyAmpleLineBundle.of_isPullback_affineBase [IsAffine S]
    (hL : RelativelyAmpleLineBundle f L) (sq : IsPullback p q f g) :
    RelativelyAmpleLineBundle q ((Scheme.Modules.pullback p).obj L) := by
  have : QuasiCompact q := MorphismProperty.of_isPullback sq hL.1
  refine ⟨inferInstance, hL.2.1.pullback p, fun U hU ↦ ?_⟩
  let : IsAffine U.toScheme := hU
  have hs := (isPullback_morphismRestrict q U).flip.paste_horiz sq
  have : IsAffineHom ((q ⁻¹ᵁ U).ι ≫ p) :=
    MorphismProperty.of_isPullback hs.flip (inferInstance : IsAffineHom (U.ι ≫ g))
  exact (hL.ample_of_affine.pullback_affine ((q ⁻¹ᵁ U).ι ≫ p)).of_iso
    ((restrictFunctorIsoPullback (q ⁻¹ᵁ U).ι).app _ ≪≫
      (pullbackComp (q ⁻¹ᵁ U).ι p).app L)

/-- Arbitrary base change from an affine base preserves relative section ampleness. -/
theorem RelativelyAmpleLineBundle.baseChange_affineBase [IsAffine S]
    (hL : RelativelyAmpleLineBundle f L) (g : T ⟶ S) :
    RelativelyAmpleLineBundle (pullback.snd f g)
      ((Scheme.Modules.pullback (pullback.fst f g)).obj L) :=
  hL.of_isPullback_affineBase (IsPullback.of_hasPullback f g)

/-- Closed power presentations transport through every cartesian square from an affine base. -/
theorem RelativeAmple.of_isPullback_affineBase [IsAffine S]
    (hL : RelativeAmple f L) (hline : LocallyFreeRankOne L)
    (sq : IsPullback p q f g) : RelativeAmple q ((Scheme.Modules.pullback p).obj L) := by
  have : IsProper q := MorphismProperty.of_isPullback sq hL.isProper
  exact ((hL.relativelyAmpleLineBundle hline).of_isPullback_affineBase sq).relativeAmple

/-- Every affine open of an arbitrary new base has a closed power presentation. -/
theorem RelativeAmple.baseChange_affineBase [IsAffine S]
    (hL : RelativeAmple f L) (hline : LocallyFreeRankOne L) (g : T ⟶ S) :
    RelativeAmple (pullback.snd f g)
      ((Scheme.Modules.pullback (pullback.fst f g)).obj L) :=
  hL.of_isPullback_affineBase hline (IsPullback.of_hasPullback f g)

end FLT.Mazur.FCurve
