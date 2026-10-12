/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineEtaleFaithfulCoefficients
public import FLT.Mazur.AmpleAffinePullback
public import FLT.Mazur.OrderedHilbertFaithfulClass

/-!
# The original proper curve over a constructed faithful neighborhood

The curve is the actual base change to the section spectrum of the principal
base open. All proper-family hypotheses and the ample line bundle survive.
The projection retains the original curve, rather than choosing a new family.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.FaithfulNeighborhoodCurve
open AffineEtaleFaithfulNeighborhood FCurve
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] {X V : Scheme}
  (f : X ⟶ Spec (.of R)) (g : V ⟶ Spec (.of R)) [Etale g] (v : V)

/-- The original curve after localization of its coefficient base. -/
abbrev curve := Limits.pullback f (spectrumBase g v)

/-- The localized proper-family structural morphism. -/
abbrev map : curve f g v ⟶ Spec (.of (BaseRing g v)) :=
  Limits.pullback.snd f (spectrumBase g v)

/-- The actual projection to the original curve. -/
abbrev projection : curve f g v ⟶ X := Limits.pullback.fst f (spectrumBase g v)

/-- The coefficient-localization square retains the original curve map. -/
@[reassoc]
theorem projection_base : projection f g v ≫ f = map f g v ≫ spectrumBase g v :=
  Limits.pullback.condition

instance map_proper [IsProper f] : IsProper (map f g v) := inferInstance
instance map_flat [Flat f] : Flat (map f g v) := inferInstance
instance map_integral [GeometricallyIntegral f] : GeometricallyIntegral (map f g v) :=
  inferInstance
instance map_smooth [SmoothOfRelativeDimension 1 f] :
    SmoothOfRelativeDimension 1 (map f g v) :=
  MorphismProperty.pullback_snd _ _ inferInstance

instance projection_open : IsOpenImmersion (projection f g v) := inferInstance
instance projection_affine : IsAffineHom (projection f g v) :=
  MorphismProperty.pullback_fst _ _ inferInstance

/-- The original ample bundle pulls back to an ample bundle on the localized curve. -/
theorem ample {L : X.Modules} (hL : AmpleLineBundle L) :
    AmpleLineBundle ((Scheme.Modules.pullback (projection f g v)).obj L) :=
  hL.pullback_affine (projection f g v)

/-- The localized family is over precisely the original scalar-localization map. -/
theorem scalar_square :
    let _ := originalBaseAlgebra g v
    projection f g v ≫ f = map f g v ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (BaseRing g v))) := by
  let _ := originalBaseAlgebra g v
  dsimp only
  rw [projection_base, spectrumBase_eq_specMap]

end FLT.Mazur.FaithfulNeighborhoodCurve
