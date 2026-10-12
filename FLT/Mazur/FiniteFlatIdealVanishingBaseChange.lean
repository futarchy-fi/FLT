/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteFlatIdealVanishingRestriction
public import FLT.Mazur.AffineCartesianPreimageSections
public import FLT.Mazur.AffinePullbackIdeal

/-!
# Geometric base change of finite flat coefficient ideals

On any compatible affine charts of a cartesian family, the coefficient ideal
of the actual pulled family ideal is the pullback of the original coefficient
ideal. No flatness of the base-change map is needed.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.FiniteFlatIdealVanishing
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {D E S T : Scheme} {g : D ⟶ S} {q : E ⟶ T} {i : E ⟶ D} {f : T ⟶ S}
  [IsFinite g] [Flat g] [LocallyOfFinitePresentation g]
  [IsFinite q] [Flat q] [LocallyOfFinitePresentation q]
  (H : IsPullback i q g f) (J : D.IdealSheafData)

include H

/-- Actual family ideal pullback commutes with coefficient equations on compatible charts. -/
theorem coefficientIdeal_baseChange (V : S.affineOpens) (U : T.affineOpens)
    (h : U.1 ≤ f ⁻¹ᵁ V.1) :
    coefficientIdeal q (J.comap i) U =
      (coefficientIdeal g J V).map (f.appLE V.1 U.1 h).hom := by
  have hc := ProjectiveIdealVanishing.ideal_ringPushout
    (f.appLE V.1 U.1 h).hom (g.app V.1).hom (q.app U.1).hom
    (i.appLE (g ⁻¹ᵁ V.1) (q ⁻¹ᵁ U.1) (AffineCartesianPreimage.preimage_le H V U h)).hom
    (AffineCartesianPreimage.sections_isPushout H V U h).flip
    (FCurve.finiteFlat_app_projective g V) (FCurve.finiteFlat_app_projective q U)
    (J.ideal ⟨g ⁻¹ᵁ V.1, V.2.preimage g⟩)
  dsimp only at hc
  erw [← Scheme.IdealSheafData.ideal_comap J i
    ⟨g ⁻¹ᵁ V.1, V.2.preimage g⟩ ⟨q ⁻¹ᵁ U.1, U.2.preimage q⟩
    (AffineCartesianPreimage.preimage_le H V U h)] at hc
  exact hc

/-- The two geometric coefficient sheaves agree on every compatible affine chart. -/
theorem idealSheaf_baseChange_ideal (V : S.affineOpens) (U : T.affineOpens)
    (h : U.1 ≤ f ⁻¹ᵁ V.1) :
    (idealSheaf q (J.comap i)).ideal U = ((idealSheaf g J).comap f).ideal U := by
  rw [Scheme.IdealSheafData.ideal_comap _ f V U h]
  exact coefficientIdeal_baseChange H J V U h

end FLT.Mazur.FiniteFlatIdealVanishing
