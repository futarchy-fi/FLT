/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.UniversalWeierstrassAuxiliarySchemeNormalizationNaturality
public import FLT.Mazur.UniversalWeierstrassAuxiliaryCubicProjection

/-!
# Actual source maps of the original and normalized universal families

The canonical pullback maps retain the universal projection and the source
morphism. Proper coefficient projections detect equality before any group laws
are unfolded.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.UniversalWeierstrass
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {T U : Scheme} (f : T ⟶ levelFour.left) (k : U ⟶ T)

/-- The full original family map induced by an arbitrary source morphism. -/
def auxiliarySchemeOriginalSourceMap :
    (auxiliarySchemeGroup (k ≫ f)).X.left ⟶ (auxiliarySchemeGroup f).X.left :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ k) (by
    exact pullback.condition.trans
      ((congrArg (fun z ↦ pullback.snd universalGroup.hom ((k ≫ f) ≫ levelFour.hom) ≫ z)
        (Category.assoc k f levelFour.hom)).trans (Category.assoc _ _ _).symm))

/-- The full normalized family map retains the actual normalized coefficient bases. -/
def auxiliarySchemeNormalizedSourceMap :
    (auxiliarySchemeGroup (auxiliarySchemeNormalizedPoint (k ≫ f))).X.left ⟶
      (auxiliarySchemeGroup (auxiliarySchemeNormalizedPoint f)).X.left :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ k) (by
    exact pullback.condition.trans
      ((congrArg (fun z ↦ pullback.snd universalGroup.hom
        (auxiliarySchemeNormalizedPoint (k ≫ f) ≫ levelFour.hom) ≫ z)
        ((auxiliarySchemeNormalizedPoint_natural_base f k).trans
          (Category.assoc _ _ _))).trans (Category.assoc _ _ _).symm))

/-- Original source change retains the universal-family projection. -/
@[reassoc] theorem auxiliarySchemeOriginalSourceMap_fst :
    auxiliarySchemeOriginalSourceMap f k ≫ pullback.fst universalGroup.hom (f ≫ levelFour.hom) =
      pullback.fst universalGroup.hom ((k ≫ f) ≫ levelFour.hom) :=
  pullback.lift_fst _ _ _

/-- Original source change retains the source morphism itself. -/
@[reassoc] theorem auxiliarySchemeOriginalSourceMap_snd :
    auxiliarySchemeOriginalSourceMap f k ≫ (auxiliarySchemeGroup f).X.hom =
      (auxiliarySchemeGroup (k ≫ f)).X.hom ≫ k := pullback.lift_snd _ _ _

/-- Normalized source change retains the universal-family projection. -/
@[reassoc] theorem auxiliarySchemeNormalizedSourceMap_fst :
    auxiliarySchemeNormalizedSourceMap f k ≫
        pullback.fst universalGroup.hom (auxiliarySchemeNormalizedPoint f ≫ levelFour.hom) =
      pullback.fst universalGroup.hom (auxiliarySchemeNormalizedPoint (k ≫ f) ≫ levelFour.hom) :=
  pullback.lift_fst _ _ _

/-- Normalized source change retains the same source morphism. -/
@[reassoc] theorem auxiliarySchemeNormalizedSourceMap_snd :
    auxiliarySchemeNormalizedSourceMap f k ≫
        (auxiliarySchemeGroup (auxiliarySchemeNormalizedPoint f)).X.hom =
      (auxiliarySchemeGroup (auxiliarySchemeNormalizedPoint (k ≫ f))).X.hom ≫ k :=
  pullback.lift_snd _ _ _

/-- The actual proper coefficient projection and structure jointly detect morphisms. -/
theorem properCoefficientMap_hom_ext {R S : Type} [CommRing R] [CommRing S]
    (W : WeierstrassCurve R) (V : WeierstrassCurve S) (g : R →+* S) (he : V = W.map g)
    {X : Scheme} (a b : X ⟶ integralCurve V)
    (hc : a ≫ properCoefficientMap W V g he = b ≫ properCoefficientMap W V g he)
    (hs : a ≫ integralCurveStructure V = b ≫ integralCurveStructure V) : a = b := by
  subst V
  let _ : Algebra R S := g.toAlgebra
  change a ≫ (𝟙 _ ≫ integralCoefficientMorphism W) =
    b ≫ (𝟙 _ ≫ integralCoefficientMorphism W) at hc
  rw [Category.id_comp] at hc
  exact (integralCoefficient_isPullback W).hom_ext hc hs

end FLT.Mazur.UniversalWeierstrass
