/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineSectionLineGeometricPullback

/-!
# Component squares for affine section-line pullback

The coefficient inclusion square and the canonical spectrum square have
bounded separate proofs. Forward-factor identities expose the constructed
line and ambient comparisons. Their full geometric inclusion law remains
a separate proof.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.AffineFreeSheafCoordinates
open AffineModuleGlobalSections NormalizedSectionLine
variable {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (f : X ⟶ Y)
variable {ι : Type u} [Finite ι]

attribute [local irreducible] sheafBaseChange vectorSheafBaseChange
attribute [local irreducible] Scheme.Modules.pullback

omit [IsAffine Y] in
/-- Pullback of the coefficient inclusion square to the original affine source. -/
lemma sectionLineCoefficientSquare (i : ι) (L : Chart Γ(Y, ⊤) ι i) :
    (pullback X.isoSpec.hom).map (sheafBaseChange f.appTop.hom i L).hom ≫
        (pullback X.isoSpec.hom).map (sheafInclusion i (baseChange f.appTop.hom i L)) =
      (pullback X.isoSpec.hom).map
        ((pullback (Spec.map f.appTop)).map (sheafInclusion i L)) ≫
        (pullback X.isoSpec.hom).map (vectorSheafBaseChange ι f.appTop.hom).hom := by
  rw [← Functor.map_comp, sheafBaseChange_inclusion, Functor.map_comp]
  rfl

attribute [local irreducible] affineSpectrumPullback

omit [Finite ι] in
/-- Naturality of the canonical spectrum square on arbitrary module sheaf maps. -/
lemma affineSpectrumPullback_naturality
    {P Q : (Spec Γ(Y, ⊤)).Modules} (a : P ⟶ Q) :
    (affineSpectrumPullback f).hom.app P ≫
        (pullback X.isoSpec.hom).map ((pullback (Spec.map f.appTop)).map a) =
      (pullback f).map ((pullback Y.isoSpec.hom).map a) ≫
        (affineSpectrumPullback f).hom.app Q :=
  ((affineSpectrumPullback f).hom.naturality a).symm

omit [Finite ι] in
/-- Expose only the line comparison's two forward factors. -/
lemma sectionLineBaseChange_hom (i : ι) (L : Chart Γ(Y, ⊤) ι i) :
    (sectionLineBaseChange f i L).hom =
      (affineSpectrumPullback f).hom.app (sheaf i L) ≫
        (pullback X.isoSpec.hom).map (sheafBaseChange f.appTop.hom i L).hom := rfl

/-- Expose only the vector comparison's two forward factors. -/
lemma affineVectorBaseChange_hom :
    (affineVectorBaseChange (ι := ι) f).hom =
      (affineSpectrumPullback f).hom.app
        (tilde (ModuleCat.of Γ(Y, ⊤) (ι → Γ(Y, ⊤)))) ≫
          (pullback X.isoSpec.hom).map (vectorSheafBaseChange ι f.appTop.hom).hom := rfl

omit [IsAffine Y] [Finite ι] in
/-- Affine tilde maps the coefficient inclusion through the spectrum pullback. -/
lemma affineTilde_subtype (i : ι) (L : Chart Γ(X, ⊤) ι i) :
    (affineTilde X).map (ModuleCat.ofHom L.val.subtype) =
      (pullback X.isoSpec.hom).map (sheafInclusion i L) := rfl

end FLT.Mazur.AffineFreeSheafCoordinates
