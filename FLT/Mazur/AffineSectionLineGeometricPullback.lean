/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineFreeSectionLineBaseChange
public import FLT.Mazur.NormalizedSectionLineSheafBaseChange

/-!
# Geometric pullback of actual affine section-line sheaves

The canonical affine spectrum square transports the proved coefficient
base-change isomorphisms to the original affine schemes. The resulting
line and ambient vector comparisons are actual sheaf isomorphisms.
Their inclusion square and transition naturality remain separate proofs.
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

/-- The canonical affine spectrum square, as an isomorphism of genuine pullback functors. -/
def affineSpectrumPullback :
    pullback Y.isoSpec.hom ⋙ pullback f ≅
      pullback (Spec.map f.appTop) ⋙ pullback X.isoSpec.hom :=
  pullbackComp f Y.isoSpec.hom ≪≫
    pullbackCongr (Scheme.isoSpec_hom_naturality f).symm ≪≫
      (pullbackComp X.isoSpec.hom (Spec.map f.appTop)).symm

variable {ι : Type u}

/-- Actual affine section-line pullback is the sheaf of the extended section submodule. -/
def sectionLineBaseChange (i : ι) (L : Chart Γ(Y, ⊤) ι i) :
    (pullback f).obj (sectionLineSheaf Y i L) ≅
      sectionLineSheaf X i (baseChange f.appTop.hom i L) :=
  (affineSpectrumPullback f).app (sheaf i L) ≪≫
    (pullback X.isoSpec.hom).mapIso (sheafBaseChange f.appTop.hom i L)

/-- The actual ambient affine vector sheaf commutes with geometric pullback. -/
def affineVectorBaseChange [Finite ι] :
    (pullback f).obj ((affineTilde Y).obj (ModuleCat.of Γ(Y, ⊤) (ι → Γ(Y, ⊤)))) ≅
      (affineTilde X).obj (ModuleCat.of Γ(X, ⊤) (ι → Γ(X, ⊤))) :=
  (affineSpectrumPullback f).app (tilde (ModuleCat.of Γ(Y, ⊤) (ι → Γ(Y, ⊤)))) ≪≫
    (pullback X.isoSpec.hom).mapIso (vectorSheafBaseChange ι f.appTop.hom)

end FLT.Mazur.AffineFreeSheafCoordinates
