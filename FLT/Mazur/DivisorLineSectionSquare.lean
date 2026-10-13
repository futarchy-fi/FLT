/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DivisorLineSectionComposition

/-!
# Commuting squares of actual marked lines

A square of scheme morphisms and section-preserving divisor-line comparisons
commutes on the lines themselves. The formula includes both pullback compositors
and the transport along the original equality of scheme morphisms.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {X Y Z T : Scheme}

/-- The precise pullback coherence equation for a square of line comparisons. -/
def LinePullbackSquare (f : X ⟶ Y) (g : Y ⟶ T) (r : X ⟶ Z) (s : Z ⟶ T)
    (w : f ≫ g = r ≫ s) {A : T.Modules} {B : Y.Modules} {C : Z.Modules} {D : X.Modules}
    (eg : (pullback g).obj A ≅ B) (ef : (pullback f).obj B ≅ D)
    (es : (pullback s).obj A ≅ C) (er : (pullback r).obj C ≅ D) : Prop :=
  (pullbackComp f g).symm.app A ≪≫ (pullback f).mapIso eg ≪≫ ef =
    (pullbackCongr w).app A ≪≫ (pullbackComp r s).symm.app A ≪≫
      (pullback r).mapIso es ≪≫ er

/-- Actual section-preserving Cartier-line comparisons satisfy square coherence. -/
theorem divisorLineSectionCompatible_square
    (f : X ⟶ Y) (g : Y ⟶ T) (r : X ⟶ Z) (s : Z ⟶ T) (w : f ≫ g = r ≫ s)
    {I : T.IdealSheafData} {J : Y.IdealSheafData} {K : Z.IdealSheafData}
    {N : X.IdealSheafData} {hI : EffectiveCartier I} {hJ : EffectiveCartier J}
    {hK : EffectiveCartier K} {hN : EffectiveCartier N}
    {eg : (pullback g).obj (divisorLineBundle I hI) ≅ divisorLineBundle J hJ}
    {ef : (pullback f).obj (divisorLineBundle J hJ) ≅ divisorLineBundle N hN}
    {es : (pullback s).obj (divisorLineBundle I hI) ≅ divisorLineBundle K hK}
    {er : (pullback r).obj (divisorLineBundle K hK) ≅ divisorLineBundle N hN}
    (hg : DivisorLineSectionCompatible g hI hJ eg)
    (hf : DivisorLineSectionCompatible f hJ hN ef)
    (hs : DivisorLineSectionCompatible s hI hK es)
    (hr : DivisorLineSectionCompatible r hK hN er) :
    LinePullbackSquare f g r s w eg ef es er := by
  exact (hg.comp hf).ext ((hs.comp hr).congr w)

/-- Extract the equality of actual sheaf isomorphisms from square coherence. -/
theorem LinePullbackSquare.eq
    {f : X ⟶ Y} {g : Y ⟶ T} {r : X ⟶ Z} {s : Z ⟶ T} {w : f ≫ g = r ≫ s}
    {A : T.Modules} {B : Y.Modules} {C : Z.Modules} {D : X.Modules}
    {eg : (pullback g).obj A ≅ B} {ef : (pullback f).obj B ≅ D}
    {es : (pullback s).obj A ≅ C} {er : (pullback r).obj C ≅ D}
    (he : LinePullbackSquare f g r s w eg ef es er) :
    (pullbackComp f g).symm.app A ≪≫ (pullback f).mapIso eg ≪≫ ef =
      (pullbackCongr w).app A ≪≫ (pullbackComp r s).symm.app A ≪≫
        (pullback r).mapIso es ≪≫ er := he

end FLT.Mazur.FCurve
