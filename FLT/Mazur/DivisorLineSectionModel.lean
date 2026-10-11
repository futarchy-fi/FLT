/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DivisorLinePullback

/-!
# Opaque divisor lines with their canonical sections

The model retains the actual divisor line, section and pullback comparison via
specified isomorphisms, while keeping dual sheaf implementations opaque.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Scheme.Modules

namespace FLT.Mazur.FCurve

universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {X Y : Scheme.{u}} {I : Y.IdealSheafData} {J : X.IdealSheafData}

/-- An opaque copy of the actual positive divisor line. -/
irreducible_def divisorLineModel (I : Y.IdealSheafData) (hI : EffectiveCartier I) :
    Y.Modules := divisorLineBundle I hI

/-- The specified identification with the original positive divisor line. -/
def divisorLineModelIso (hI : EffectiveCartier I) :
    divisorLineModel I hI ≅ divisorLineBundle I hI := eqToIso (divisorLineModel_def I hI)

/-- The actual canonical divisor section transported to the opaque model. -/
def divisorLineModelSection (hI : EffectiveCartier I) :
    structureModule Y ⟶ divisorLineModel I hI :=
  divisorSectionMap hI ≫ (divisorLineModelIso hI).inv

/-- The original divisor comparison transported to opaque line objects. -/
def divisorLineModelPullbackIso (f : X ⟶ Y) (hI : EffectiveCartier I)
    (hJ : EffectiveCartier J) (h : I.comap f = J)
    [IsIso (idealModulePullbackHom I f)] :
    (pullback f).obj (divisorLineModel I hI) ≅ divisorLineModel J hJ :=
  (pullback f).mapIso (divisorLineModelIso hI) ≪≫
    divisorLinePullbackIsoOfEq f hI hJ h ≪≫ (divisorLineModelIso hJ).symm

/-- The transported canonical comparison preserves the transported actual section. -/
@[reassoc] theorem divisorLineModelPullbackIso_section (f : X ⟶ Y)
    (hI : EffectiveCartier I) (hJ : EffectiveCartier J) (h : I.comap f = J)
    [IsIso (idealModulePullbackHom I f)] :
    (pullback f).map (divisorLineModelSection hI) ≫
        (divisorLineModelPullbackIso f hI hJ h).hom =
      (modulePullbackUnitIso f).hom ≫ divisorLineModelSection hJ := by
  simp only [divisorLineModelSection, divisorLineModelPullbackIso, Iso.trans_hom,
    Functor.mapIso_hom, Iso.symm_hom, Functor.map_comp, Category.assoc,
    Iso.map_inv_hom_id_assoc]
  rw [divisorLinePullbackIsoOfEq_section_assoc]

end FLT.Mazur.FCurve
