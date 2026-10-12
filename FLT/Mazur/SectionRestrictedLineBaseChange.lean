/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SectionPointPowerBaseChange

/-!
# The point-divisor line restricted to its marking under base change

The comparison is over the actual base and uses the original cartesian square.
In particular a frame on a base open becomes a frame of the new section's line,
which is the input required by the relative Weierstrass construction.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {P X T S : Scheme} {p : P ⟶ X} {q : P ⟶ T} {f : X ⟶ S} {g : T ⟶ S}
  [IsSeparated f] (h : IsPullback p q f g)
  (s : S ⟶ X) (t : T ⟶ P) (hs : s ≫ f = 𝟙 _) (ht : t ≫ q = 𝟙 _)
  (hst : t ≫ p = g ≫ s) (hI : EffectiveCartier s.ker) (hJ : EffectiveCartier t.ker)

/-- Pullback on the base agrees with restricting the new point line to its actual marking. -/
def sectionRestrictedLineBaseChangeIso :
    (pullback g).obj ((pullback s).obj (divisorLineBundle s.ker hI)) ≅
      (pullback t).obj (divisorLineBundle t.ker hJ) :=
  (pullbackComp g s).app _ ≪≫ (pullbackCongr hst.symm).app _ ≪≫
    ((pullbackComp t p).app _).symm ≪≫
    (pullback t).mapIso (sectionPointLineIso h s t hs ht hst hI hJ)

/-- A frame on an open base induces a frame of the original section after that restriction. -/
def sectionRestrictedLineOpenFrame [IsOpenImmersion g]
    (e : ((pullback s).obj (divisorLineBundle s.ker hI)).restrict g ≅
      structureModule T) :
    (pullback t).obj (divisorLineBundle t.ker hJ) ≅ structureModule T :=
  (sectionRestrictedLineBaseChangeIso h s t hs ht hst hI hJ).symm ≪≫
    ((restrictFunctorIsoPullback g).app _).symm ≪≫ e

/-- A global frame remains a frame after arbitrary base change. -/
def sectionRestrictedLinePullbackFrame
    (e : (pullback s).obj (divisorLineBundle s.ker hI) ≅ structureModule S) :
    (pullback t).obj (divisorLineBundle t.ker hJ) ≅ structureModule T :=
  (sectionRestrictedLineBaseChangeIso h s t hs ht hst hI hJ).symm ≪≫
    (pullback g).mapIso e ≪≫ modulePullbackUnitIso g

end FLT.Mazur.FCurve
