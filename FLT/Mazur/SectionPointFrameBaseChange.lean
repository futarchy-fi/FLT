/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SectionPoleBaseChangeFrames
public import FLT.Mazur.SectionPoleMultiplicativeCoordinates

/-!
# Transfer the underlying point-line frame before taking powers

The original cartesian line comparison transfers a single frame of the divisor
line along its section. Taking powers afterwards gives multiplicative leading
coordinates on the actual changed family.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.FCurve
open ModuleLineBundleTensorPullback
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] divisorLineBundle

variable {P X T S : Scheme} {p : P ⟶ X} {q : P ⟶ T} {f : X ⟶ S} {g : T ⟶ S}
  [IsSeparated f] (h : IsPullback p q f g)
  (s : S ⟶ X) (t : T ⟶ P) (hs : s ≫ f = 𝟙 _) (ht : t ≫ q = 𝟙 _)
  (hst : t ≫ p = g ≫ s) (hI : EffectiveCartier s.ker) (hJ : EffectiveCartier t.ker)

/-- The original restricted divisor line pulls back to the actual new restricted line. -/
def sectionPointFrameBaseChangeIso :
    (pullback g).obj ((pullback s).obj (divisorLineBundle s.ker hI)) ≅
      (pullback t).obj (divisorLineBundle t.ker hJ) :=
  (pullbackComp g s).app _ ≪≫ (pullbackCongr hst.symm).app _ ≪≫
    ((pullbackComp t p).app _).symm ≪≫
      (pullback t).mapIso (sectionPointLineIso h s t hs ht hst hI hJ)

/-- Transfer one original frame; tensor powers of this frame multiply coordinates. -/
def sectionPointChangedLineFrame
    (e : (pullback g).obj ((pullback s).obj (divisorLineBundle s.ker hI)) ≅
      structureModule T) :
    (pullback t).obj (divisorLineBundle t.ker hJ) ≅ structureModule T :=
  (sectionPointFrameBaseChangeIso h s t hs ht hst hI hJ).symm ≪≫ e

/-- The transferred single frame defines multiplicative coordinates in every degree. -/
theorem sectionPointChangedLineFrame_coefficient_mul
    (e : (pullback g).obj ((pullback s).obj (divisorLineBundle s.ker hI)) ≅
      structureModule T) (m n : ℕ)
    (x : Γ(tensorPower (divisorLineBundle t.ker hJ) m, ⊤))
    (y : Γ(tensorPower (divisorLineBundle t.ker hJ) n, ⊤)) :
    sectionPoleCoefficient t hJ (sectionPointChangedLineFrame h s t hs ht hst hI hJ e) (m + n)
      (SectionGradedMultiplication.mul _ ⊤ m n x y) =
        sectionPoleCoefficient t hJ (sectionPointChangedLineFrame h s t hs ht hst hI hJ e) m x *
          sectionPoleCoefficient t hJ
            (sectionPointChangedLineFrame h s t hs ht hst hI hJ e) n y :=
  sectionPoleCoefficient_mul t hJ _ m n x y

end FLT.Mazur.FCurve
