/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SectionPointPowerBaseChange
public import FLT.Mazur.TensorPowerPullbackSquare

/-!
# Section compatibility of cartesian marking comparisons

These formulas keep the total spaces abstract, so geometric specializations
can use the section and power laws without expanding sheaf constructions.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.FCurve
open ModuleLineBundleTensorPullback
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] divisorLineBundle ModuleSheafTensor.tensor
  Scheme.Modules.pullback sectionPointLineIso
variable {P X T S : Scheme} {p : P ⟶ X} {q : P ⟶ T} {f : X ⟶ S} {g : T ⟶ S}
  [IsSeparated f] (h : IsPullback p q f g)
  (s : S ⟶ X) (t : T ⟶ P) (hs : s ≫ f = 𝟙 _) (ht : t ≫ q = 𝟙 _)
  (hst : t ≫ p = g ≫ s) (hI : EffectiveCartier s.ker) (hJ : EffectiveCartier t.ker)

/-- The cartesian section-line comparison preserves the canonical section. -/
theorem sectionPointLineIso_compatible :
    DivisorLineSectionCompatible p hI hJ (sectionPointLineIso h s t hs ht hst hI hJ) :=
  sectionPointLineIso_section h s t hs ht hst hI hJ

/-- The cartesian pole comparison is the canonical tensor power of the line comparison. -/
theorem sectionPointPowerIso_eq (m : ℕ) :
    sectionPointPowerIso h s t hs ht hst hI hJ m =
      tensorPowerPullbackComparison p (sectionPointLineIso h s t hs ht hst hI hJ) m := rfl

end FLT.Mazur.FCurve
