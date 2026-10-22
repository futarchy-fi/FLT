/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SectionPoleBaseChangeFrames
public import FLT.Mazur.SectionPoleLeadingRestriction
public import FLT.Mazur.ModuleSectionSquareTransport

/-!
# Actual pole sections and leading terms under base change

Transport uses the original cartesian point-power comparison and the
adjunction unit. Restricting the transported section to the new marking
agrees with transporting its original leading section, without flatness.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.FCurve
open ModuleLineBundleTensorPullback
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] divisorLineBundle ModuleSheafTensor.tensor
  Scheme.Modules.pullback
variable {P X T S : Scheme} {p : P ⟶ X} {q : P ⟶ T} {f : X ⟶ S} {g : T ⟶ S}
  [IsSeparated f] (h : IsPullback p q f g)
  (s : S ⟶ X) (t : T ⟶ P) (hs : s ≫ f = 𝟙 _) (ht : t ≫ q = 𝟙 _)
  (hst : t ≫ p = g ≫ s) (hI : EffectiveCartier s.ker) (hJ : EffectiveCartier t.ker)

/-- Transport the actual global pole section to the retained divisor power. -/
def sectionPointPowerPullGlobal (m : ℕ)
    (x : Γ(tensorPower (divisorLineBundle s.ker hI) m, ⊤)) :
    Γ(tensorPower (divisorLineBundle t.ker hJ) m, ⊤) :=
  (sectionPointPowerIso h s t hs ht hst hI hJ m).hom.app ⊤
    (pullGlobal p _ x)

/-- The original leading-line comparison preserves restriction of actual sections. -/
theorem sectionPoleLineBaseChangeIso_sections (m : ℕ)
    (x : Γ(tensorPower (divisorLineBundle s.ker hI) m, ⊤)) :
    (sectionPoleLineBaseChangeIso h s t hs ht hst hI hJ m).hom.app ⊤
      (pullGlobal g _ (pullGlobal s _ x)) =
        pullGlobal t _ (sectionPointPowerPullGlobal h s t hs ht hst hI hJ m x) := by
  exact sectionSquareTransportIso_sections p t g s hst
    (sectionPointPowerIso h s t hs ht hst hI hJ m) x

variable [IsSeparated q]

/-- Cohomological leading terms commute with actual transport of the pole section. -/
theorem sectionPoleLeading_baseChange (m : ℕ)
    (x : ModuleRingH f.appTop.hom
      (tensorPower (divisorLineBundle s.ker hI) (m + 1)) 0) :
    sectionPoleLeading q t ht hJ m
      ((moduleH0Equiv _).symm
        (sectionPointPowerPullGlobal h s t hs ht hst hI hJ (m + 1)
          (moduleH0Equiv _ x))) =
      (sectionPoleLineBaseChangeIso h s t hs ht hst hI hJ (m + 1)).hom.app ⊤
        (pullGlobal g _ (sectionPoleLeading f s hs hI m x)) := by
  rw [sectionPoleLeading_sections, sectionPoleLeading_sections]
  dsimp only [Functor.id_obj]
  erw [LinearEquiv.apply_symm_apply]
  exact (sectionPoleLineBaseChangeIso_sections h s t hs ht hst hI hJ (m + 1) _).symm

end FLT.Mazur.FCurve
