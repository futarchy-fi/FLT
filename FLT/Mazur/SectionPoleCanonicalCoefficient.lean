/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SectionPoleMultiplicativeCoordinates
public import FLT.Mazur.RelativeGenusOneInitialPoleStep
public import FLT.Mazur.DivisorComplementCanonical

/-!
# Lower-pole and canonical sections vanish along the marking

The leading coefficient is zero on the original pole inclusion. In particular,
every positive canonical divisor power restricts to zero in the marked frame.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.FCurve
open ModuleLineBundleTensorPullback
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] divisorLineBundle sectionPoleMultiplicativeCoordinates
variable {X S : Scheme.{0}} (f : X ⟶ S) [IsSeparated f]
  (s : S ⟶ X) (hs : s ≫ f = 𝟙 S) (hI : EffectiveCartier s.ker)
  (e : (pullback s).obj (divisorLineBundle s.ker hI) ≅ structureModule S)
local notation "L" => divisorLineBundle s.ker hI

include hs in
/-- An actual lower-pole inclusion has zero leading coefficient. -/
theorem sectionPoleCoefficient_step (m : ℕ)
    (x : ModuleRingH f.appTop.hom (tensorPower (L) m) 0) :
    sectionPoleCoefficient s hI e (m + 1)
      (moduleH0Equiv _ (divisorPowerRingStep f.appTop.hom hI m x)) = 0 := by
  rw [sectionPoleCoefficient_leading s hI e f hs]
  rw [(sectionPoleLeading_eq_zero_iff f s hs hI m _).mpr ⟨x, rfl⟩, map_zero]

include f hs in
/-- A positive canonical power restricts to zero along the original marking. -/
theorem sectionPoleCoefficient_canonical (m : ℕ) :
    sectionPoleCoefficient s hI e (m + 1)
      (tensorPowerSection (L) ⊤ (divisorSection hI ⊤) (m + 1)) = 0 := by
  have ht : tensorPowerSection (L) ⊤ (divisorSection hI ⊤) (m + 1) =
      moduleH0Equiv _ (divisorPowerRingStep f.appTop.hom hI m
        ((moduleH0Equiv _).symm (tensorPowerSection (L) ⊤ (divisorSection hI ⊤) m))) := by
    rw [divisorPowerRingStep_sections, LinearEquiv.apply_symm_apply,
      divisorTwistedComplex_leftUnitor]
    rfl
  rw [ht, sectionPoleCoefficient_step f s hs hI e]

end FLT.Mazur.FCurve
