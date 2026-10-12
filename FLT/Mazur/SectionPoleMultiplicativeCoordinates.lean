/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SectionGradedCoordinates
public import FLT.Mazur.SectionGradedPullback
public import FLT.Mazur.SectionPoleLeadingRestriction

/-!
# Multiplicative leading coordinates from one section-line frame

Restriction to the retained section followed by tensor powers of one frame
multiplies leading coefficients of arbitrary original pole sections.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.FCurve
open ModuleLineBundleTensorPullback
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] divisorLineBundle ModuleSheafTensor.tensor

variable {X S : Scheme} (s : S ⟶ X) (hI : EffectiveCartier s.ker)
  (e : (pullback s).obj (divisorLineBundle s.ker hI) ≅ structureModule S)

/-- All leading frames are tensor powers of the same original section-line frame. -/
def sectionPoleMultiplicativeFrame (m : ℕ) :
    sectionPoleLine s hI m ≅ structureModule S :=
  tensorPowerIso s (divisorLineBundle s.ker hI) m ≪≫ tensorPowerTrivialization e m

/-- The induced linear coordinate on sections of the actual leading line. -/
def sectionPoleMultiplicativeCoordinates (m : ℕ) :
    Γ(sectionPoleLine s hI m, ⊤) ≃ₗ[Γ(S, ⊤)] Γ(S, ⊤) :=
  ((AffineModuleGlobalSections.sections S).mapIso
    (sectionPoleMultiplicativeFrame s hI e m)).toLinearEquiv

/-- Evaluate any original pole section along the marking in its common tensor frame. -/
def sectionPoleCoefficient (m : ℕ)
    (x : Γ(tensorPower (divisorLineBundle s.ker hI) m, ⊤)) : Γ(S, ⊤) :=
  SectionGradedCoordinates.coordinate e m ⊤
    (SectionGradedPullback.pull s (divisorLineBundle s.ker hI) m ⊤ x)

/-- The coefficient is obtained by the actual adjunction-unit restriction. -/
theorem sectionPoleCoefficient_restriction (m : ℕ)
    (x : Γ(tensorPower (divisorLineBundle s.ker hI) m, ⊤)) :
    sectionPoleCoefficient s hI e m x =
      sectionPoleMultiplicativeCoordinates s hI e m
        (((pullbackPushforwardAdjunction s).unit.app
          (tensorPower (divisorLineBundle s.ker hI) m)).app ⊤ x) := rfl

/-- Leading coefficients of arbitrary sections multiply in the common frame. -/
theorem sectionPoleCoefficient_mul (m n : ℕ)
    (x : Γ(tensorPower (divisorLineBundle s.ker hI) m, ⊤))
    (y : Γ(tensorPower (divisorLineBundle s.ker hI) n, ⊤)) :
    sectionPoleCoefficient s hI e (m + n)
      (SectionGradedMultiplication.mul _ ⊤ m n x y) =
        sectionPoleCoefficient s hI e m x * sectionPoleCoefficient s hI e n y := by
  unfold sectionPoleCoefficient
  rw [SectionGradedPullback.pull_mul]
  exact SectionGradedCoordinates.coordinate_mul e m n ⊤ _ _

variable (f : X ⟶ S) [IsSeparated f] (hs : s ≫ f = 𝟙 S)

/-- The common-frame coefficient is the original cohomological leading map. -/
theorem sectionPoleCoefficient_leading (m : ℕ)
    (x : ModuleRingH f.appTop.hom (tensorPower (divisorLineBundle s.ker hI) (m + 1)) 0) :
    sectionPoleCoefficient s hI e (m + 1) (moduleH0Equiv _ x) =
      sectionPoleMultiplicativeCoordinates s hI e (m + 1)
        (sectionPoleLeading f s hs hI m x) := by
  rw [sectionPoleLeading_sections]
  exact sectionPoleCoefficient_restriction s hI e (m + 1) _

end FLT.Mazur.FCurve
