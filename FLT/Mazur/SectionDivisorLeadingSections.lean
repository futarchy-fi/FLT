/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SectionDivisorQuotientLine
public import FLT.Mazur.DivisorPowerRingLeadingClass
public import Mathlib.Tactic.IrreducibleDef

/-!
# Leading sections in the original base line

Identify the actual leading-class module with sections of the line obtained
by restricting the original pole power along the section. Exactness and
surjectivity retain the base scalars and the original pole transition.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.FCurve
open ModuleLineBundleTensorPullback
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] divisorLineBundle

variable {X S : Scheme} (f : X ⟶ S)

/-- H0 over the original base ring is sections of the actual direct image. -/
def ringHZeroPushforwardSections (M : X.Modules) :
    ModuleRingH f.appTop.hom M 0 ≃ₗ[Γ(S, ⊤)]
      Γ((pushforward f).obj M, ⊤) :=
  { (moduleH0Equiv M).toAddEquiv with
    map_smul' := fun r x ↦ (moduleH0Equiv M).map_smul (f.appTop r) x }

variable [IsSeparated f] (s : S ⟶ X) (hs : s ≫ f = 𝟙 S)
  (hI : EffectiveCartier s.ker)

/-- The leading-class module is canonically sections of the original base line. -/
irreducible_def sectionLeadingLineEquiv (m : ℕ) :
    ModuleRingH f.appTop.hom
      (divisorTwistedComplex hI (tensorPower (divisorLineBundle s.ker hI) m)).X₃ 0 ≃ₗ[Γ(S, ⊤)]
        Γ(sectionPoleLine s hI (m + 1), ⊤) :=
  (ringHZeroPushforwardSections f _).trans
    (((AffineModuleGlobalSections.sections S).mapIso
      (sectionDivisorQuotientPushforwardIso f s hs hI m)).toLinearEquiv)

/-- The original leading map, with values in the base pole line's actual sections. -/
def sectionPoleLeading (m : ℕ) :
    ModuleRingH f.appTop.hom (tensorPower (divisorLineBundle s.ker hI) (m + 1)) 0 →ₗ[Γ(S, ⊤)]
      Γ(sectionPoleLine s hI (m + 1), ⊤) :=
  (sectionLeadingLineEquiv f s hs hI m).toLinearMap.comp
    (divisorPowerRingLeading f.appTop.hom hI m)

/-- The base-line leading section vanishes exactly in the original lower pole space. -/
theorem sectionPoleLeading_eq_zero_iff (m : ℕ)
    (x : ModuleRingH f.appTop.hom (tensorPower (divisorLineBundle s.ker hI) (m + 1)) 0) :
    sectionPoleLeading f s hs hI m x = 0 ↔
      x ∈ LinearMap.range (divisorPowerRingStep f.appTop.hom hI m) := by
  change sectionLeadingLineEquiv f s hs hI m (divisorPowerRingLeading _ _ _ x) = 0 ↔ _
  rw [LinearEquiv.map_eq_zero_iff, divisorPowerRingLeading_eq_zero_iff]

/-- H1 vanishing lifts every section of the original base pole line. -/
theorem sectionPoleLeading_surjective (m : ℕ)
    [Subsingleton (ModuleH (tensorPower (divisorLineBundle s.ker hI) m) 1)] :
    Function.Surjective (sectionPoleLeading f s hs hI m) :=
  (sectionLeadingLineEquiv f s hs hI m).surjective.comp
    (divisorPowerRingLeading_surjective f.appTop.hom hI m)

/-- The positive pole quotient is the actual base-line section module. -/
def sectionPoleQuotientEquiv (m : ℕ)
    [Subsingleton (ModuleH (tensorPower (divisorLineBundle s.ker hI) m) 1)] :
    (ModuleRingH f.appTop.hom (tensorPower (divisorLineBundle s.ker hI) (m + 1)) 0 ⧸
      LinearMap.range (divisorPowerRingStep f.appTop.hom hI m)) ≃ₗ[Γ(S, ⊤)]
        Γ(sectionPoleLine s hI (m + 1), ⊤) :=
  (divisorPowerRingLeadingEquiv f.appTop.hom hI m).trans
    (sectionLeadingLineEquiv f s hs hI m)

end FLT.Mazur.FCurve
