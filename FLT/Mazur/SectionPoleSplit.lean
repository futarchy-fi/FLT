/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SectionDivisorLeadingSections
public import FLT.Mazur.AffinePicardSections
public import Mathlib.Algebra.Exact.Basic

/-!
# Splitting the original positive pole filtration

On an affine base the actual section pole line has projective sections.
Consequently H1 vanishing splits the original leading map over the base
ring. The resulting product decomposition preserves both filtration maps.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.FCurve
open ModuleLineBundleTensorPullback
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {X S : Scheme} [IsAffine S] (f : X ⟶ S) [IsSeparated f]
  (s : S ⟶ X) (hs : s ≫ f = 𝟙 S) (hI : EffectiveCartier s.ker)

/-- The actual leading line has invertible global sections over the affine base. -/
theorem sectionPoleLine_sections_invertible (m : ℕ) :
    Module.Invertible Γ(S, ⊤) Γ(sectionPoleLine s hI m, ⊤) :=
  SchemePicard.sections_invertible _ (sectionPoleLine_rankOne s hI m)

omit [IsAffine S] in
/-- The original pole transition and base-line leading map are exact. -/
theorem sectionPoleLeading_exact (m : ℕ) :
    Function.Exact (divisorPowerRingStep f.appTop.hom hI m)
      (sectionPoleLeading f s hs hI m) :=
  fun x ↦ sectionPoleLeading_eq_zero_iff f s hs hI m x

variable (m : ℕ) [Subsingleton (ModuleH (tensorPower (divisorLineBundle s.ker hI) m) 1)]

/-- Projectivity constructs a linear lift of every base-line leading section. -/
theorem sectionPoleLeading_has_section :
    ∃ l : Γ(sectionPoleLine s hI (m + 1), ⊤) →ₗ[Γ(S, ⊤)]
        ModuleRingH f.appTop.hom (tensorPower (divisorLineBundle s.ker hI) (m + 1)) 0,
      (sectionPoleLeading f s hs hI m).comp l = LinearMap.id := by
  let _ := sectionPoleLine_sections_invertible s hI (m + 1)
  exact LinearMap.exists_rightInverse_of_surjective _
    (LinearMap.range_eq_top.mpr (sectionPoleLeading_surjective f s hs hI m))

/-- The constructed decomposition retains the actual inclusion and leading projection. -/
def sectionPoleSplit :
    { e : ModuleRingH f.appTop.hom (tensorPower (divisorLineBundle s.ker hI) (m + 1)) 0 ≃ₗ[Γ(S, ⊤)]
        ModuleRingH f.appTop.hom (tensorPower (divisorLineBundle s.ker hI) m) 0 ×
          Γ(sectionPoleLine s hI (m + 1), ⊤) //
      divisorPowerRingStep f.appTop.hom hI m =
        e.symm.toLinearMap.comp (LinearMap.inl _ _ _) ∧
      sectionPoleLeading f s hs hI m = (LinearMap.snd _ _ _).comp e.toLinearMap } :=
  (sectionPoleLeading_exact f s hs hI m).splitSurjectiveEquiv
    (divisorPowerRingStep_injective f.appTop.hom hI m)
    ⟨_, (sectionPoleLeading_has_section f s hs hI m).choose_spec⟩

/-- The old pole space is precisely the first summand of the constructed splitting. -/
theorem sectionPoleSplit_step
    (x : ModuleRingH f.appTop.hom (tensorPower (divisorLineBundle s.ker hI) m) 0) :
    (sectionPoleSplit f s hs hI m).val (divisorPowerRingStep f.appTop.hom hI m x) =
      (x, 0) := by
  rw [LinearMap.congr_fun (sectionPoleSplit f s hs hI m).property.1 x]
  exact (sectionPoleSplit f s hs hI m).val.apply_symm_apply _

/-- The second component is the original leading section, not a new quotient map. -/
theorem sectionPoleSplit_leading
    (x : ModuleRingH f.appTop.hom (tensorPower (divisorLineBundle s.ker hI) (m + 1)) 0) :
    ((sectionPoleSplit f s hs hI m).val x).2 = sectionPoleLeading f s hs hI m x :=
  (LinearMap.congr_fun (sectionPoleSplit f s hs hI m).property.2 x).symm

end FLT.Mazur.FCurve
