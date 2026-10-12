/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SectionDivisorLeadingSections

/-!
# Relative leading sections are original restrictions

The base-ring cohomology comparison preserves the original global section.
The leading map is thus the actual restriction along the section, which is
needed when computing leading coefficients of products.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.FCurve
open ModuleLineBundleTensorPullback
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] divisorLineBundle

variable {X S : Scheme} (f : X ⟶ S) (s : S ⟶ X) (hs : s ≫ f = 𝟙 S)

/-- A section retraction does not change the underlying global section. -/
theorem sectionPushforwardComparison_sections {M : X.Modules} {N : S.Modules}
    (a : M ≅ (pushforward s).obj N) (x : Γ(M, ⊤)) :
    (((pushforward f).mapIso a ≪≫ (pushforwardComp s f).app N ≪≫
      (pushforwardCongr hs).app N ≪≫ (pushforwardId S).app N).hom.app ⊤) x =
        a.hom.app ⊤ x := by
  change N.presheaf.map (𝟙 (Opposite.op ⊤)) (a.hom.app ⊤ x) = a.hom.app ⊤ x
  simp

/-- Applying an H0-to-direct-image comparison preserves its original section. -/
theorem ringHZeroPushforwardSections_iso_apply (M : X.Modules) (N : S.Modules)
    (e : (pushforward f).obj M ≅ N) (x : ModuleRingH f.appTop.hom M 0) :
    ((ringHZeroPushforwardSections f M).trans
      (((AffineModuleGlobalSections.sections S).mapIso e).toLinearEquiv)) x =
        e.hom.app ⊤ (moduleH0Equiv M x) := rfl

variable [IsSeparated f] (hI : EffectiveCartier s.ker)

/-- The base-line leading map is restriction of the original section along the marking. -/
theorem sectionPoleLeading_sections (m : ℕ)
    (x : ModuleRingH f.appTop.hom (tensorPower (divisorLineBundle s.ker hI) (m + 1)) 0) :
    sectionPoleLeading f s hs hI m x =
      ((pullbackPushforwardAdjunction s).unit.app
        (tensorPower (divisorLineBundle s.ker hI) (m + 1))).app ⊤ (moduleH0Equiv _ x) := by
  let Q := (divisorTwistedComplex hI (tensorPower (divisorLineBundle s.ker hI) m)).X₃
  let g := (divisorTwistedComplex hI (tensorPower (divisorLineBundle s.ker hI) m)).g
  let a := sectionDivisorQuotientIso f s hs hI m
  change sectionLeadingLineEquiv f s hs hI m (divisorPowerRingLeading _ _ _ x) = _
  calc
    _ = ((ringHZeroPushforwardSections f Q).trans
        (((AffineModuleGlobalSections.sections S).mapIso
          (sectionDivisorQuotientPushforwardIso f s hs hI m)).toLinearEquiv))
            (divisorPowerRingLeading f.appTop.hom hI m x) :=
      DFunLike.congr_fun (sectionLeadingLineEquiv_def f s hs hI m) _
    _ = (sectionDivisorQuotientPushforwardIso f s hs hI m).hom.app ⊤
        (moduleH0Equiv Q (divisorPowerRingLeading f.appTop.hom hI m x)) :=
      ringHZeroPushforwardSections_iso_apply f Q (sectionPoleLine s hI (m + 1))
        (sectionDivisorQuotientPushforwardIso f s hs hI m)
        (divisorPowerRingLeading f.appTop.hom hI m x)
    _ = a.hom.app ⊤ (moduleH0Equiv Q (divisorPowerRingLeading f.appTop.hom hI m x)) :=
      (congrArg (fun e ↦ e.hom.app ⊤
        (moduleH0Equiv Q (divisorPowerRingLeading f.appTop.hom hI m x)))
          (sectionDivisorQuotientPushforwardIso_def f s hs hI m)).trans
        (sectionPushforwardComparison_sections f s hs a _)
    _ = a.hom.app ⊤ (g.app ⊤ (moduleH0Equiv _ x)) :=
      congrArg (fun z ↦ a.hom.app ⊤ z) (moduleH0Equiv_naturality g x)
    _ = _ := congrArg (fun t ↦ t.app ⊤ (moduleH0Equiv _ x))
      (sectionDivisorQuotientIso_projection f s hs hI m)

end FLT.Mazur.FCurve
