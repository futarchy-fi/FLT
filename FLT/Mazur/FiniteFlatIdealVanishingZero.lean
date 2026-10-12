/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteFlatIdealVanishingRestriction
public import FLT.Mazur.ProjectiveIdealVanishingZero

/-!
# Global detection of the original family ideal

The global coefficient ideal vanishes exactly when the original ideal on the
entire finite family vanishes. Detection uses its affine preimage cover and
does not discard nonreduced structure.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.FiniteFlatIdealVanishing
set_option backward.isDefEq.respectTransparency false
variable {D S : Scheme} (g : D ⟶ S) [IsFinite g] [Flat g]
  [LocallyOfFinitePresentation g] (J : D.IdealSheafData)

/-- On a chart, the coefficient ideal detects the whole original preimage ideal. -/
theorem coefficientIdeal_eq_bot_iff (U : S.affineOpens) :
    coefficientIdeal g J U = ⊥ ↔ preimageIdeal g J U = ⊥ := by
  let _ := (g.app U.1).hom.toAlgebra
  let _ := FCurve.finiteFlat_app_projective g U
  exact ProjectiveIdealVanishing.ideal_eq_bot_iff _ _ _

/-- The actual global equations are zero exactly when the original family ideal is zero. -/
theorem idealSheaf_eq_bot_iff : idealSheaf g J = ⊥ ↔ J = ⊥ := by
  constructor
  · intro h
    apply Scheme.IdealSheafData.ext_of_iSup_eq_top
      (fun U : S.affineOpens ↦ ⟨g ⁻¹ᵁ U.1, U.2.preimage g⟩)
    · apply top_unique
      intro x _
      have hx : g x ∈ ⨆ U : S.affineOpens, U.1 := by
        rw [iSup_affineOpens_eq_top]
        trivial
      obtain ⟨U, hU⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨U, hU⟩
    · intro U
      have hc := congrArg (fun I : S.IdealSheafData ↦ I.ideal U) h
      exact (coefficientIdeal_eq_bot_iff g J U).mp hc
  · intro h
    apply Scheme.IdealSheafData.ext
    funext U
    apply (coefficientIdeal_eq_bot_iff g J U).mpr
    simp only [preimageIdeal, h, Scheme.IdealSheafData.ideal_bot, Pi.bot_apply]

/-- The global closed immersion is an isomorphism precisely for an already zero ideal. -/
theorem locusInclusion_isIso_iff : IsIso (locusInclusion g J) ↔ J = ⊥ := by
  change IsIso (idealSheaf g J).subschemeι ↔ _
  rw [Scheme.isIso_subschemeι_iff_eq_bot, idealSheaf_eq_bot_iff]

end FLT.Mazur.FiniteFlatIdealVanishing
