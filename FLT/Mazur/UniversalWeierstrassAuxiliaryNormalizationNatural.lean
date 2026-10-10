/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.UniversalWeierstrassAuxiliaryNormalEquation

/-!
# Canonical auxiliary normalization commutes with every ring map

The original global frame units, the chosen variable change, the normalized
separation, and the entire normalized equation retain their values after
arbitrary further pullback, including residue maps and nilpotent thickenings.
-/

@[expose] public noncomputable section

open WeierstrassCurve

namespace FLT.Mazur.UniversalWeierstrass

variable {R S : Type} [CommRing R] [CommRing S]
  (g : AuxiliarySectionRing →+* R) (f : R →+* S)

/-- The constructed admissible normalization is natural over arbitrary coefficient rings. -/
theorem auxiliaryFrameChange_natural :
    auxiliaryFrameChange (f.comp g) = (auxiliaryFrameChange g).map f := by
  apply VariableChange.ext
  · simp only [auxiliaryFrameChange, WeierstrassFrameNormalization.change,
      WeierstrassFrameNormalization.scale, VariableChange.map, map_mul, map_inv]
    rfl
  · rfl
  · simp only [auxiliaryFrameChange, WeierstrassFrameNormalization.change,
      VariableChange.map, RingHom.comp_apply, map_mul, map_sub, ← map_inv]
    rfl
  · rfl

/-- The unit separating the normalized marked sections is natural as an actual unit. -/
theorem auxiliaryFrameSeparation_natural :
    auxiliaryFrameSeparation (f.comp g) = Units.map f (auxiliaryFrameSeparation g) := by
  simp only [auxiliaryFrameSeparation, WeierstrassFrameNormalization.separation,
    WeierstrassFrameNormalization.scale, map_mul, map_pow, map_inv]
  rfl

/-- The entire normalized equation, not just its invariants, commutes with base ring maps. -/
theorem auxiliaryNormalizedEquation_natural :
    auxiliaryNormalizedEquation (f.comp g) = (auxiliaryNormalizedEquation g).map f := by
  rw [auxiliaryNormalizedEquation, auxiliaryFrameChange_natural]
  change (auxiliaryFrameChange g).map f • auxiliarySectionEquation.map (f.comp g) = _
  rw [← WeierstrassCurve.map_map, map_variableChange]
  rfl

end FLT.Mazur.UniversalWeierstrass
