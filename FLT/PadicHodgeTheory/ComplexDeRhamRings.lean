/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.PadicHodgeTheory.ComplexFontaineTheta
public import Mathlib.RingTheory.Perfectoid.BDeRham

/-! # De Rham ring constructions for the actual integer ring of C_p

Instantiate the existing localization and adic-completion constructions.
Principalness of the theta kernel, DVR structure and the comparison theorem
remain separate obligations.
-/

@[expose] public noncomputable section
namespace PadicHodgeTheory
variable (p : ℕ) [Fact p.Prime]

/-- A_inf with p inverted. -/
abbrev ComplexAinfInvertP := Localization.Away (p : Ainf p)

/-- The localized theta map, constructed using actual p-adic completeness. -/
def complexThetaInvertP :
    ComplexAinfInvertP p →+* Localization.Away (p : 𝓞_ℂ_[p]) :=
  fontaineThetaInvertP 𝓞_ℂ_[p] p

/-- Localized theta agrees with integral theta on A_inf. -/
theorem complexThetaInvertP_algebraMap (x : Ainf p) :
    complexThetaInvertP p (algebraMap (Ainf p) (ComplexAinfInvertP p) x) =
      algebraMap 𝓞_ℂ_[p] (Localization.Away (p : 𝓞_ℂ_[p])) (complexTheta p x) := by
  simp [complexThetaInvertP, fontaineThetaInvertP, Localization.awayLift,
    IsLocalization.Away.lift_eq, complexTheta]

/-- B_dR^+ is the completion at the kernel of localized theta. -/
abbrev ComplexBDeRhamPlus := BDeRhamPlus 𝓞_ℂ_[p] p

/-- The underlying completion is the actual theta-kernel completion. -/
theorem complexBDeRhamPlus_eq : ComplexBDeRhamPlus p =
    AdicCompletion (RingHom.ker (complexThetaInvertP p)) (ComplexAinfInvertP p) := rfl

/-- B_dR uses Mathlib's localization at the images of all kernel generators.
This definition does not assert that such a generator exists. -/
abbrev ComplexBDeRham := BDeRham 𝓞_ℂ_[p] p

end PadicHodgeTheory
