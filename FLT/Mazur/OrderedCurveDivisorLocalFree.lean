/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OrderedCurveDivisorPresentation
public import FLT.Mazur.FiniteFlatAffineLocalFree

/-!
# Local freeness of the actual ordered divisor algebra

Each affine parameter open has a finite projective divisor algebra. Every prime
has a principal neighborhood where that actual algebra is free, including over
collision loci and non-Noetherian parameter schemes.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace FLT.Mazur.OrderedCurvePower

open FCurve

variable {X S : Scheme.{u}} (f : X ⟶ S) (n : ℕ)
  [SmoothOfRelativeDimension 1 f] [IsProper f]
  (U : (space f n).affineOpens)

/-- The finite algebra of the universal divisor is projective on every affine parameter open. -/
theorem divisorToBase_app_projective :
    let _ := ((divisorToBase f n).app U).hom.toAlgebra
    Module.Projective Γ(space f n, U) Γ(divisorScheme f n, divisorToBase f n ⁻¹ᵁ U) := by
  let _ := divisorToBase_isFinite f n
  let _ := divisorToBase_flat f n
  let _ := divisorToBase_locallyOfFinitePresentation f n
  exact finiteFlat_app_projective (divisorToBase f n) U

/-- Principal free neighborhoods for the actual universal divisor coordinate algebra. -/
theorem divisorToBase_app_exists_free (p : PrimeSpectrum Γ(space f n, U)) :
    let _ := ((divisorToBase f n).app U).hom.toAlgebra
    ∃ r : Γ(space f n, U), r ∉ p.asIdeal ∧
      Module.Free (Localization.Away r)
        (LocalizedModule.Away r Γ(divisorScheme f n, divisorToBase f n ⁻¹ᵁ U)) ∧
      Module.finrank (Localization.Away r)
          (LocalizedModule.Away r Γ(divisorScheme f n, divisorToBase f n ⁻¹ᵁ U)) =
        Module.rankAtStalk Γ(divisorScheme f n, divisorToBase f n ⁻¹ᵁ U) p := by
  let _ := divisorToBase_isFinite f n
  let _ := divisorToBase_flat f n
  let _ := divisorToBase_locallyOfFinitePresentation f n
  exact finiteFlat_app_exists_free (divisorToBase f n) U p

end FLT.Mazur.OrderedCurvePower
