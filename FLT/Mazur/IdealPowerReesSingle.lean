/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealPowerReesAction

/-!
# Original homogeneous section coordinates

An original ideal-power section occupies exactly its own polynomial degree.
The Rees action on such a section is the original polynomial convolution.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open Scheme.Modules FLT.Mazur.GlobalIdealPower
open scoped DirectSum

universe u

namespace FLT.Mazur.IdealPowerRees

variable {X : Scheme.{u}} [IsLocallyNoetherian X]
  (I : X.IdealSheafData) (M : X.Modules) [M.IsFinitePresentation] (V : X.affineOpens)

/-- A single original power section has its original inclusion in exactly one degree. -/
lemma sectionsEquiv_of (n : ℕ) (s : Γ(power I n M, V.1)) :
    (sectionsEquiv I M V (DirectSum.of (fun k ↦ Γ(power I k M, V.1)) n s)).val =
      PolynomialModule.single Γ(X, V.1) n ((inclusion (I ^ n) M).app V.1 s) := by
  ext k
  rw [sectionsEquiv_coeff, PolynomialModule.coeff_single]
  by_cases h : n = k
  · subst k
    rw [DirectSum.of_eq_same, Finsupp.single_eq_same]
  · rw [DirectSum.of_eq_of_ne _ _ _ (Ne.symm h), map_zero,
      Finsupp.single_eq_of_ne (Ne.symm h)]

/-- A local homogeneous Rees scalar multiplies the original included coefficient. -/
lemma sectionsEquiv_monomial_smul_of (a n : ℕ) (r : ↥((I.ideal V) ^ a))
    (s : Γ(power I n M, V.1)) :
    let _ := sectionsModule I M V
    (sectionsEquiv I M V
      ((⟨Polynomial.monomial a r.val, reesAlgebra.monomial_mem.mpr r.property⟩ :
          reesAlgebra (I.ideal V)) •
        DirectSum.of (fun k ↦ Γ(power I k M, V.1)) n s)).val =
      PolynomialModule.single Γ(X, V.1) (a + n)
        (r.val • (inclusion (I ^ n) M).app V.1 s) := by
  let _ := sectionsModule I M V
  dsimp only
  rw [sectionsModule_smul]
  change Polynomial.monomial a r.val •
    (sectionsEquiv I M V (DirectSum.of (fun k ↦ Γ(power I k M, V.1)) n s)).val = _
  rw [sectionsEquiv_of, PolynomialModule.monomial_smul_single]

end FLT.Mazur.IdealPowerRees
