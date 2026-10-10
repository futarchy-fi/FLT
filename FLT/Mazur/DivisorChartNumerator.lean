/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DivisorCanonicalSection

/-!
# Numerators of actual positive divisor sections

A specified regular equation gives numerator coordinates on the positive
line. Restriction carries these numerators along the actual section map.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.FCurve

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u
variable {X : Scheme.{u}} {I : X.IdealSheafData} (hI : EffectiveCartier I)
variable (U : X.affineOpens) (a : Γ(X, U)) (ha : IsRegular a)
variable (he : I.ideal U = Ideal.span {a})

/-- Evaluation on a specified regular equation is the actual section numerator. -/
def divisorNumerator : Γ(divisorLineBundle I hI, U.1) ≃ₗ[Γ(X, U)] Γ(X, U) :=
  (show CartierChart I U from ⟨a, ha, he⟩).divisorSectionsEquiv hI ≪≫ₗ
    CartierModule.dualEquiv _ a ha he

/-- The numerator is evaluation on the original ideal generator. -/
theorem divisorNumerator_apply (s : Γ(divisorLineBundle I hI, U.1)) :
    divisorNumerator hI U a ha he s =
      divisorChartEval I U s (CartierModule.idealEquiv _ a ha he 1) := rfl

/-- The canonical section multiplied by a function has that function times the equation. -/
theorem divisorNumerator_canonical (r : Γ(X, U)) :
    divisorNumerator hI U a ha he (r • divisorSection hI U.1) = r * a := by
  rw [map_smul, divisorNumerator_apply, divisorSection_eval]
  change r * (1 * a) = r * a
  rw [one_mul]

/-- Numerator coordinates restrict along the genuine section-ring restriction map. -/
theorem divisorNumerator_restrict {V : X.affineOpens} (hVU : V ≤ U)
    (s : Γ(divisorLineBundle I hI, U.1)) :
    divisorNumerator hI V
        ((X.presheaf.map (homOfLE (show V.1 ≤ U.1 from hVU)).op).hom a)
        (regular_restrict hVU ha) (ideal_eq_span_restrict I hVU he)
        ((divisorLineBundle I hI).presheaf.map
          (homOfLE (show V.1 ≤ U.1 from hVU)).op s) =
      X.presheaf.map (homOfLE (show V.1 ≤ U.1 from hVU)).op
        (divisorNumerator hI U a ha he s) := by
  rw [divisorNumerator_apply, divisorNumerator_apply]
  have hg : CartierModule.idealEquiv (I.ideal V) _ (regular_restrict hVU ha)
      (ideal_eq_span_restrict I hVU he) 1 =
      CartierModule.idealRestrict _ _ _ (I.map_ideal hVU).le
        (CartierModule.idealEquiv _ a ha he 1) := by
    apply Subtype.ext
    change 1 * _ = (X.presheaf.map (homOfLE (show V.1 ≤ U.1 from hVU)).op).hom (1 * a)
    simp only [one_mul]
  rw [hg]
  exact divisorChartEval_restrict I hVU s _

/-- Restriction of a function times the canonical section retains its original function. -/
theorem divisorCanonical_smul_restrict {V : X.Opens} (hVU : V ≤ U.1) (r : Γ(X, U)) :
    (divisorLineBundle I hI).presheaf.map (homOfLE hVU).op
        (r • divisorSection hI U.1) =
      (X.presheaf.map (homOfLE hVU).op r) • divisorSection hI V := by
  rw [Scheme.Modules.map_smul, divisorSection_restrict]

end FLT.Mazur.FCurve
