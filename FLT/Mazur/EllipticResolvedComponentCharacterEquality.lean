/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticResolvedLaurentEquality
public import FLT.Mazur.EllipticFiniteTerminalLaurentEquality
public import FLT.Mazur.EllipticSplitDepthResidueCharacter
public import FLT.Mazur.EllipticFiniteMiddleLaurentCharacter

/-!
# Original characters on every component and on E₀

The Laurent equality tests extend through the final odd-depth chart. On E₀,
the actual resolved smooth specialization remembers precisely the original
smooth-reduction character. The even middle component retains its vertical
Laurent unit. All comparisons concern the same proper model.
-/

@[expose] public noncomputable section
open IsLocalRing CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {K : Type u} [Field K] (A : ValuationSubring K)
  {W : WeierstrassCurve A} {π : A} {n : ℕ} (D : SplitNodeDepth W π n)
  (j : ℕ) (hj0 : 0 < j) (hj : 2 * j < n)
  (P Q : (W.map (algebraMap A K)).toProjective.Point)
  (v : NodePointCoordinates A W π P) (hv : v.depth = j)
  (w : NodePointCoordinates A W π Q) (hw : w.depth = j)

include hj0 hj hv hw in
/-- Every strict negative component retains its character, including the final odd depth. -/
theorem resolvedSplitSmoothPoint_strict_negative_eq_iff
    (hb : IsUnit v.b) (hd : IsUnit w.b) :
    resolvedSplitSmoothPoint A D P = resolvedSplitSmoothPoint A D Q ↔
      residue A v.b = residue A w.b := by
  by_cases hlt : j < n / 2
  · exact resolvedSplitSmoothPoint_negative_eq_iff A D j hj0 hlt P Q v hv w hw hb hd
  have he : j = n / 2 := by omega
  rw [he] at hv hw hj0 hj
  rw [resolvedSplitSmoothPoint_eq_iff]
  exact finitePointSpecialization_terminal_negative_eq_iff A D.uniformizer_ne_zero
    (splitResolutionData A D) D (n / 2) (le_refl _) (by omega) (by omega)
    P Q v (by simpa only [zero_add] using hv) w (by simpa only [zero_add] using hw) hb hd

include hj0 hj hv hw in
/-- The positive character detects equality at every strict depth, without a retention gap. -/
theorem resolvedSplitSmoothPoint_strict_positive_eq_iff
    (hb : v.b ∈ maximalIdeal A) (hd : w.b ∈ maximalIdeal A) :
    resolvedSplitSmoothPoint A D P = resolvedSplitSmoothPoint A D Q ↔
      residue A (v.b + W.a₁ * v.a) = residue A (w.b + W.a₁ * w.a) := by
  by_cases hlt : j < n / 2
  · exact resolvedSplitSmoothPoint_positive_eq_iff A D j hj0 hlt P Q v hv w hw hb hd
  have he : j = n / 2 := by omega
  rw [he] at hv hw hj0 hj
  have hvu := nodePositiveLaurent_isUnit A (start := 0) D (n / 2) (by omega) (by omega) P v
    (by simpa only [zero_add] using hv) hb
  have hwu := nodePositiveLaurent_isUnit A (start := 0) D (n / 2) (by omega) (by omega) Q w
    (by simpa only [zero_add] using hw) hd
  rw [resolvedSplitSmoothPoint_eq_iff]
  exact finitePointSpecialization_terminal_positive_eq_iff A D.uniformizer_ne_zero
    (splitResolutionData A D) D (n / 2) (le_refl _) (by omega) (by omega)
    P Q v (by simpa only [zero_add] using hv) w (by simpa only [zero_add] using hw) hvu hwu

/-- The even middle component retains exactly the original vertical Laurent residue. -/
theorem resolvedSplitSmoothPoint_middle_character_eq_iff
    (P Q : (W.map (algebraMap A K)).toProjective.Point)
    (v : NodePointCoordinates A W π P) (w : NodePointCoordinates A W π Q)
    (hv : 2 * v.depth = n) (hw : 2 * w.depth = n) :
    resolvedSplitSmoothPoint A D P = resolvedSplitSmoothPoint A D Q ↔
      residue A v.b = residue A w.b := by
  have hn := D.depth_pos
  rw [resolvedSplitSmoothPoint_eq_iff,
    finitePointSpecialization_middle_character A D.uniformizer_ne_zero
      (splitResolutionData A D) D (n / 2) (le_refl _) (by omega) (by omega) (by omega)
      P v (by omega),
    finitePointSpecialization_middle_character A D.uniformizer_ne_zero
      (splitResolutionData A D) D (n / 2) (le_refl _) (by omega) (by omega) (by omega)
      Q w (by omega),
    cancel_mono, laurentUnitSpec_eq_iff, ← Units.val_inj,
    finiteMiddleLaurentUnit_val, finiteMiddleLaurentUnit_val]

/-- On E₀ the actual resolved points agree exactly when their original nodal characters agree. -/
theorem resolvedSplitSmoothPoint_e0_character_eq_iff [DecidableEq (ResidueField A)]
    (P Q : ellipticE0 A W) :
    resolvedSplitSmoothPoint A D P.val = resolvedSplitSmoothPoint A D Q.val ↔
      splitDepthSmoothCharacter D P = splitDepthSmoothCharacter D Q := by
  rw [resolvedSplitSmoothPoint_eq_iff, finitePointSpecialization_e0,
    finitePointSpecialization_e0, e0FiniteClosedPoint_eq_iff,
    splitDepthSmoothCharacter_eq_iff]

end FLT.Mazur.WeierstrassDividedDepth
