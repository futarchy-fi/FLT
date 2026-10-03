/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DivisorCanonicalSection

/-!
# Canonical sections under divisor comparisons

Ideal equality, the empty-divisor isomorphism, and divisor addition preserve
the canonical section. The addition identity holds on every open, by the
sheaf condition and the already proved identities on common Cartier charts.
-/

open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules
@[expose] public noncomputable section
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.FCurve
variable {X : Scheme.{u}} {I J : X.IdealSheafData}
/-- Ideal equality preserves the canonical divisor section. -/
lemma divisorSection_eqIso (h : I = J) (hI : EffectiveCartier I) (hJ : EffectiveCartier J)
    (U : X.Opens) :
    (divisorLineBundleEqIso h hI hJ).hom.app U (divisorSection hI U) =
      divisorSection hJ U := by
  subst J
  rfl
/-- The empty divisor canonical section is the inverse trivialization. -/
lemma divisorSection_top_map :
    divisorSectionMap (X := X) effectiveCartier_top =
      (divisorLineBundleTopIso effectiveCartier_top).inv := rfl
/-- The canonical section of the empty divisor has coordinate one. -/
lemma divisorSection_top (U : X.Opens) :
    (divisorLineBundleTopIso (X := X) effectiveCartier_top).hom.app U
      (divisorSection effectiveCartier_top U) = (1 : Γ(X, U)) := by
  unfold divisorSection
  rw [divisorSection_top_map]
  exact congrArg (fun f ↦ f.app U (1 : Γ(X, U)))
    (divisorLineBundleTopIso (X := X) effectiveCartier_top).inv_hom_id
/-- Divisor addition preserves canonical sections on an arbitrary open. -/
lemma divisorSection_sum_open (hI : EffectiveCartier I) (hJ : EffectiveCartier J)
    (U : X.Opens) :
    (divisorLineBundleSumIso hI hJ).hom.app U
      (ModuleSheafTensor.pure _ _ U (divisorSection hI U) (divisorSection hJ U)) =
    divisorSection (hI.mul hJ) U := by
  apply TopCat.Presheaf.IsSheaf.section_ext (divisorLineBundle (I * J) (hI.mul hJ)).isSheaf
  intro x hx
  obtain ⟨V, ⟨A, rfl⟩, hxA, hAU⟩ :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.mp (commonCartierChart_isBasis hI hJ) hx
  refine ⟨A.1.1, hAU, hxA, ?_⟩
  have hn := congrArg (fun f ↦ f (ModuleSheafTensor.pure _ _ U
    (divisorSection hI U) (divisorSection hJ U)))
    ((divisorLineBundleSumIso hI hJ).hom.mapPresheaf.naturality (homOfLE hAU).op)
  change (divisorLineBundleSumIso hI hJ).hom.app A.1.1
      ((ModuleSheafTensor.tensor _ _).presheaf.map _ _) =
      (divisorLineBundle (I * J) (hI.mul hJ)).presheaf.map (homOfLE hAU).op
        ((divisorLineBundleSumIso hI hJ).hom.app U
          (ModuleSheafTensor.pure _ _ U (divisorSection hI U) (divisorSection hJ U))) at hn
  rw [← hn, ModuleSheafTensor.pure_restrict, divisorSection_restrict,
    divisorSection_restrict, divisorSection_restrict]
  exact divisorSection_sum hI hJ A.1 A.2.1 A.2.2
end FLT.Mazur.FCurve
