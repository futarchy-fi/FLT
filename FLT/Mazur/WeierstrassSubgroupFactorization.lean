/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CompatibleSubgroupIsoConjugation
public import FLT.Mazur.CompatibleSubgroupBaseChangeCompEq
public import FLT.Mazur.WeierstrassSubgroupUniversalCurve

/-!
# Closed subgroup factorization over the original coefficient base

The factorization criterion uses the original subgroups over any named
composite base map and the actual pullback of the full universal comparison.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry WeierstrassCurve
namespace FLT.Mazur.WeierstrassChangeParameter
open WeierstrassIntegralChart GeneralizedEllipticCurve GeneralizedEllipticCurve.FiniteSubgroup
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] (W V : WeierstrassCurve R)
  (hW : IsUnit W.Δ) (hV : IsUnit V.Δ) {n : ℕ}
  (H : (integralGeneralizedEllipticCurve W hW).FiniteSubgroup n)
  (J : (integralGeneralizedEllipticCurve V hV).FiniteSubgroup n)
local notation "q" => comparisonStructure W V
local notation "e" => universalGeneralizedComparison W V hW hV

/-- A test factors through the closed locus exactly when its full comparison preserves subgroups. -/
theorem subgroupInclusion_factorization_comp_iff {T : Scheme}
    (g : T ⟶ comparisonScheme W V) (t : T ⟶ Spec (.of R)) (ht : t = g ≫ q) :
    (∃ k : T ⟶ subgroupScheme W V hW hV H J,
      k ≫ subgroupInclusion W V hW hV H J = g) ↔
      ∃ a : CompatibleIso (H.baseChange t) (J.baseChange t),
        a.curve = comparisonPullback _ _ q g t ht e := by
  rw [subgroupInclusion_factorization_iff]
  have h := compatibleIso_exists_conjugate_iff
    (compatibleBaseChangeCompEq H q g t ht).symm
    (compatibleBaseChangeCompEq J q g t ht).symm
    (((H.baseChange q).transportCompatibleIso e).baseChange g).curve
  simpa only [CompatibleIso.symm, compatibleBaseChangeCompEq_curve, Iso.symm_symm_eq,
    CompatibleIso.baseChange, transportCompatibleIso, comparisonPullback] using h

/-- Closed immersion makes every such lift unique, without any etaleness hypothesis. -/
theorem subgroupInclusion_factorization_unique {T : Scheme}
    (g : T ⟶ comparisonScheme W V) (t : T ⟶ Spec (.of R)) (ht : t = g ≫ q)
    (a : CompatibleIso (H.baseChange t) (J.baseChange t))
    (ha : a.curve = comparisonPullback _ _ q g t ht e) :
    ∃! k : T ⟶ subgroupScheme W V hW hV H J,
      k ≫ subgroupInclusion W V hW hV H J = g := by
  obtain ⟨k, hk⟩ := (subgroupInclusion_factorization_comp_iff W V hW hV H J g t ht).mpr
    ⟨a, ha⟩
  exact ⟨k, hk, fun l hl ↦ (cancel_mono _).mp (hl.trans hk.symm)⟩

end FLT.Mazur.WeierstrassChangeParameter
