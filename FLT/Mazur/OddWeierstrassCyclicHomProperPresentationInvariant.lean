/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OddWeierstrassCyclicHomNormalizedCubicValue
public import FLT.Mazur.OddWeierstrassAuxiliaryProperPointInvariant

/-!
# Unrestricted cyclic normalization is independent of proper presentation

Actual proper comparisons preserve the auxiliary frame and all cyclic values.
The entire normalized parameter is then equal, including coincident cyclic labels.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.OddWeierstrassParameter
open UniversalWeierstrass (Labels)
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (n : ℕ) [NeZero n] {T : Scheme}
  (f g : T ⟶ (cyclicHomAuxiliaryScheme n).left)
local notation "a" => CommRingCat.Hom.hom (Scheme.Hom.appTop (cyclicHomAuxiliaryPoint n f))
local notation "b" => CommRingCat.Hom.hom (Scheme.Hom.appTop (cyclicHomAuxiliaryPoint n g))

/-- Full proper comparison data retain both independent markings on the original family. -/
def CyclicHomProperRelated : Prop :=
  ∃ e : integralCurve (auxiliaryPullbackEquation a) ≅
      integralCurve (auxiliaryPullbackEquation b),
    (e.hom ≫ integralCurveStructure (auxiliaryPullbackEquation b) =
      integralCurveStructure (auxiliaryPullbackEquation a)) ∧
    (integralCurveZero (auxiliaryPullbackEquation a) ≫ e.hom =
      integralCurveZero (auxiliaryPullbackEquation b)) ∧
    (∀ (c : Labels 3) (hc : c ≠ 1),
      auxiliaryPullbackSection a c hc ≫ e.hom = auxiliaryPullbackSection b c hc) ∧
    (∀ c : Multiplicative (ZMod n),
      cyclicHomOriginalCubicValue n f c ≫ e.hom = cyclicHomOriginalCubicValue n g c)

/-- An actual original proper comparison identifies the entire normalized cyclic parameter. -/
theorem CyclicHomProperRelated.normalized_eq (h : CyclicHomProperRelated n f g) :
    cyclicHomNormalizedPoint n f = cyclicHomNormalizedPoint n g := by
  obtain ⟨e, hb, hz, hm, hv⟩ := h
  have he := (auxiliaryNormalization_invariant a b e hb hz hm).1
  apply cyclicHomPoint_ext n
  · rw [cyclicHomNormalizedPoint_auxiliary, cyclicHomNormalizedPoint_auxiliary]
    exact auxiliarySchemeNormalizedPoint_invariant_of_proper_comparison _ _ e hb hz hm
  · intro c
    rw [cyclicHomNormalizedPoint_value_cubic, cyclicHomNormalizedPoint_value_cubic]
    have hs := auxiliaryProperSection_normalization_invariant a b e hb hz hm
      (cyclicHomOriginalCubicValue n f c) (cyclicHomOriginalCubicValue n g c) (hv c) he
    have hp := congrArg (fun z ↦ z ≫ auxiliaryNormalizedCoefficientProjection b) hs
    simpa only [Category.assoc, auxiliaryNormalizedCoefficientProjection_transport a b he] using hp

/-- Proper comparisons on affine tests identify the original global full normalization. -/
theorem cyclicHomNormalizedPoint_invariant_of_affine_tests
    (h : ∀ (R : Type) [CommRing R] (k : Spec (.of R) ⟶ T),
      CyclicHomProperRelated n (k ≫ f) (k ≫ g)) :
    cyclicHomNormalizedPoint n f = cyclicHomNormalizedPoint n g := by
  apply T.affineCover.hom_ext
  intro i
  apply (cancel_epi (T.affineCover.X i).isoSpec.inv).mp
  let k := (T.affineCover.X i).isoSpec.inv ≫ T.affineCover.f i
  have he := (h Γ(T.affineCover.X i, ⊤) k).normalized_eq n _ _
  rw [cyclicHomNormalizedPoint_natural, cyclicHomNormalizedPoint_natural] at he
  exact (Category.assoc _ _ _).symm.trans (he.trans (Category.assoc _ _ _))

end FLT.Mazur.OddWeierstrassParameter
