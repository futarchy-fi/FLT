/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DivisorComplementFaithful
public import FLT.Mazur.DivisorLeadingNonzeroProduct

/-!
# Exact pole orders of products on the original complement

Restriction to the actual Cartier point detects the preceding pole bound.
This transports nonzero products of fiber sections through their total degree
and back to the original filtration of complement functions.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.FCurve
open ModuleLineBundleTensorPullback
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {k : Type} [Field k] {X : Scheme} (f : X ⟶ Spec (.of k))
  {I : X.IdealSheafData} (hI : EffectiveCartier I)

include f in
/-- Exact successor pole order is detected on the actual restricted line. -/
theorem divisorComplementFunction_not_mem_iff (m : ℕ)
    (s : Γ(tensorPower (divisorLineBundle I hI) (m + 1), ⊤)) :
    divisorComplementFunction hI (m + 1) s ∉ divisorPoleFunctions hI m ↔
      pullGlobal I.subschemeι _ s ≠ 0 := by
  let x := (moduleScalarH0Equiv f _).symm s
  have he := (divisorPowerH0Function_mem_lower_iff hI f m x).not
  have hl := divisorPowerLeadingClass_ne_zero_iff_restriction f hI m x
  rw [ne_eq, divisorPowerLeadingClass_eq_zero_iff] at hl
  simpa only [x, divisorPowerH0Function, LinearEquiv.apply_symm_apply] using he.trans hl

include f in
/-- Nonzero restriction at any positive total degree excludes the preceding pole bound. -/
theorem divisorComplementFunction_not_mem_pred (d : ℕ) (hd : 0 < d)
    (s : Γ(tensorPower (divisorLineBundle I hI) d, ⊤))
    (hs : pullGlobal I.subschemeι _ s ≠ 0) :
    divisorComplementFunction hI d s ∉ divisorPoleFunctions hI (d - 1) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hd)
  exact (divisorComplementFunction_not_mem_iff f hI m s).mpr hs

include f in
/-- Exact positive orders add under multiplication at an integral one-point divisor. -/
theorem divisorPoleFunctions_mul_not_mem
    [IsIntegral I.subscheme] [Subsingleton I.subscheme]
    (m n : ℕ) {a b : Γ(Scheme.Opens.toScheme (X := X) I.support.compl, ⊤)}
    (ha : a ∈ divisorPoleFunctions hI (m + 1))
    (hb : b ∈ divisorPoleFunctions hI (n + 1))
    (ha' : a ∉ divisorPoleFunctions hI m) (hb' : b ∉ divisorPoleFunctions hI n) :
    a * b ∉ divisorPoleFunctions hI (m + n + 1) := by
  obtain ⟨s, rfl⟩ := ha
  obtain ⟨t, rfl⟩ := hb
  have hs := (divisorComplementFunction_not_mem_iff f hI m s).mp ha'
  have ht := (divisorComplementFunction_not_mem_iff f hI n t).mp hb'
  have hp := SectionGradedCoordinates.pullGlobal_mul_ne_zero I.subschemeι
    hI.divisorLineBundle_locallyFreeRankOne (m + 1) (n + 1) s t hs ht
  have hn := divisorComplementFunction_not_mem_pred f hI ((m + 1) + (n + 1))
    (by omega) _ hp
  rw [divisorComplementFunction_mul] at hn
  have he : ((m + 1) + (n + 1)) - 1 = m + n + 1 := by omega
  rw [he] at hn
  exact hn

/-- The original total-degree leading class of the product is nonzero. -/
theorem divisorLeading_product_ne_zero
    [IsIntegral I.subscheme] [Subsingleton I.subscheme]
    (m n r : ℕ) (hr : (m + 1) + (n + 1) = r + 1)
    (s : Γ(tensorPower (divisorLineBundle I hI) (m + 1), ⊤))
    (t : Γ(tensorPower (divisorLineBundle I hI) (n + 1), ⊤))
    (hs : pullGlobal I.subschemeι _ s ≠ 0)
    (ht : pullGlobal I.subschemeι _ t ≠ 0) :
    divisorPowerLeadingClass f hI r ((moduleScalarH0Equiv f _).symm
      (SectionGradedMultiplication.cast _ hr ⊤
        (SectionGradedMultiplication.mul _ ⊤ (m + 1) (n + 1) s t))) ≠ 0 := by
  rw [divisorPowerLeadingClass_ne_zero_iff_restriction, LinearEquiv.apply_symm_apply]
  have hp := SectionGradedCoordinates.pullGlobal_mul_ne_zero I.subschemeι
    hI.divisorLineBundle_locallyFreeRankOne (m + 1) (n + 1) s t hs ht
  have hc {a b : ℕ} (e : a = b)
      (z : Γ(tensorPower (divisorLineBundle I hI) a, ⊤))
      (hz : pullGlobal I.subschemeι _ z ≠ 0) :
      pullGlobal I.subschemeι _ (SectionGradedMultiplication.cast _ e ⊤ z) ≠ 0 := by
    subst b
    exact hz
  exact hc hr _ hp

end FLT.Mazur.FCurve
