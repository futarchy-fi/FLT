/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DivisorCanonicalSection

/-!
# The Cartier ideal in arbitrary linear section coordinates

Changing a rank-one frame preserves the full principal ideal of a section.
Thus the canonical divisor section cuts out the original Cartier ideal in
every linear frame on a Cartier chart, with its multiplicity retained.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
universe u v

/-- Two linear frames give the same principal ideal for each original section. -/
theorem linearFrame_span_eq {R : Type u} [CommRing R] {M : Type v}
    [AddCommGroup M] [Module R M] (e d : M ≃ₗ[R] R) (x : M) :
    Ideal.span {e x} = Ideal.span {d x} := by
  have h (a b : M ≃ₗ[R] R) : a x ∈ Ideal.span {b x} := by
    have hx : b x • b.symm 1 = x := by
      apply b.injective
      rw [b.map_smul, b.apply_symm_apply, smul_eq_mul, mul_one]
    have hc : b x * a (b.symm 1) = a x := by
      rw [← smul_eq_mul, ← a.map_smul, hx]
    exact Ideal.mem_span_singleton.mpr ⟨a (b.symm 1), hc.symm⟩
  exact le_antisymm (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr (h e d)))
    (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr (h d e)))

/-- The original divisor ideal is independent of the chosen linear section frame. -/
theorem divisorSection_span_in_frame {X : Scheme.{u}} {I : X.IdealSheafData}
    (hI : EffectiveCartier I) {U : X.affineOpens} (hU : CartierChart I U)
    (e : Γ(divisorLineBundle I hI, U.1) ≃ₗ[Γ(X, U.1)] Γ(X, U.1)) :
    Ideal.span {e (divisorSection hI U.1)} = I.ideal U := by
  exact (linearFrame_span_eq e ((hU.divisorSectionsEquiv hI).trans hU.dualEquiv)
    (divisorSection hI U.1)).trans (divisorSection_span hI hU)

end FLT.Mazur.FCurve
