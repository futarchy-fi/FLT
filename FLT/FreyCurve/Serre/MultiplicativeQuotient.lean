/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.MultiplicativeReduction
public import FLT.FreyCurve.Serre.TateTorsion

/-!
# The unramified quotient at multiplicative reduction

A single inertia-equivariant splitting twist transports the Tate exponent quotient.
The torsion order may equal the residue characteristic.
-/

@[expose] public section

open scoped WeierstrassCurve.Affine
open ValuativeRel

namespace WeierstrassCurve

/-- Multiplicative reduction supplies a surjective inertia-invariant quotient of
geometric torsion, including when the torsion order is the residue characteristic. -/
theorem exists_inertia_invariant_torsion_quotient {K Ω : Type*}
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (E : WeierstrassCurve K) [E.IsElliptic] [E.HasMultiplicativeReduction 𝒪[K]]
    [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] [DecidableEq Ω]
    (A : ValuationSubring Ω)
    (hA : (A.comap (algebraMap K Ω)).toSubring = (algebraMap 𝒪[K] K).range)
    (n : ℕ) [NeZero (n : Ω)] :
    ∃ r : AddSubgroup.torsionBy (E⁄Ω).Point (n : ℤ) →+ ZMod n,
      Function.Surjective r ∧
      ∀ (σ : A.decompositionSubgroup K), σ ∈ A.inertiaSubgroup K →
        ∀ P Q : AddSubgroup.torsionBy (E⁄Ω).Point (n : ℤ),
          (Q : (E⁄Ω).Point) = Affine.Point.map (σ : Ω ≃ₐ[K] Ω).toAlgHom P → r Q = r P := by
  let : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  obtain ⟨E', hell, hsplit, e, he⟩ := E.exists_uniform_inertia_equivariant_split_twist A hA
  let := hell
  let := hsplit
  let eT : AddSubgroup.torsionBy (E⁄Ω).Point (n : ℤ) ≃+
      AddSubgroup.torsionBy (E'⁄Ω).Point (n : ℤ) :=
    { toFun := fun P ↦ ⟨e P, by
        change (n : ℤ) • e P = 0
        rw [← map_zsmul, show (n : ℤ) • P.val = 0 from P.property, map_zero]⟩
      invFun := fun P ↦ ⟨e.symm P, by
        change (n : ℤ) • e.symm P = 0
        rw [← map_zsmul, show (n : ℤ) • P.val = 0 from P.property, map_zero]⟩
      left_inv := fun P ↦ Subtype.ext (e.symm_apply_apply P)
      right_inv := fun P ↦ Subtype.ext (e.apply_symm_apply P)
      map_add' := fun P Q ↦ Subtype.ext (e.map_add P Q) }
  refine ⟨(E'.tateTorsionQuotient Ω n).comp eT.toAddMonoidHom,
    (E'.tateTorsionQuotient_surjective Ω n).comp eT.surjective, ?_⟩
  intro σ hσ P Q hQ
  apply E'.tateTorsionQuotient_galois Ω n (σ : Ω ≃ₐ[K] Ω) (eT P) (eT Q)
  change e Q = Affine.Point.map (σ : Ω ≃ₐ[K] Ω).toAlgHom (e P)
  rw [hQ, he σ hσ]

end WeierstrassCurve
