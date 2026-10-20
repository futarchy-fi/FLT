/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteRelationEndpointImmersion
public import FLT.Mazur.AffineCartesianNorm

/-!
# Endpoint functions span the full finite relation algebra

The closed endpoint immersion and the affine tensor description express every
relation function as a linear combination of second-endpoint functions, with
coefficients from the first endpoint. All original arrows are retained.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct
namespace FLT.Mazur.FiniteRelationEndpointSpan
universe u
set_option backward.isDefEq.respectTransparency false
variable {D A S : Scheme.{u}} [IsAffine A] [IsAffine S]
  (p q : D ⟶ A) (f : A ⟶ S) (h : p ≫ f = q ≫ f)
  (e : CategoryTheory.EquivalenceRelation p q) [IsFinite p] [IsSeparated f]

include e h in
/-- The second endpoint spans the entire relation algebra over the first. -/
theorem span_range_eq_top :
    let _ := p.appTop.hom.toAlgebra
    Submodule.span Γ(A, ⊤) (Set.range q.appTop) = ⊤ := by
  let _ := p.appTop.hom.toAlgebra
  let _ := f.appTop.hom.toAlgebra
  let H := IsPullback.of_hasPullback f f
  let i := AffineCartesianNorm.tensorIso (pullback.snd f f) (pullback.fst f f)
    f f H.flip
  let m := pullback.lift p q h
  let φ : Γ(A, ⊤) ⊗[Γ(S, ⊤)] Γ(A, ⊤) →+* Γ(D, ⊤) :=
    m.appTop.hom.comp i.hom.hom
  let N := Submodule.span Γ(A, ⊤) (Set.range q.appTop)
  have hleft (a : Γ(A, ⊤)) : φ (a ⊗ₜ[Γ(S, ⊤)] 1) = p.appTop a := by
    change m.appTop (i.hom (a ⊗ₜ[Γ(S, ⊤)] 1)) = _
    rw [AffineCartesianNorm.tensorIso_left]
    change (m ≫ pullback.fst f f).appTop a = _
    rw [pullback.lift_fst]
  have hright (b : Γ(A, ⊤)) : φ (1 ⊗ₜ[Γ(S, ⊤)] b) = q.appTop b := by
    change m.appTop (i.hom (1 ⊗ₜ[Γ(S, ⊤)] b)) = _
    rw [AffineCartesianNorm.tensorIso_right]
    change (m ≫ pullback.snd f f).appTop b = _
    rw [pullback.lift_snd]
  have hmem (z : Γ(A, ⊤) ⊗[Γ(S, ⊤)] Γ(A, ⊤)) : φ z ∈ N := by
    induction z using TensorProduct.inductionOn with
    | tmul a b =>
      have ht : a ⊗ₜ[Γ(S, ⊤)] b =
          (a ⊗ₜ[Γ(S, ⊤)] 1) * (1 ⊗ₜ[Γ(S, ⊤)] b) := by
        simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rw [ht, map_mul, hleft, hright]
      exact N.smul_mem a (Submodule.subset_span ⟨b, rfl⟩)
    | add x y hx hy => simpa only [map_add] using N.add_mem hx hy
  apply top_unique
  intro z _
  obtain ⟨w, hw⟩ := FiniteRelationEndpointImmersion.endpoint_appTop_surjective p q f h e z
  obtain ⟨t, ht⟩ := i.commRingCatIsoToRingEquiv.surjective w
  have he : φ t = z := by
    change m.appTop (i.hom t) = z
    rw [show i.hom t = w from ht]
    exact hw
  rw [← he]
  exact hmem t

end FLT.Mazur.FiniteRelationEndpointSpan
