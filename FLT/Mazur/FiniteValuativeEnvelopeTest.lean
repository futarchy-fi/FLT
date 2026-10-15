/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ValuativeEnvelopeInterior

/-!
# Finitely many original generic coordinates suffice for valuation tests

Choose the generic points of the excluded locus once. Their valuation
specializations detect every original full-interior point simultaneously.
The points lie in the actual original envelope, and no proper core or
coefficient-domain hypothesis is needed.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry IsLocalRing TopologicalSpace
namespace FLT.Mazur.SchemeOpenEnvelope
universe u
variable {Y X : Scheme.{u}} (π : Y ⟶ X) (O : Y.Opens) [NoetherianSpace Y]

/-- A finite family of actual excluded coordinates gives a uniform valuation test. -/
theorem exists_finite_valuation_test :
    ∃ F : Set Y, F.Finite ∧ (∀ e ∈ F, e ∉ O) ∧
      ∀ x : X, x ∈ fullFiberInterior π O ↔
        ∀ D : ValuativeCommSq π, D.i₂ (closedPoint D.R) = x →
          D.i₁ (default : Spec (.of D.K)) ∈ F →
          D.i₁ (default : Spec (.of D.K)) ∈ O := by
  obtain ⟨F, hF, hFO, htest⟩ := NoetherianClosedImage.exists_finite_image_generizations
    π π.continuous O.isOpen.isClosed_compl
  refine ⟨F, hF, fun e he ↦ hFO he, fun x ↦ ⟨?_, ?_⟩⟩
  · intro hx D hc _
    exact generic_mem_of_closed_mem_interior π O D (hc.symm ▸ hx)
  · intro h
    by_contra hx
    have hcl : x ∈ closure (π '' (O : Set Y)ᶜ) := by
      change x ∉ interior (π '' (O : Set Y)ᶜ)ᶜ at hx
      rwa [interior_compl, Set.mem_compl_iff, not_not] at hx
    obtain ⟨e, he, hs⟩ := (htest x).mp hcl
    obtain ⟨D, hg, hc⟩ := SpecializationValuationSquare.exists_square π e x hs
    exact hFO he (hg ▸ h D hc (hg ▸ he))

omit [NoetherianSpace Y] in
/-- The finite tests construct one source denominator through any finite collection of points. -/
theorem exists_coefficient_of_valuation_tests [IsAffine X]
    (F : Set Y) (hF : ∀ x : X, x ∈ fullFiberInterior π O ↔
      ∀ D : ValuativeCommSq π, D.i₂ (closedPoint D.R) = x →
        D.i₁ (default : Spec (.of D.K)) ∈ F → D.i₁ (default : Spec (.of D.K)) ∈ O)
    (Z : Set X) (hZ : Z.Finite)
    (h : ∀ D : ValuativeCommSq π, D.i₂ (closedPoint D.R) ∈ Z →
      D.i₁ (default : Spec (.of D.K)) ∈ F → D.i₁ (default : Spec (.of D.K)) ∈ O) :
    ∃ r : Γ(X, ⊤), Z ⊆ X.basicOpen r ∧ r ∈ denominatorIdeal π.appTop.hom O := by
  apply exists_fullFiberInterior_coefficient π O Z hZ
  intro x hx
  apply (hF x).mpr
  intro D hc he
  exact h D (hc.symm ▸ hx) he

end FLT.Mazur.SchemeOpenEnvelope
