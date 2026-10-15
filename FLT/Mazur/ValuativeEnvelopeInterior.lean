/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SpecializationValuationSquare
public import FLT.Mazur.NoetherianClosedImageGenerizations
public import FLT.Mazur.SchemeOpenEnvelopeInterior

/-!
# Valuation tests for original full-envelope interiors

Every failure of interior membership is witnessed by an actual valuation
square whose generic envelope coordinate is excluded. Conversely every such
square prevents interior membership. At a full closed fiber, the excluded
square has no lift to the envelope, even though its closed fiber is full.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry IsLocalRing TopologicalSpace
namespace FLT.Mazur.SchemeOpenEnvelope
universe u
variable {Y X : Scheme.{u}} (π : Y ⟶ X) (O : Y.Opens)

/-- All valuation tests centered in the interior have their generic coordinate retained. -/
theorem generic_mem_of_closed_mem_interior (D : ValuativeCommSq π)
    (h : D.i₂ (closedPoint D.R) ∈ fullFiberInterior π O) :
    D.i₁ (default : Spec (.of D.K)) ∈ O := by
  have hg := (SpecializationValuationSquare.specializes π D).mem_open
    (fullFiberInterior π O).isOpen h
  exact preimage_fullFiberInterior_le π O hg

/-- An excluded generic coordinate cannot extend over a full closed fiber. -/
theorem no_lift_of_excluded_generic (D : ValuativeCommSq π)
    (hx : D.i₂ (closedPoint D.R) ∈ fullFiberLocus π O)
    (he : D.i₁ (default : Spec (.of D.K)) ∉ O) : ¬ D.commSq.HasLift := by
  intro hl
  obtain ⟨l, hg, hc⟩ := hl.exists_lift
  have hcO : l (closedPoint D.R) ∈ O := by
    apply (mem_fullFiberLocus π O _).mp hx
    exact congrArg (fun g : Spec (.of D.R) ⟶ X ↦ g (closedPoint D.R)) hc
  have hs := (specializes_closedPoint
    (Spec.map (CommRingCat.ofHom (algebraMap D.R D.K))
      (default : Spec (.of D.K)))).map l.continuous
  have hgO := hs.mem_open O.isOpen hcO
  have heq := congrArg (fun g : Spec (.of D.K) ⟶ Y ↦ g default) hg
  exact he (heq ▸ hgO)

variable [NoetherianSpace Y]

/-- Noninterior points have actual valuation-ring witnesses, with no properness assumption. -/
theorem not_interior_iff_valuation (x : X) :
    x ∉ fullFiberInterior π O ↔
      ∃ D : ValuativeCommSq π, D.i₂ (closedPoint D.R) = x ∧
        D.i₁ (default : Spec (.of D.K)) ∉ O := by
  constructor
  · intro hx
    have hcl : x ∈ closure (π '' (O : Set Y)ᶜ) := by
      change x ∉ interior (π '' (O : Set Y)ᶜ)ᶜ at hx
      rwa [interior_compl, Set.mem_compl_iff, not_not] at hx
    obtain ⟨e, he, hs⟩ := (NoetherianClosedImage.mem_closure_image_iff π π.continuous
      O.isOpen.isClosed_compl x).mp hcl
    obtain ⟨D, hg, hc⟩ := SpecializationValuationSquare.exists_square π e x hs
    exact ⟨D, hc, hg ▸ he⟩
  · rintro ⟨D, hc, he⟩ hx
    exact he (generic_mem_of_closed_mem_interior π O D (hc.symm ▸ hx))

/-- Testing whole valuation squares is necessary and sufficient for an original neighborhood. -/
theorem interior_iff_valuation (x : X) :
    x ∈ fullFiberInterior π O ↔
      ∀ D : ValuativeCommSq π, D.i₂ (closedPoint D.R) = x →
        D.i₁ (default : Spec (.of D.K)) ∈ O := by
  constructor
  · intro hx D hc
    exact generic_mem_of_closed_mem_interior π O D (hc.symm ▸ hx)
  · intro h
    by_contra hx
    obtain ⟨D, hc, he⟩ := (not_interior_iff_valuation π O x).mp hx
    exact he (h D hc)

/-- At a full fiber every obstruction can be chosen with a provably unliftable square. -/
theorem exists_unliftable_valuation (x : X) (hx : x ∈ fullFiberLocus π O)
    (hi : x ∉ fullFiberInterior π O) :
    ∃ D : ValuativeCommSq π, D.i₂ (closedPoint D.R) = x ∧
      D.i₁ (default : Spec (.of D.K)) ∉ O ∧ ¬ D.commSq.HasLift := by
  obtain ⟨D, hc, he⟩ := (not_interior_iff_valuation π O x).mp hi
  exact ⟨D, hc, he, no_lift_of_excluded_generic π O D (hc.symm ▸ hx) he⟩

end FLT.Mazur.SchemeOpenEnvelope
