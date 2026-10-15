/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ValuativeEnvelopeInterior
public import FLT.Mazur.ValuativePullbackSquare
public import FLT.Mazur.NoetherianEnvelopeGenericInterior

/-!
# Residual boundaries force nonextension of the original translation

The full Cartesian envelope transports its valuation obstruction to the
original translation over the unchanged coefficient scheme. At a full fiber
the coefficient specialization is strict. This is an actual unliftable
scheme square, rather than an inequality of projected topological points.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing TopologicalSpace
namespace FLT.Mazur.OriginalTranslationValuation
open SchemeOpenEnvelope ValuativePullbackSquare
universe u
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme.{u}} (A V : Over S)
local notation "π" => Over.Hom.left (prod.fst : prod A V ⟶ A)

/-- Transport the valuation test through the entire original independent product. -/
def translationSquare (D : ValuativeCommSq π) : ValuativeCommSq V.hom :=
  baseSquare (Over.isPullback_of_binaryFan_isLimit _ (prodIsProd A V)) D

/-- Its generic coefficient is the actual original source coefficient. -/
theorem generic_coefficient (D : ValuativeCommSq π) :
    V.hom ((translationSquare A V D).i₁ (default : Spec (.of D.K))) =
      A.hom (π (D.i₁ (default : Spec (.of D.K)))) := by
  have hw := (Over.isPullback_of_binaryFan_isLimit _ (prodIsProd A V)).w
  exact congrArg (fun g : (prod A V).left ⟶ S ↦
    g (D.i₁ (default : Spec (.of D.K)))) hw.symm

/-- No lift of the envelope means no lift of the original translation with this same test. -/
theorem translation_hasLift_iff (D : ValuativeCommSq π) :
    (translationSquare A V D).commSq.HasLift ↔ D.commSq.HasLift :=
  hasLift_iff (Over.isPullback_of_binaryFan_isLimit _ (prodIsProd A V)) D

variable [Etale V.hom] [QuasiCompact V.hom] (O : (prod A V).left.Opens)

/-- Every excluded specialization produces a nonextendable original translation coordinate. -/
theorem of_excluded_specialization (x : A.left) (hx : x ∈ fullFiberLocus π O)
    (e : (prod A V).left) (he : e ∉ O) (hs : π e ⤳ x) :
    ∃ D : ValuativeCommSq π, D.i₂ (closedPoint D.R) = x ∧
      D.i₁ (default : Spec (.of D.K)) = e ∧
      ¬ (translationSquare A V D).commSq.HasLift ∧
      V.hom ((translationSquare A V D).i₁ (default : Spec (.of D.K))) ⤳ A.hom x ∧
      V.hom ((translationSquare A V D).i₁ (default : Spec (.of D.K))) ≠ A.hom x := by
  obtain ⟨D, hg, hc⟩ := SpecializationValuationSquare.exists_square π e x hs
  refine ⟨D, hc, hg, ?_, ?_, ?_⟩
  · intro hl
    exact no_lift_of_excluded_generic π O D (hc.symm ▸ hx) (hg ▸ he)
      ((translation_hasLift_iff A V D).mp hl)
  · rw [generic_coefficient, hg]
    exact hs.map A.hom.continuous
  · rw [generic_coefficient, hg]
    exact EnvelopeVerticalGenerizations.excluded_specialization_base_ne A V O hx e he hs

variable [NoetherianSpace (prod A V).left]

/-- A noninterior full fiber constructs an original translation obstruction over a strict
coefficient specialization, with no domain or reducedness assumption on the coefficient base. -/
theorem exists_of_not_interior (x : A.left) (hx : x ∈ fullFiberLocus π O)
    (hi : x ∉ fullFiberInterior π O) :
    ∃ D : ValuativeCommSq π, D.i₂ (closedPoint D.R) = x ∧
      D.i₁ (default : Spec (.of D.K)) ∉ O ∧
      ¬ (translationSquare A V D).commSq.HasLift ∧
      V.hom ((translationSquare A V D).i₁ (default : Spec (.of D.K))) ⤳ A.hom x ∧
      V.hom ((translationSquare A V D).i₁ (default : Spec (.of D.K))) ≠ A.hom x := by
  obtain ⟨D, hc, he⟩ := (not_interior_iff_valuation π O x).mp hi
  have hs := SpecializationValuationSquare.specializes π D
  rw [hc] at hs
  obtain ⟨D', hc', hg', hn, hspec, hne⟩ :=
    of_excluded_specialization A V O x hx _ he hs
  exact ⟨D', hc', hg' ▸ he, hn, hspec, hne⟩

end FLT.Mazur.OriginalTranslationValuation
