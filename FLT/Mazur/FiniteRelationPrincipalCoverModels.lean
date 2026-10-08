/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteRelationCoverDescent
public import FLT.Mazur.FiniteRelationLocalizationSpectrum
public import FLT.Mazur.PrincipalOpenIntersectionModels
public import Mathlib.AlgebraicGeometry.Cover.Open

/-!
# Finite principal covers on a tail of the model system

A principal cover of the full quotient gives covers on every sufficiently
large finite-relation model. The cover components are the localized stages,
so their transition and projection squares are the cartesian squares already
constructed. Their intersections are the models obtained by inverting products.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.FiniteRelationLocalization

universe u v

variable (R : Type u) [CommRing R] {P : Type u} [CommRing P] [Algebra R P]
  (I : Ideal P) {ι : Type v} (r : ι → P)

/-- A finite principal cover holds on an entire tail of the relation system. -/
theorem exists_principal_cover_tail [Finite ι] (s : Finset I)
    (h : (⨆ i, PrimeSpectrum.basicOpen (Ideal.Quotient.mk I (r i))) = ⊤) :
    ∃ t : Finset I, s ≤ t ∧ ∀ q : Finset I, t ≤ q →
      (⨆ i, PrimeSpectrum.basicOpen
        (Ideal.Quotient.mk (FiniteRelationModel.relations I q) (r i))) = ⊤ := by
  classical
  let _ := Fintype.ofFinite ι
  obtain ⟨t, hst, c, hc, _⟩ := FiniteRelationModel.exists_principal_cover_stage (R := P) I s
    (fun i ↦ Ideal.Quotient.mk _ (r i))
    (by simpa only [FiniteRelationModel.toQuotient_mk] using h)
  refine ⟨t, hst, fun q htq ↦ ?_⟩
  apply PrimeSpectrum.iSup_basicOpen_eq_top_iff.mpr
  apply Ideal.eq_top_of_isUnit_mem _ ?_ isUnit_one
  apply Ideal.mem_span_range_iff_exists_fun.mpr
  refine ⟨fun i ↦ FiniteRelationModel.transition P I htq (c i), ?_⟩
  have he := congrArg (FiniteRelationModel.transition P I htq) hc
  simpa only [map_sum, map_mul, map_one, FiniteRelationModel.transition_mk] using he

/-- The actual finite affine cover at a stage where the denominators cover. -/
def principalCover (s : Finset I)
    (h : (⨆ i, PrimeSpectrum.basicOpen
      (Ideal.Quotient.mk (FiniteRelationModel.relations I s) (r i))) = ⊤) :
    (Spec (.of (FiniteRelationModel.Stage I s))).AffineOpenCover :=
  Scheme.affineOpenCoverOfSpanRangeEqTop
    (fun i ↦ Ideal.Quotient.mk (FiniteRelationModel.relations I s) (r i))
    (PrimeSpectrum.iSup_basicOpen_eq_top_iff.mp h)

/-- Cover maps are the explicit principal-open inclusions used in the model system. -/
theorem principalCover_f (s : Finset I)
    (h : (⨆ i, PrimeSpectrum.basicOpen
      (Ideal.Quotient.mk (FiniteRelationModel.relations I s) (r i))) = ⊤) (i : ι) :
    (principalCover I r s h).f i = PrincipalLocalizationSquare.inclusion
      (Ideal.Quotient.mk (FiniteRelationModel.relations I s) (r i)) := rfl

/-- Every cover component remains locally finitely presented over the original base. -/
instance principalCover_locallyOfFinitePresentation [Algebra.FinitePresentation R P]
    (s : Finset I) (h : (⨆ i, PrimeSpectrum.basicOpen
      (Ideal.Quotient.mk (FiniteRelationModel.relations I s) (r i))) = ⊤) (i : ι) :
    LocallyOfFinitePresentation
      ((principalCover I r s h).f i ≫ FiniteRelationModel.stageStructure R I s) := by
  change LocallyOfFinitePresentation
    (PrincipalLocalizationSquare.inclusion
      (Ideal.Quotient.mk (FiniteRelationModel.relations I s) (r i)) ≫
      FiniteRelationModel.stageStructure R I s)
  infer_instance

end FLT.Mazur.FiniteRelationLocalization
