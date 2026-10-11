/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertAcyclicParameterOpen
public import FLT.Mazur.LocalAcyclicCartierCriterion

/-!
# Recovery of the full Hilbert universal ideal on the acyclic open

The acyclic divisor constructed by unpointed descent equals the original
Hilbert universal family on the open parameter scheme. The equality holds
on full ideals and proves its finite locally free degree on every test.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite
open FLT.Mazur.FCurve FLT.Mazur.ClosedIdealCover
open FLT.Mazur.SchemePicard FLT.Mazur.CartierAbel
namespace FLT.Mazur.HilbertChart
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R]
  {Z : Scheme} (z : Z ⟶ Spec (.of R)) [IsProper z] [Flat z]
  [GeometricallyIntegral z] [SmoothOfRelativeDimension 1 z] (d : ℕ)

/-- The full original Hilbert divisor associated to a map into the acyclic open is acyclic. -/
def acyclicHilbertParameterDivisor (T : Over (Spec (.of R)))
    (k : T ⟶ acyclicHilbertTest z d) :
    AcyclicRankOneRelativeDivisor (pullback.snd z T.hom) :=
  relativeDivisorOfLocalAcyclic z T
    ((allAffineAmbientCharts z).parameterPicardDivisor d T
      (ampleHilbertParameterEquiv z d T (k ≫ acyclicHilbertArrow z d)))
    ((allAffineAmbientCharts z).parameterPicardIdeal_relative d T _).2
    (acyclicHilbert_map_mem z d T k)

/-- Unpointed descent recovers the independently constructed Hilbert divisor on every test. -/
theorem acyclicHilbertParameterDivisor_eq (T : Over (Spec (.of R)))
    (k : T ⟶ acyclicHilbertTest z d) :
    acyclicHilbertParameterDivisor z d T k =
      finiteTypeAcyclicDivisorMap z k (acyclicHilbertDivisor z d) := by
  apply finiteTypeUnpointedOpenDivisor_unique z _ (ampleHilbertAbelSection z d) k
  exact (ampleHilbertAbelSection_map z d T (k ≫ acyclicHilbertArrow z d)).symm

/-- Recovery identifies full ideals, preserving all nilpotents and multiplicities. -/
theorem acyclicHilbertParameterDivisor_ideal (T : Over (Spec (.of R)))
    (k : T ⟶ acyclicHilbertTest z d) :
    (allAffineAmbientCharts z).parameterPicardIdeal d T
        (ampleHilbertParameterEquiv z d T (k ≫ acyclicHilbertArrow z d)) =
      (acyclicHilbertDivisor z d).val.val.comap (relativeTotalMap z k) := by
  have h := congrArg (fun D ↦ D.val.val) (acyclicHilbertParameterDivisor_eq z d T k)
  exact h.trans (finiteTypeAcyclicDivisorMap_ideal z k (acyclicHilbertDivisor z d))

omit [Algebra.FiniteType ℤ R] [Flat z] [GeometricallyIntegral z]
  [SmoothOfRelativeDimension 1 z] in
/-- Exchanging the Hilbert fiber-product factors preserves the actual finite flat degree. -/
theorem hilbertPicardIdeal_degree (T : Over (Spec (.of R)))
    (p : (allAffineAmbientCharts z).GluedParameters d T.hom) :
    FiniteLocallyFreeDegree
      (((allAffineAmbientCharts z).parameterPicardIdeal d T p).subschemeι ≫
        pullback.snd z T.hom) d := by
  have H : IsPullback (pullbackSymmetry z T.hom).hom
      (pullback.snd z T.hom) (pullback.fst T.hom z) (𝟙 T.left) :=
    IsPullback.of_horiz_isIso ⟨by simp only [pullbackSymmetry_hom_comp_fst,
      Category.comp_id]⟩
  exact restriction_degree ((allAffineAmbientCharts z).parameterFamily d T.hom p).val
    _ H d ((allAffineAmbientCharts z).parameterFamily d T.hom p).property

/-- The original universal divisor on the acyclic parameter scheme has degree d. -/
theorem acyclicHilbertDivisor_degree :
    FiniteLocallyFreeDegree
      ((acyclicHilbertDivisor z d).val.val.subschemeι ≫
        pullback.snd z (acyclicHilbertTest z d).hom) d := by
  have h := acyclicHilbertParameterDivisor_ideal z d _ (𝟙 _)
  rw [relativeTotalMap_id, Scheme.IdealSheafData.comap_id] at h
  rw [← h]
  exact hilbertPicardIdeal_degree z d _ _

end FLT.Mazur.HilbertChart
