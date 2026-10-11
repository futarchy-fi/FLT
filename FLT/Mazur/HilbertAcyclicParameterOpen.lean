/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AmpleHilbertFunctorRepresentation
public import FLT.Mazur.HilbertParameterAbelClass
public import FLT.Mazur.UnpointedAbelOpenFiberRepresentation

/-!
# An actual acyclic open inside the Hilbert parameter scheme

The Abel section of the constructed Hilbert universal family cuts out an
actual open parameter scheme. Its maps classify precisely the parameters
whose full divisor has locally acyclic Picard class on the original test.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite
open FLT.Mazur.SchemePicard FLT.Mazur.CartierAbel
namespace FLT.Mazur.HilbertChart
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R]
  {Z : Scheme} (z : Z ⟶ Spec (.of R)) [IsProper z] [Flat z]
  [GeometricallyIntegral z] [SmoothOfRelativeDimension 1 z] (d : ℕ)

/-- The Abel section of the full universal family on the actual Hilbert scheme. -/
def ampleHilbertAbelSection :
    (relativeFppfSheaf z).obj.obj (op (ampleHilbertTest z d)) :=
  (allAffineAmbientCharts z).parameterAbelClass d (ampleHilbertTest z d)
    (ampleHilbertParameterEquiv z d _ (𝟙 _))

omit [Algebra.FiniteType ℤ R] [Flat z] [GeometricallyIntegral z] in
/-- Restriction of the universal section is the Abel class of the actual parameter divisor. -/
lemma ampleHilbertAbelSection_map (T : Over (Spec (.of R)))
    (k : T ⟶ ampleHilbertTest z d) :
    (relativeFppfSheaf z).obj.map k.op (ampleHilbertAbelSection z d) =
      (allAffineAmbientCharts z).parameterAbelClass d T
        (ampleHilbertParameterEquiv z d T k) := by
  have h := (allAffineAmbientCharts z).parameterAbelClass_natural d k
    (ampleHilbertParameterEquiv z d _ (𝟙 _))
  simpa only [ampleHilbertAbelSection, ampleHilbertParameterEquiv, Equiv.coe_fn_mk,
    Over.id_left, Category.comp_id] using h.symm

/-- The cohomological open of the actual degree-d Hilbert parameter scheme. -/
def acyclicHilbertOpen : (ampleHilbertTest z d).left.Opens :=
  finiteTypeUnpointedFppfAcyclicOpen z _ (ampleHilbertAbelSection z d)

/-- The acyclic Hilbert parameter scheme retains the original map to the coefficient base. -/
def acyclicHilbertTest : Over (Spec (.of R)) :=
  finiteTypeUnpointedFppfOpenTest z _ (ampleHilbertAbelSection z d)

/-- The actual open inclusion from acyclic parameters into all degree-d parameters. -/
def acyclicHilbertArrow : acyclicHilbertTest z d ⟶ ampleHilbertTest z d :=
  finiteTypeUnpointedFppfOpenArrow z _ (ampleHilbertAbelSection z d)

/-- This parameter inclusion is an actual scheme open immersion. -/
instance : IsOpenImmersion (acyclicHilbertArrow z d).left :=
  inferInstanceAs (IsOpenImmersion (acyclicHilbertOpen z d).ι)

/-- An arbitrary parameter factors through the open exactly on its local acyclic locus. -/
theorem acyclicHilbert_represents (T : Over (Spec (.of R)))
    (k : T ⟶ ampleHilbertTest z d) :
    (allAffineAmbientCharts z).parameterAbelClass d T
        (ampleHilbertParameterEquiv z d T k) ∈
        (localGeometricAcyclicFppfSubfunctor z).obj (op T) ↔
      ∃! l : T ⟶ acyclicHilbertTest z d, l ≫ acyclicHilbertArrow z d = k := by
  rw [← ampleHilbertAbelSection_map]
  exact finiteTypeUnpointedFppfAcyclicOpen_represents_over z k (ampleHilbertAbelSection z d)

/-- Every map to the actual parameter open gives an acyclic full-divisor class. -/
theorem acyclicHilbert_map_mem (T : Over (Spec (.of R)))
    (k : T ⟶ acyclicHilbertTest z d) :
    (allAffineAmbientCharts z).parameterAbelClass d T
        (ampleHilbertParameterEquiv z d T (k ≫ acyclicHilbertArrow z d)) ∈
      (localGeometricAcyclicFppfSubfunctor z).obj (op T) := by
  apply (acyclicHilbert_represents z d T _).mpr
  refine ⟨k, rfl, ?_⟩
  intro l hl
  apply Over.OverMorphism.ext
  exact (cancel_mono (acyclicHilbertArrow z d).left).mp (congrArg Over.Hom.left hl)

/-- The actual universal acyclic divisor carried by the open parameter scheme. -/
def acyclicHilbertDivisor :
    AcyclicRankOneRelativeDivisor (pullback.snd z (acyclicHilbertTest z d).hom) :=
  finiteTypeUnpointedOpenDivisor z _ (ampleHilbertAbelSection z d)

/-- Its class is the actual Hilbert universal Abel section restricted to the parameter open. -/
theorem acyclicHilbertDivisor_class :
    relativeFppfClass z _ (abel _ (acyclicHilbertDivisor z d).val) =
      (allAffineAmbientCharts z).parameterAbelClass d (acyclicHilbertTest z d)
        (ampleHilbertParameterEquiv z d _ (acyclicHilbertArrow z d)) := by
  exact (finiteTypeUnpointedOpenDivisor_class z _ (ampleHilbertAbelSection z d)).trans
    (ampleHilbertAbelSection_map z d _ (acyclicHilbertArrow z d))

end FLT.Mazur.HilbertChart
