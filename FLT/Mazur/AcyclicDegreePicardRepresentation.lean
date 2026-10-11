/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AcyclicHilbertDivisorRepresentation

/-!
# A represented degree-d subfunctor of the original Picard sheaf

The actual acyclic Hilbert open represents the Picard-sheaf sections
admitting a full acyclic degree-d divisor. This supplies genuine parameter
geometry and a universal ideal without asserting that these loci cover Picard.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite
open FLT.Mazur.FCurve FLT.Mazur.SchemePicard
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.CartierAbel
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R]
  {X : Scheme} (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  (d : ℕ)

/-- Actual Picard-sheaf sections represented by full acyclic divisors of degree d. -/
def acyclicDegreePicardSubfunctor :
    Subfunctor ((relativeFppfSheaf f).obj ⋙ forget CommGrpCat) where
  obj T := {s | ∃ D : (acyclicDivisorDegreeSubfunctor f d).toFunctor.obj T,
    relativeFppfClass f T.unop (abel (pullback.snd f T.unop.hom) D.val.val) = s}
  map {T U} g s hs := by
    obtain ⟨D, rfl⟩ := hs
    refine ⟨(acyclicDivisorDegreeSubfunctor f d).toFunctor.map g D, ?_⟩
    change relativeFppfClass f U.unop
      (abel _ (finiteTypeAcyclicDivisorMap f g.unop D.val).val) = _
    rw [finiteTypeAcyclicDivisorMap_class, ← relativeFppfClass_naturality]
    rfl

/-- The full degree-d Abel correspondence retains the actual original Picard-sheaf class. -/
def acyclicDegreePicardEquiv (T : Over (Spec (.of R))) :
    (acyclicDivisorDegreeSubfunctor f d).toFunctor.obj (op T) ≃
      (acyclicDegreePicardSubfunctor f d).toFunctor.obj (op T) :=
  Equiv.ofBijective (fun D ↦ ⟨relativeFppfClass f T (abel _ D.val.val), D, rfl⟩) ⟨by
    intro D E h
    apply Subtype.ext
    exact finiteTypeAcyclicAbelFppf_injective f T (congrArg Subtype.val h), by
    intro s
    obtain ⟨D, hD⟩ := s.property
    exact ⟨D, Subtype.ext hD⟩⟩

/-- Degree-d full Abel is natural for arbitrary maps of original test schemes. -/
def acyclicDegreePicardIso :
    (acyclicDivisorDegreeSubfunctor f d).toFunctor ⋙ uliftFunctor.{1} ≅
      (acyclicDegreePicardSubfunctor f d).toFunctor :=
  NatIso.ofComponents (fun T ↦
    (Equiv.ulift.trans (acyclicDegreePicardEquiv f d T.unop)).toIso)
    (fun {T U} g ↦ by
      apply ConcreteCategory.hom_ext
      intro D
      apply Subtype.ext
      exact (congrArg (relativeFppfClass f U.unop)
        (finiteTypeAcyclicDivisorMap_class f g.unop D.down.val)).trans
        (relativeFppfClass_naturality f g.unop _).symm)

/-- Every member lies in the original locally defined acyclic Picard subsheaf. -/
theorem acyclicDegreePicard_le_local :
    acyclicDegreePicardSubfunctor f d ≤ localGeometricAcyclicFppfSubfunctor f := by
  rintro T s ⟨D, rfl⟩
  exact (relativeDivisor_localAcyclic_iff f T.unop D.val.val D.val.property.1).mpr
    D.val.property.2

end FLT.Mazur.CartierAbel

namespace FLT.Mazur.HilbertChart
open CartierAbel
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R]
  {X : Scheme} (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] (d : ℕ) {L : X.Modules} (hL : AmpleLineBundle L)

/-- The actual Hilbert open represents the degree-d locus inside the original Picard sheaf. -/
def acyclicHilbertPicardIso :
    yoneda.obj (acyclicHilbertTest f d) ⋙ uliftFunctor.{1} ≅
      (acyclicDegreePicardSubfunctor f d).toFunctor :=
  Functor.isoWhiskerRight (acyclicHilbertDivisorIso f d hL) uliftFunctor.{1} ≪≫
    acyclicDegreePicardIso f d

/-- The represented section is the Abel class of the actual pulled-back Hilbert divisor. -/
lemma acyclicHilbertPicardIso_class (T : Over (Spec (.of R)))
    (k : T ⟶ acyclicHilbertTest f d) :
    ((acyclicHilbertPicardIso f d hL).hom.app (op T) (ULift.up k)).val =
      (allAffineAmbientCharts f).parameterAbelClass d T
        (ampleHilbertParameterEquiv f d T (k ≫ acyclicHilbertArrow f d)) := rfl

include hL in
/-- The actual parameter map into the original Picard sheaf is injective on every test. -/
theorem acyclicHilbertAbel_injective (T : Over (Spec (.of R))) :
    Function.Injective (fun k : T ⟶ acyclicHilbertTest f d ↦
      (allAffineAmbientCharts f).parameterAbelClass d T
        (ampleHilbertParameterEquiv f d T (k ≫ acyclicHilbertArrow f d))) := by
  intro k l h
  have he : ((acyclicHilbertPicardIso f d hL).hom.app (op T) (ULift.up k)) =
      ((acyclicHilbertPicardIso f d hL).hom.app (op T) (ULift.up l)) := Subtype.ext h
  have hk := ((acyclicHilbertPicardIso f d hL).app (op T)).toEquiv.injective he
  exact congrArg ULift.down hk

end FLT.Mazur.HilbertChart
