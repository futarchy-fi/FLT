/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AcyclicHilbertPicardTestOverlap

/-!
# Actual Hilbert presentations of the degree restrictions of a full divisor

The canonical degree opens cover the original test. On each, the full
restricted ideal is the pullback of the original Hilbert universal ideal,
and its Hilbert class is the restriction of the original Abel class.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart
open CartierAbel FCurve SchemePicard
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R]
  {X : Scheme} (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {B : X.Modules} (hB : AmpleLineBundle B)
  (T : Over (Spec (.of R))) (D : AcyclicRankOneRelativeDivisor (pullback.snd f T.hom))

/-- A genuine small open cover, indexed by the actual finite divisor degree. -/
def divisorDegreePresentationCover : T.left.OpenCover :=
  T.left.openCoverOfIsOpenCover (acyclicDivisorDegreeOpen f T D)
    (iSup_acyclicDivisorDegreeOpen f T D)

/-- The actual Hilbert parameter of the full divisor on its degree open. -/
def divisorDegreeParameter (d : ℕ) :
    acyclicDivisorDegreeTest f T D d ⟶ acyclicHilbertTest f d :=
  (acyclicHilbertDegreeEquiv f d hB _).symm
    ⟨finiteTypeAcyclicDivisorMap f (acyclicDivisorDegreeArrow f T D d) D,
      acyclicDivisorDegreeArrow_mem f T D d⟩

/-- The parameter recovers the full original restricted divisor. -/
theorem divisorDegreeParameter_divisor (d : ℕ) :
    acyclicHilbertParameterDivisor f d _ (divisorDegreeParameter f hB T D d) =
      finiteTypeAcyclicDivisorMap f (acyclicDivisorDegreeArrow f T D d) D :=
  congrArg Subtype.val ((acyclicHilbertDegreeEquiv f d hB _).apply_symm_apply _)

/-- Full universal-ideal pullback agrees with the full original divisor comap. -/
theorem divisorDegreeParameter_ideal (d : ℕ) :
    (acyclicHilbertDivisor f d).val.val.comap
        (relativeTotalMap f (divisorDegreeParameter f hB T D d)) =
      D.val.val.comap (relativeTotalMap f (acyclicDivisorDegreeArrow f T D d)) := by
  rw [← acyclicHilbertParameterDivisor_ideal]
  change (acyclicHilbertParameterDivisor f d _ _).val.val = _
  rw [divisorDegreeParameter_divisor, finiteTypeAcyclicDivisorMap_ideal]

/-- The parameter retains exactly the original restricted Abel class. -/
theorem divisorDegreeParameter_class (d : ℕ) :
    acyclicHilbertPicardPoint f d hB _ (divisorDegreeParameter f hB T D d) =
      (relativeFppfSheaf f).obj.map (acyclicDivisorDegreeArrow f T D d).op
        (relativeFppfClass f T (abel _ D.val)) := by
  change relativeFppfClass f _
    (abel _ (acyclicHilbertParameterDivisor f d _ _).val) = _
  rw [divisorDegreeParameter_divisor, finiteTypeAcyclicDivisorMap_class,
    relativeFppfClass_naturality]

end FLT.Mazur.HilbertChart
