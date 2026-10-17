/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertNormalizedCompleteFiberSplit
public import FLT.Mazur.EquivalenceRelationCompleteThickenings

/-!
# Constructed complete infinitesimal sources over every original Hilbert point

All original endpoints, including those outside the dense open rank strata,
lift to constructed closed complete thickenings of every order. Their full
original two-endpoint relation comparison retains each power-quotient scheme.
No extension from these stages to an original open domain is asserted.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve EquivalenceRelationNormalizedFrames
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [IsAffine V.left] [Etale V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} [IsAffine A.left]
  (k : A ⟶ variableHilbertTest f d V) [IsOpenImmersion k.left]
local notation "p" => Over.Hom.left (fst f hL d V c k)
local notation "q" => Over.Hom.left (snd f hL d V c k)
local notation "e" => fullRelationSchemeEquivalence f hL d V c k

/-- The actual complete normalized infinitesimal source of each positive order. -/
def normalizedCompleteThickening (n : ℕ) (o : Fin n) (j : ℕ) : Scheme :=
  completeThickening («p» := p) («q» := q) (Fin n) o j

/-- Every original Hilbert endpoint occurs on a constructed stage of every order. -/
theorem exists_normalizedCompleteThickening_lift (x : A.left) (j : ℕ) :
    ∃ (n : ℕ) (o : Fin n) (y : normalizedCompleteThickening f hL d V c k n o j),
      (completeThickeningInclusion (Fin n) o j ≫ first p q (Fin n) o) y = x :=
  exists_completeThickening_lift e x j

/-- On a constructed stage the full original Hilbert relation has the permutation comparison. -/
def normalizedCompleteThickeningRelationIso (n : ℕ) (o : Fin n) (j : ℕ)
    {B : Scheme} (v : B ⟶ source p q (Fin n) o) :
    SourceRestriction.comparisonSource e (completeThickeningInclusion (Fin n) o j) v ≅
      SourceRestriction.relation (completeThickeningInclusion (Fin n) o j) v :=
  completeThickeningRelationIso (Fin n) o e j v

/-- The entire original coefficient arrow survives on each infinitesimal stage. -/
@[reassoc] theorem normalizedCompleteThickeningRelationIso_inv_arrow
    (n : ℕ) (o : Fin n) (j : ℕ) {B : Scheme} (v : B ⟶ source p q (Fin n) o) :
    (normalizedCompleteThickeningRelationIso f hL d V c k n o j v).inv ≫
      pullback.fst (relationComparison e (Fin n) o)
        (SourceRestriction.original (completeThickeningInclusion (Fin n) o j) v) ≫
          relationComparison e (Fin n) o ≫ relationArrow p q (Fin n) o =
            SourceRestriction.arrow (completeThickeningInclusion (Fin n) o j) v :=
  completeThickeningRelationIso_inv_arrow (Fin n) o e j v

end FLT.Mazur.HilbertChart.AffineRestriction
