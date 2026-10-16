/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertDerivedNoetherianRelation
public import FLT.Mazur.HilbertNormalizedFrameAction
public import FLT.Mazur.EquivalenceRelationNormalizedFrameCover
public import FLT.Mazur.EquivalenceRelationNormalizedActionRelation

/-!
# Normalized covers and the full original Hilbert relation

The normalized frame maps give an actual etale cover of the original Hilbert
source. For each size and distinguished label, the permutation relation embeds
openly in the full original relation on normalized frames, with a scheme-level
identification on its open image. Complete geometric pairs belong to this image.
A compatible source restriction making the comparison exhaustive is still needed.
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

/-- Actual normalized full-relation frames form an etale cover of the Hilbert source. -/
def normalizedFullRelationCover : Scheme.Cover (Scheme.precoverage @Etale) A.left :=
  normalizedFramesCover e

variable (n : ℕ) (o : Fin n)

/-- The normalized original first endpoint is etale. -/
instance normalizedFullRelationFirst_etale :
    Etale (normalizedFullRelationFirst f hL d V c k n o) := first_etale e (Fin n) o

/-- The whole original Hilbert relation on two independent normalized frames. -/
def normalizedOriginalRelation : Scheme := fullRelation p q (Fin n) o

/-- The exact open image of the finite permutation relation inside the original relation. -/
def normalizedOriginalActionOpen : (normalizedOriginalRelation f hL d V c k n o).Opens :=
  actionRelationOpen e (Fin n) o

/-- The original relation on this open image is the actual permutation relation as schemes. -/
def normalizedOriginalActionIso :
    permutationRelation («p» := p) («q» := q) (Fin n) o ≅
      (normalizedOriginalActionOpen f hL d V c k n o).toScheme :=
  actionRelationIso e (Fin n) o

/-- The comparison retains its actual original relation morphism. -/
@[reassoc] theorem normalizedOriginalActionIso_inclusion :
    (normalizedOriginalActionIso f hL d V c k n o).hom ≫
      (normalizedOriginalActionOpen f hL d V c k n o).ι =
        relationComparison e (Fin n) o := actionRelationIso_inclusion e (Fin n) o

/-- Every original related pair of complete frames factors through the scheme comparison. -/
theorem normalizedOriginalAction_complete {K : Type} [Field K]
    (z : Spec (.of K) ⟶ normalizedOriginalRelation f hL d V c k n o)
    (h₁ : Complete (Fin n) o (z ≫ relationFirst p q (Fin n) o))
    (h₂ : Complete (Fin n) o (z ≫ relationSecond p q (Fin n) o)) :
    ∃ w : Spec (.of K) ⟶ permutationRelation («p» := p) («q» := q) (Fin n) o,
      w ≫ relationComparison e (Fin n) o = z :=
  complete_factors_relationComparison e (Fin n) o z h₁ h₂

end FLT.Mazur.HilbertChart.AffineRestriction
