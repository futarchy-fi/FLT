/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OriginalBoundaryComparisonNeighborhood
public import FLT.Mazur.RelationComparisonEquation
public import FLT.Mazur.RelativeFrameEquationGeometry
public import FLT.Mazur.RelativeFrameRankPullback

/-!
# Full original boundary comparisons on higher-rank framed tests

Every complete frame of the original boundary source decomposes the actual
scalar comparison into disjoint full coordinate equations. The original
first-endpoint rank supplies completeness; the second rank is unrestricted.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RelativeOrderedTuples RingPairInvariantFlatScalars SchemeScalarPrincipalNeighborhood
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A B : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  [QuasiCompact p] (J : A.IdealSheafData) (hJ : J.comap p = J.comap q)
attribute [local instance] sourceAlgebra targetAlgebra originalBoundaryAlgebra
set_option quotPrecheck false
local notation "R" => invariants p.appTop.hom q.appTop.hom
local notation "f" => scalarMorphism (algebraMap R Γ(J.subscheme, ⊤))
local notation "P" => pullback.snd p J.subschemeι
local notation "Q" => InvariantIdealRelation.snd J p q hJ
local notation "E" => Over.mk P
local notation "c" => originalBoundaryComparison p q J hJ
local instance framedBoundaryOver_separated : IsSeparated (E).hom :=
  inferInstanceAs (IsSeparated P)
local instance framedBoundaryOver_etale : Etale (E).hom := inferInstanceAs (Etale P)
local instance framedBoundaryOver_compact : QuasiCompact (E).hom :=
  inferInstanceAs (QuasiCompact P)
local instance framedOriginalOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance framedOriginalOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance framedOriginalOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
variable (t : B ⟶ pullback
    (scalarMorphism (algebraMap (invariants p.appTop.hom q.appTop.hom) Γ(J.subscheme, ⊤)))
    (scalarMorphism (algebraMap (invariants p.appTop.hom q.appTop.hom) Γ(J.subscheme, ⊤))))
  (n : ℕ)
local notation "x" => t ≫ pullback.fst f f
local notation "y" => t ≫ pullback.snd f f
variable (a : Over.mk (t ≫ pullback.fst _ _) ⟶
    distinctScheme (Over.mk (pullback.snd p J.subschemeι)) (Fin n))
  (ht : Set.range (t ≫ pullback.fst _ _ ≫ J.subschemeι) ⊆ exactRank (Over.mk p) n)

include ht in
/-- The original first-endpoint rank makes the actual boundary frame complete. -/
theorem originalBoundary_frame_complete : Set.range a.left ⊆ completeLocus E (Fin n) := by
  apply frame_range_complete_of_rankAtMost E n a
  rintro _ ⟨z, rfl⟩
  exact ((exactRank_pullback_iff (Over.mk p) J.subschemeι (x z) n).mpr
    (ht ⟨z, rfl⟩)).2

/-- Coordinate equations decompose the entire original scalar comparison. -/
def originalBoundaryFramedComparisonIso :
    (∐ fun i : Fin n ↦ frameEquationChart E (Fin n) a Q y i) ≅ pullback c t :=
  (frameEquationIso E (Fin n) a Q y (originalBoundary_frame_complete J t n a ht)).trans
    (RelationComparisonEquation.iso P Q f c (pullback.lift_fst _ _ _)
      (pullback.lift_snd _ _ _) t).symm

/-- Every coordinate equation supplies an actual original comparison arrow. -/
def originalBoundaryFrameEquationMap (i : Fin n) :
    frameEquationChart E (Fin n) a Q y i ⟶ pullback c t :=
  frameEquationMap E (Fin n) a Q y i ≫
    (RelationComparisonEquation.iso P Q f c (pullback.lift_fst _ _ _)
      (pullback.lift_snd _ _ _) t).inv

omit [QuasiCompact p] [Etale p] in
/-- The constructed arrow keeps precisely the original coefficient on each equation chart. -/
@[reassoc] theorem originalBoundaryFrameEquationMap_snd (i : Fin n) :
    originalBoundaryFrameEquationMap J hJ t n a i ≫ pullback.snd c t =
      equalizer.ι
        (testSection E (Fin n) a i ≫ pullback.fst P x ≫ Q)
        (testSection E (Fin n) a i ≫ pullback.snd P x ≫ y) := by
  dsimp only [originalBoundaryFrameEquationMap, RelationComparisonEquation.iso]
  rw [Category.assoc, RelationComparisonEquation.fromEquation_snd]
  exact frameEquationMap_projection E (Fin n) a Q y i

/-- The coproduct decomposition is the assembled family of these actual original arrows. -/
@[reassoc] theorem originalBoundaryFramedComparisonIso_component (i : Fin n) :
    Sigma.ι (fun i : Fin n ↦ frameEquationChart E (Fin n) a Q y i) i ≫
      (originalBoundaryFramedComparisonIso J hJ t n a ht).hom =
        originalBoundaryFrameEquationMap J hJ t n a i := by
  change _ ≫ frameEquationComparison E (Fin n) a Q y ≫ _ = _
  rw [frameEquationComparison_component_assoc]
  rfl

end FLT.Mazur.EquivalenceRelationOrderedFrames
