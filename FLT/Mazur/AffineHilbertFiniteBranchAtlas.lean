/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertFiniteBranches
public import FLT.Mazur.EtaleFiniteBranchAtlas
public import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-!
# An actual finite-branch atlas of the full original Hilbert relation

The jointly covering branches retain both original endpoint maps. Each has
an affine coefficient neighborhood and an actual finite etale surjection.
The resulting covering sieve is on the full original relation, including
arrows with distinct translation-base coordinates.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [Etale V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} [IsAffine A.left]
  (k : A ⟶ variableHilbertTest f d V) [IsOpenImmersion k.left]
local notation "D" => relation f hL d V c k
local notation "p" => fst f hL d V c k
local notation "q" => snd f hL d V c k
local notation "s" => sectionAt f hL d V c k
local notation "Z" => EtaleFiniteBranchAtlas.source p
local notation "a" => EtaleFiniteBranchAtlas.original p
local notation "t" => EtaleFiniteBranchAtlas.projection p
local notation "b" => EtaleFiniteBranchAtlas.base p

/-- An actual etale covering family of the entire original restricted relation. -/
def finiteBranchEtaleCover : Scheme.Cover.{0} Scheme.etalePrecoverage (D).left :=
  EtaleFiniteBranchAtlas.cover p

/-- The same constructed affine branches are an actual original fppf covering family. -/
def finiteBranchFppfCover : Scheme.Cover.{0} Scheme.fppfPrecoverage (D).left :=
  Scheme.Cover.mkOfCovers (P := @Flat ⊓ @LocallyOfFinitePresentation) (D).left
    (fun r ↦ (Z r).left) (fun r ↦ (a r).left)
    (fun r ↦ ⟨r, EtaleFiniteBranchAtlas.original_covers p r⟩)
    (fun _ ↦ ⟨inferInstance, inferInstance⟩)

/-- The original relative fppf site sees a covering sieve on the FULL relation. -/
theorem finiteBranch_covering : Sieve.ofArrows Z a ∈
    (Scheme.fppfTopology.over (Spec (.of R))) D := by
  rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
  exact Precoverage.generate_mem_toGrothendieck (finiteBranchFppfCover f hL d V c k).mem₀

/-- Each branch retains its actual original first endpoint scheme morphism. -/
@[reassoc]
theorem finiteBranch_fst (r : (D).left) : a r ≫ p = t r ≫ b r :=
  EtaleFiniteBranchAtlas.condition p r

/-- The second endpoint is etale too, and keeps its independent original coordinate. -/
instance finiteBranch_snd_etale (r : (D).left) : Etale (a r ≫ q).left :=
  inferInstanceAs (Etale ((a r).left ≫ (q).left))

/-- On every atlas member the second original Picard class comes from its coefficient base. -/
theorem finiteBranch_other_class (r : (D).left) :
    (relativeFppfSheaf f).obj.map (a r ≫ q).op s =
      (relativeFppfSheaf f).obj.map (t r).op ((relativeFppfSheaf f).obj.map (b r).op s) :=
  finite_branch_other_class f hL d V c k (b r) (t r) (a r)
    (finiteBranch_fst f hL d V c k r)

end FLT.Mazur.HilbertChart.AffineRestriction
