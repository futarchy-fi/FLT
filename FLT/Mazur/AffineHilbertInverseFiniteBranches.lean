/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertFiniteBranchAtlas

/-!
# Inversion of the constructed finite branches

Inversion keeps the actual finite etale coefficient cover and reverses both
original endpoints. The inverse branches cover the entire original relation.
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
local notation "Z" => EtaleFiniteBranchAtlas.source p
local notation "a" => EtaleFiniteBranchAtlas.original p

/-- Invert the actual relation arrow, keeping its constructed affine source. -/
def inverseFiniteBranch (r : (D).left) : Z r ⟶ D :=
  a r ≫ (swapIso f hL d V c k).hom

instance inverseFiniteBranch_etale (r : (D).left) :
    Etale (inverseFiniteBranch f hL d V c k r).left := by
  let e := (Over.forget _).mapIso (swapIso f hL d V c k)
  exact inferInstanceAs (Etale ((a r).left ≫ e.hom))

/-- The first inverse endpoint is the independent second original endpoint. -/
@[reassoc]
theorem inverseFiniteBranch_fst (r : (D).left) :
    inverseFiniteBranch f hL d V c k r ≫ p = a r ≫ q := by
  exact (Category.assoc _ _ _).trans
    (congrArg (fun g ↦ a r ≫ g) (equivalence f hL d V c k).symmetry₁)

/-- The same finite etale surjection now lies over the second endpoint. -/
@[reassoc]
theorem inverseFiniteBranch_snd (r : (D).left) :
    inverseFiniteBranch f hL d V c k r ≫ q =
      EtaleFiniteBranchAtlas.projection p r ≫ EtaleFiniteBranchAtlas.base p r := by
  rw [inverseFiniteBranch, Category.assoc]
  change a r ≫ (equivalence f hL d V c k).s ≫ q = _
  rw [(equivalence f hL d V c k).symmetry₂, EtaleFiniteBranchAtlas.condition]

/-- Inversion of the branches still covers every original arrow. -/
theorem inverseFiniteBranch_covers (r : (D).left) :
    ∃ (i : (D).left) (z : (Z i).left),
      (inverseFiniteBranch f hL d V c k i).left z = r := by
  let e := (Over.forget _).mapIso (swapIso f hL d V c k)
  obtain ⟨z, hz⟩ := EtaleFiniteBranchAtlas.original_covers p (e.inv r)
  refine ⟨e.inv r, z, ?_⟩
  change e.hom ((a (e.inv r)).left z) = r
  rw [hz]
  exact congrArg (fun g : (D).left ⟶ (D).left ↦ g r) e.inv_hom_id

/-- The inverse branches form an actual etale cover of the full relation. -/
def inverseFiniteBranchCover : Scheme.Cover.{0} Scheme.etalePrecoverage (D).left :=
  Scheme.Cover.mkOfCovers (P := @Etale) (D).left
    (fun r ↦ (Z r).left) (fun r ↦ (inverseFiniteBranch f hL d V c k r).left)
    (inverseFiniteBranch_covers f hL d V c k) (fun _ ↦ inferInstance)

end FLT.Mazur.HilbertChart.AffineRestriction
