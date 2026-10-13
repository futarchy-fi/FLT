/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertInvariantAffineModel

/-!
# The full invariant affine candidate preserves relative factorizations

The affine universal property holds over the original coefficient scheme.
The descended arrows retain both the entire source map and the specified
structural morphism. No quotient effectivity assumption is introduced.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R)))
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} (k : A ⟶ variableHilbertTest f d V)
local notation "p" => fst f hL d V c k
local notation "q" => snd f hL d V c k
local notation "M" => invariantAffineModel f hL d V c k
local notation "v" => invariantAffineProjection f hL d V c k
variable {Y : Over (Spec (.of R))} [IsAffine Y.left]

/-- The constructed affine factorization retains the original structural coefficient morphism. -/
def invariantAffineDescend (g : A ⟶ Y) (hg : p ≫ g = q ≫ g) : M ⟶ Y :=
  Over.homMk (SchemeRelationInvariantSpectrum.descend (p).left (q).left g.left
    (congrArg Over.Hom.left hg)) (by
      apply SchemeRelationInvariantSpectrum.affine_hom_ext (p).left (q).left
      rw [← Category.assoc, SchemeRelationInvariantSpectrum.projection_descend]
      exact g.w.trans (SchemeRelationInvariantSpectrum.projection_descend
        (p).left (q).left A.hom _).symm)

/-- The entire relative map, including its sheaf pullback, is the original map. -/
@[reassoc]
theorem invariantAffineProjection_descend (g : A ⟶ Y) (hg : p ≫ g = q ≫ g) :
    v ≫ invariantAffineDescend f hL d V c k g hg = g := by
  apply Over.OverMorphism.ext
  exact SchemeRelationInvariantSpectrum.projection_descend (p).left (q).left g.left _

/-- The original parameter source determines relative maps to any affine target. -/
theorem invariantAffine_relative_hom_ext {g h : M ⟶ Y} (he : v ≫ g = v ≫ h) : g = h := by
  apply Over.OverMorphism.ext
  exact SchemeRelationInvariantSpectrum.affine_hom_ext (p).left (q).left
    (congrArg Over.Hom.left he)

/-- The candidate is the coequalizer for affine relative test schemes over the original base. -/
theorem invariantAffine_existsUnique_relative (g : A ⟶ Y) (hg : p ≫ g = q ≫ g) :
    ∃! h : M ⟶ Y, v ≫ h = g :=
  ⟨invariantAffineDescend f hL d V c k g hg,
    invariantAffineProjection_descend f hL d V c k g hg,
    fun _ he ↦ invariantAffine_relative_hom_ext f hL d V c k
      (he.trans (invariantAffineProjection_descend f hL d V c k g hg).symm)⟩

/-- The induced coefficient homomorphism factors through the original source coefficient map. -/
theorem invariantAffineDescend_coefficients (g : A ⟶ Y) (hg : p ≫ g = q ≫ g) :
    (invariantAffineDescend f hL d V c k g hg).left.appTop ≫ (v).left.appTop =
      g.left.appTop :=
  congrArg (fun h ↦ h.left.appTop) (invariantAffineProjection_descend f hL d V c k g hg)

end FLT.Mazur.HilbertChart.AffineRestriction
