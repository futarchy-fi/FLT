/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertFiniteModelGenericFppf
public import FLT.Mazur.AffineHilbertModelGenericFppf

/-!
# Nonemptiness of the represented original Picard image in integral finite models

The target and represented subfunctor come from the full original Picard
relation. For an integral selected source, their target is nonempty precisely
when the full effective target is. Generic flatness supplies the fppf step;
this does not prove nonemptiness of the full effective target itself.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
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
local notation "v" => finiteKernelProjection f hL d V c k
local notation "H" => congrArg Over.Hom.left (finiteKernelProjection_condition f hL d V c k)

/-- The actual finite model's represented full Picard region, with the original base. -/
def finiteModelPicardFppfTarget : Over (Spec (.of R)) :=
  modelFppfTarget f hL d V c k v H

/-- Its image is defined by fppf-local original source representatives on every test. -/
def finiteModelPicardFppfImage := modelFppfLocalImage f hL d V c k v H

/-- Natural representation uses the original Picard sheaf, not a substitute quotient. -/
def finiteModelPicardFppfIso :
    yoneda.obj (finiteModelPicardFppfTarget f hL d V c k) ⋙ uliftFunctor.{1} ≅
      (finiteModelPicardFppfImage f hL d V c k).toFunctor :=
  modelFppfLocalImageIso f hL d V c k v H

variable [IsIntegral A.left]

/-- No new nonemptiness condition comes from requiring the full effective projection to be fppf. -/
theorem finiteModelPicardFppfTarget_nonempty_iff :
    Nonempty (finiteModelPicardFppfTarget f hL d V c k).left ↔
      Nonempty (modelEffectiveTarget f hL d V c k v H).left :=
  modelFppfTarget_nonempty_iff f hL d V c k v H

/-- The complete original source over the represented region has the same nonemptiness test. -/
theorem finiteModelPicardFppfSource_nonempty_iff :
    Nonempty (modelFppfSource f hL d V c k v H).left ↔
      Nonempty (modelEffectiveTarget f hL d V c k v H).left :=
  modelFppfSource_nonempty_iff f hL d V c k v H

/-- Every nonempty effective open contains a point in the represented full Picard region. -/
theorem finiteModelPicardFppfLocus_hits
    (W : (modelEffectiveTarget f hL d V c k v H).left.Opens)
    (hW : (W : Set (modelEffectiveTarget f hL d V c k v H).left).Nonempty) :
    ((W : Set (modelEffectiveTarget f hL d V c k v H).left) ∩
      SchemeFppfTargetOpen.locus
        (modelEffectiveRelativeProjection f hL d V c k v H).left).Nonempty :=
  modelFppfLocus_inter_nonempty f hL d V c k v H W hW

end FLT.Mazur.HilbertChart.AffineRestriction
