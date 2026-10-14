/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertNestedFiniteEtale
public import FLT.Mazur.SchemeEtaleImageModelBaseChange
public import FLT.Mazur.SchemeRelationMonicSeedOpenQuotient

/-!
# Effective finite recomputation on constructed monic-seed Hilbert charts

The affine charts are constructed from the original seed orbit. Their joint
finite projection is proved etale and their actual fppf region is compared
with the old coefficient quotient. The full-kernel input is derived here.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve
attribute [local irreducible] relation fst snd
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [Etale V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} [IsAffine A.left]
  (k : A ⟶ variableHilbertTest f d V) [IsOpenImmersion k.left]
variable {Z : Scheme} (a : Z ⟶ A.left)
  [Etale a] [Etale (a ≫ (finiteKernelProjection f hL d V c k).left)]
  [Mono (a ≫ (finiteKernelProjection f hL d V c k).left)]
  (z : (pullback (snd f hL d V c k).left a : Scheme))
local notation "v" => monicSeedAffineMap f hL d V c k a z
local notation "w₀" => Over.Hom.left (finiteKernelProjection f hL d V c k)
local notation "hw" => congrArg Over.Hom.left (finiteKernelProjection_condition f hL d V c k)
local instance seedNestedChartOpen : IsOpenImmersion (v).left :=
  monicSeedAffineMap_isOpenImmersion f hL d V c k a z w₀ hw
local instance seedNestedOldEtale : Etale ((v).left ≫ w₀) :=
  monicSeedAffineChart_target_etale f hL d V c k a z w₀ hw
local notation "H" => monicSeedAffine_isPullback f hL d V c k w₀ hw a z
local notation "j" => nestedFiniteProjection f hL d V c k v
local notation "hj" => nestedFiniteProjection_condition f hL d V c k v
local notation "r" => nestedFiniteToOld f hL d V c k v
local notation "hr" => nestedFiniteProjection_toOld f hL d V c k v
attribute [local irreducible] finiteKernelProjection finiteKernelModel
  nestedFiniteProjection nestedFiniteTarget nestedFiniteToOld nestedFiniteToNew

/-- The newly recomputed joint coefficients have an etale map on the entire constructed chart. -/
theorem monicSeedNestedFiniteProjection_etale : Etale j :=
  nestedFiniteProjection_etale f hL d V c k v H

/-- A genuine scheme isomorphism onto the actual fppf region, with the kernel input constructed. -/
def monicSeedNestedFiniteEffectiveIso :
    (SchemeEtaleImageQuotient.image ((v).left ≫ w₀)).toScheme ≅
      (SchemeFppfTargetOpen.locus j).toScheme := nestedFiniteEffectiveIso f hL d V c k v H

/-- The effective-region isomorphism retains the old finite coefficient morphism. -/
@[reassoc]
theorem monicSeedNestedFiniteEffectiveIso_toOld :
    (monicSeedNestedFiniteEffectiveIso f hL d V c k a z).hom ≫
      (SchemeFppfTargetOpen.locus j).ι ≫ r =
        (SchemeEtaleImageQuotient.image ((v).left ≫ w₀)).ι :=
  SchemeEtaleImageDenseModel.effectiveIso_toOld ((v).left ≫ w₀) H j hj r hr

/-- Every arbitrary test of this quotient has a surjective etale COMPLETE source pullback. -/
theorem monicSeedNestedFinite_complete_cover {Y : Scheme}
    (b : Y ⟶ (SchemeEtaleImageQuotient.image ((v).left ≫ w₀)).toScheme) :
    Etale (SchemeEtaleImageDenseModel.completeProjection ((v).left ≫ w₀) H j hj b) ∧
    Surjective (SchemeEtaleImageDenseModel.completeProjection ((v).left ≫ w₀) H j hj b) :=
  ⟨SchemeEtaleImageDenseModel.completeProjection_etale ((v).left ≫ w₀) H j hj b r hr,
    SchemeEtaleImageDenseModel.completeProjection_surjective ((v).left ≫ w₀) H j hj b r hr⟩

omit [Etale a] [Mono (a ≫ (finiteKernelProjection f hL d V c k).left)] in
/-- The selected affine quotient is an actual open of the original propagated-source quotient. -/
theorem monicSeedNestedImage_le_quotient :
    SchemeEtaleImageQuotient.image ((v).left ≫ w₀) ≤
      SchemeRelationMonicSeedKernel.quotientOpen w₀ hw a := by
  rintro y ⟨x, rfl⟩
  exact ⟨SchemeRelationMonicSeedKernel.affineToBranch
    (p := fst f hL d V c k) a z x, rfl⟩

/-- The old actual quotient receives the recomputed chart quotient by its open inclusion. -/
def monicSeedNestedToQuotient :
    (SchemeEtaleImageQuotient.image ((v).left ≫ w₀)).toScheme ⟶
      (SchemeRelationMonicSeedKernel.quotientOpen w₀ hw a).toScheme :=
  (finiteKernelModel f hL d V c k).left.homOfLE
    (monicSeedNestedImage_le_quotient f hL d V c k a z)

local instance seedNestedOriginalKernelMono : Mono (pullback.lift
    (fst f hL d V c k).left (snd f hL d V c k).left hw) :=
  modelRelationKernelMap_mono f hL d V c k w₀ hw

/-- The finite quotient comparison agrees with the previously constructed actual source-open map. -/
theorem monicSeedNested_open_quotient :
    SchemeRelationMonicSeedKernel.affineToBranch (p := fst f hL d V c k) a z ≫
      (SchemeRelationMonicSeedKernel.sourceIso w₀ hw a).hom ≫
        SchemeRelationMonicSeedKernel.openProjection w₀ hw a =
    SchemeEtaleImageQuotient.projection ((v).left ≫ w₀) ≫
      monicSeedNestedToQuotient f hL d V c k a z := by
  apply (cancel_mono (SchemeRelationMonicSeedKernel.quotientOpen w₀ hw a).ι).mp
  rw [Category.assoc, Category.assoc,
    SchemeRelationMonicSeedKernel.openProjection_ι,
    SchemeRelationMonicSeedKernel.sourceIso_hom_ι_assoc]
  rw [Category.assoc, monicSeedNestedToQuotient, Scheme.homOfLE_ι,
    SchemeEtaleImageQuotient.projection_ι]
  rfl

end FLT.Mazur.HilbertChart.AffineRestriction
