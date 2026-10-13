/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertFiniteModelImage

/-!
# An actual surjective projection over the finite model's dense image open

Restrict the original source by the inverse image of the constructed target
open. The resulting projection is surjective, quasi-compact and locally
finitely presented. All maps retain the original coefficient base. Flatness
and identification of the Picard relation remain separate requirements.
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
local notation "Q" => finiteKernelModel f hL d V c k
local notation "v" => finiteKernelProjection f hL d V c k
local notation "U" => finiteModelImageInterior f hL d V c k
/-- The source open is the full inverse image of the actual target image interior. -/
def finiteModelImageSourceOpen : A.left.Opens := (v).left ⁻¹ᵁ U

local notation "W" => finiteModelImageSourceOpen f hL d V c k

/-- The actual dense open target with its unchanged structural morphism. -/
def finiteModelImageTarget : Over (Spec (.of R)) := Over.mk ((U).ι ≫ (Q).hom)

/-- Its actual inverse image inside the original parameter scheme. -/
def finiteModelImageSource : Over (Spec (.of R)) := Over.mk ((W).ι ≫ A.hom)

/-- The source remains an open part of the original parameter. -/
def finiteModelImageSourceMap : finiteModelImageSource f hL d V c k ⟶ A := Over.homMk (W).ι

/-- The target inclusion retains the original finite coefficient model. -/
def finiteModelImageTargetMap : finiteModelImageTarget f hL d V c k ⟶ Q := Over.homMk (U).ι

/-- The constructed projection is the actual restriction, not an assumed quotient map. -/
def finiteModelImageProjection : finiteModelImageSource f hL d V c k ⟶
    finiteModelImageTarget f hL d V c k :=
  Over.homMk ((v).left ∣_ U) (by
    change ((v).left ∣_ U) ≫ (U).ι ≫ (Q).hom = (W).ι ≫ A.hom
    rw [← Category.assoc, morphismRestrict_ι, Category.assoc, (v).w]
    rfl)

local notation "u" => finiteModelImageProjection f hL d V c k

/-- The complete square retains the original source and target maps. -/
@[reassoc]
theorem finiteModelImageProjection_square :
    u ≫ finiteModelImageTargetMap f hL d V c k =
      finiteModelImageSourceMap f hL d V c k ≫ v := by
  apply Over.OverMorphism.ext
  exact morphismRestrict_ι (v).left U

/-- The restriction square is an actual scheme pullback. -/
theorem finiteModelImageProjection_isPullback :
    IsPullback (finiteModelImageSourceMap f hL d V c k).left (u).left
      (v).left (finiteModelImageTargetMap f hL d V c k).left :=
  (isPullback_morphismRestrict (v).left U).flip

/-- Surjectivity is proved from membership in the original image. -/
instance finiteModelImageProjection_surjective : Surjective (u).left := by
  constructor
  intro y
  obtain ⟨x, hx⟩ := finiteModelImageInterior_subset_range f hL d V c k y.property
  refine ⟨⟨x, ?_⟩, ?_⟩
  · change (v).left x ∈ U
    rw [hx]
    exact y.property
  · apply Subtype.ext
    exact (morphismRestrict_base_coe (v).left U _).trans hx

/-- The complete restricted projection is locally finitely presented by base change. -/
instance finiteModelImageProjection_locallyOfFinitePresentation :
    LocallyOfFinitePresentation (u).left :=
  MorphismProperty.of_isPullback (finiteModelImageProjection_isPullback f hL d V c k)
    inferInstance

/-- The entire projection remains quasi-compact, without selecting individual branches. -/
instance finiteModelImageProjection_quasiCompact : QuasiCompact (u).left :=
  MorphismProperty.of_isPullback (finiteModelImageProjection_isPullback f hL d V c k)
    inferInstance

/-- The constructed open target is Noetherian. -/
instance finiteModelImageTarget_isNoetherian :
    IsNoetherian (finiteModelImageTarget f hL d V c k).left := by
  change IsNoetherian (U).toScheme
  let _ := finiteKernelModel_isNoetherian f hL d V c k
  let _ : TopologicalSpace.NoetherianSpace U :=
    TopologicalSpace.NoetherianSpace.set (U : Set (Q).left)
  let _ : CompactSpace U := TopologicalSpace.NoetherianSpace.compactSpace U
  exact ⟨⟩

/-- The actual source remains Noetherian over the constructed target. -/
instance finiteModelImageSource_isNoetherian :
    IsNoetherian (finiteModelImageSource f hL d V c k).left := by
  let _ := LocallyOfFiniteType.isLocallyNoetherian (u).left
  let _ := QuasiCompact.compactSpace_of_compactSpace (u).left
  exact ⟨⟩

end FLT.Mazur.HilbertChart.AffineRestriction
