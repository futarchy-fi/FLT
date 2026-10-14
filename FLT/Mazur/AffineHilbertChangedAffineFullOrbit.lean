/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertChangedOrbitKernel
public import FLT.Mazur.AffineHilbertGroundKernelRestriction

/-!
# Affine orbit parameters through every changed-ground seed

Choose an affine open in the complete orbit through each reflexive seed.
Its actual changed-family Picard relation is its ground kernel, giving an
effective etale image quotient. These image opens cover the entire new ground.
The affine parameter maps are monic, but are not claimed open in Hilbert space.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] relation fst snd finiteKernelProjection finiteKernelModel
variable {R R' : Type} [CommRing R] [CommRing R']
  [Algebra.FiniteType ℤ R] [Algebra.FiniteType ℤ R'] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [Etale V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} [IsAffine A.left]
  (k : A ⟶ variableHilbertTest f d V) [IsOpenImmersion k.left]
  (s : Spec (.of R') ⟶ A.left)
local notation "p" => fst f hL d V c k
local notation "q" => snd f hL d V c k
local notation "e" => equivalence f hL d V c k
local notation "π" => pullback.snd (Over.Hom.left q) s
local notation "b" =>
  SchemeRelationEtaleBranchPropagation.branch (Over.Hom.left p) (Over.Hom.left q) s
local notation "a" => s ≫ A.hom
local notation "g" => Limits.pullback.snd f a
local notation "W" => RelativeCoefficientBaseChange.target a (T := V)
local notation "t" => RelativeCoefficientBaseChange.toOld a (T := V)
local notation "P" => variableHilbertFixedBaseProjection f a hL d V W t
local instance changedAffineFullSmooth : SmoothOfRelativeDimension 1 g :=
  MorphismProperty.pullback_snd _ _ inferInstance

local notation "B" => changedOrbitSource f hL d V c k s
local notation "l" => changedOrbitParameter f hL d V c k s
local notation "u" => changedOrbitToOld f hL d V c k s
local notation "h" => fixedBaseAmple f a hL
local notation "c'" => fixedBaseTranslationClass f a V W t c
local notation "p'" => fst g h d W c' l
local notation "q'" => snd g h d W c' l
local notation "D'" => relation g h d W c' l
local notation "r" => fixedBaseRelationMap f a hL d V W t c k l u
  (changedOrbitParameter_compat f hL d V c k s)
local notation "K" => (pullback (Over.hom B) (Over.hom B) : Scheme)
local notation "x" => pullback.fst (Over.hom B) (Over.hom B)
local notation "y" => pullback.snd (Over.hom B) (Over.hom B)

attribute [local irreducible] SchemeRelationSplitOrbit.affineSource
  SchemeRelationSplitOrbit.affineToOrbit changedOrbitParameter changedOrbitChart

/-- An actual affine neighborhood in the full orbit through any requested seed. -/
def changedAffineFullSource (z : Spec (.of R')) : Over (Spec (.of R')) :=
  Over.mk (SchemeRelationSplitOrbit.affineToOrbit e s z ≫ (B).hom)

instance changedAffineFullSource_isAffine (z : Spec (.of R')) :
    IsAffine (changedAffineFullSource f hL d V c k s z).left :=
  inferInstanceAs (IsAffine (SchemeRelationSplitOrbit.affineSource e s z))

instance changedAffineFullSource_etale (z : Spec (.of R')) :
    Etale (changedAffineFullSource f hL d V c k s z).hom :=
  SchemeRelationSplitOrbit.affineProjection_etale e s z

/-- Its relative open inclusion is into the complete orbit. -/
def changedAffineFullToOrbit (z : Spec (.of R')) :
    changedAffineFullSource f hL d V c k s z ⟶ B :=
  Over.homMk (SchemeRelationSplitOrbit.affineToOrbit e s z)

/-- Its actual changed-family Hilbert parameter map retains all coefficients. -/
def changedAffineFullParameter (z : Spec (.of R')) :
    changedAffineFullSource f hL d V c k s z ⟶ variableHilbertTest g d W :=
  changedAffineFullToOrbit f hL d V c k s z ≫ l

instance changedAffineFullParameter_mono (z : Spec (.of R')) :
    Mono (changedAffineFullParameter f hL d V c k s z).left :=
  inferInstanceAs (Mono
    (SchemeRelationSplitOrbit.affineToOrbit e s z ≫ (l).left))

/-- The affine parameters preserve the literal old Hilbert parameter morphism. -/
@[reassoc]
theorem changedAffineFullParameter_old (z : Spec (.of R')) :
    (changedAffineFullParameter f hL d V c k s z).left ≫ (P).left =
      SchemeRelationSplitOrbit.affineToOrbit e s z ≫ (u).left ≫ k.left := by
  change (SchemeRelationSplitOrbit.affineToOrbit e s z ≫ (l).left) ≫ (P).left = _
  rw [Category.assoc]
  have he := congrArg Over.Hom.left (changedOrbitParameter_compat f hL d V c k s)
  change (u).left ≫ k.left = (l).left ≫ (P).left at he
  rw [← he]

/-- The retained affine seed has exactly the requested original Hilbert parameter. -/
theorem changedAffineFullParameter_seed (z : Spec (.of R')) :
    ((changedAffineFullParameter f hL d V c k s z).left ≫ (P).left)
      (SchemeRelationSplitOrbit.affineSeed e s z
        ⟨z, SchemeRelationSplitOrbit.mem_affineSeedOpen e s z⟩) = k.left (s z) := by
  rw [changedAffineFullParameter_old]
  exact congrArg (fun a' ↦ k.left a') (SchemeRelationSplitOrbit.affineSeed_point e s z)

/-- The independently rebuilt full relation on the affine parameters is their ground kernel. -/
theorem changedAffineFullRelation_isPullback (z : Spec (.of R')) :
    IsPullback (fst g h d W c' (changedAffineFullParameter f hL d V c k s z)).left
      (snd g h d W c' (changedAffineFullParameter f hL d V c k s z)).left
      (changedAffineFullSource f hL d V c k s z).hom
      (changedAffineFullSource f hL d V c k s z).hom :=
  groundKernelRestriction_isPullback g h d W c' l
    (changedOrbitRelation_isPullback f hL d V c k s)
    (changedAffineFullToOrbit f hL d V c k s z)

/-- The actual quotient target is an open of the full new ground. -/
def changedAffineFullImage (z : Spec (.of R')) : (Spec (.of R')).Opens :=
  SchemeEtaleImageQuotient.image (changedAffineFullSource f hL d V c k s z).hom

omit [Algebra.FiniteType ℤ R'] [IsAffine A.left] in
/-- Every requested seed lies in the image; this does not require W277's open-domain condition. -/
theorem mem_changedAffineFullImage (z : Spec (.of R')) :
    z ∈ changedAffineFullImage f hL d V c k s z := by
  let z' : (SchemeRelationSplitOrbit.affineSeedOpen e s z).toScheme :=
    ⟨z, SchemeRelationSplitOrbit.mem_affineSeedOpen e s z⟩
  refine ⟨SchemeRelationSplitOrbit.affineSeed e s z z', ?_⟩
  exact congrArg (fun v' ↦ v' z') (SchemeRelationSplitOrbit.affineSeed_target e s z)

omit [Algebra.FiniteType ℤ R'] [IsAffine A.left] in
/-- The effective affine image quotients cover the entire new ground, including every seed. -/
theorem changedAffineFullImage_cover :
    (⨆ z : Spec (.of R'), changedAffineFullImage f hL d V c k s z) = ⊤ := by
  apply top_le_iff.mp
  intro z _
  exact (le_iSup (fun z ↦ changedAffineFullImage f hL d V c k s z) z)
    (mem_changedAffineFullImage f hL d V c k s z)

/-- The image quotient is effective for the full actual changed-family relation. -/
theorem changedAffineFullImage_isPullback (z : Spec (.of R')) :
    IsPullback (fst g h d W c' (changedAffineFullParameter f hL d V c k s z)).left
      (snd g h d W c' (changedAffineFullParameter f hL d V c k s z)).left
      (SchemeEtaleImageQuotient.projection (changedAffineFullSource f hL d V c k s z).hom)
      (SchemeEtaleImageQuotient.projection (changedAffineFullSource f hL d V c k s z).hom) :=
  SchemeEtaleImageQuotient.isPullback _
    (changedAffineFullRelation_isPullback f hL d V c k s z)

end FLT.Mazur.HilbertChart.AffineRestriction
