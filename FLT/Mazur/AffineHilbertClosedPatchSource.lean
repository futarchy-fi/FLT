/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertFlatStratumSource
public import FLT.Mazur.AffineHilbertMonicModelRelation

/-!
# Complete original sources over possibly nonreduced closed patches

Every ideal, without primality or radicality, gives an actual closed target
patch and a full original-source pullback. The original Picard relation remains
coequalized. This preserves nilpotents but does not assert flatness on the patch.
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
variable (r : Γ((finiteKernelModel f hL d V c k).left, ⊤))
local notation "U" => Scheme.basicOpen (Over.left Q) r
local notation "g" => finiteModelPrincipalProjection f hL d V c k r
variable (J : Ideal Γ(((finiteKernelModel f hL d V c k).left.basicOpen r).toScheme, ⊤))
local notation "i" => finiteModelStratumMap f hL d V c k r J

/-- The original closed patch includes all quotient-ring nilpotents. -/
def finiteModelClosedPatchToModel :
    Spec (.of (Γ((U).toScheme, ⊤) ⧸ J)) ⟶ (Q).left := i ≫ (U).ι

instance finiteModelClosedPatchToModel_mono :
    Mono (finiteModelClosedPatchToModel f hL d V c k r J) := by
  unfold finiteModelClosedPatchToModel
  infer_instance

/-- Keep the entire original source over the actual, possibly nonreduced, target patch. -/
def finiteModelClosedPatchSource : Over (Spec (.of R)) :=
  Over.mk (pullback.fst g i ≫ ((v).left ⁻¹ᵁ U).ι ≫ A.hom)

/-- The source comparison retains the original structural morphism. -/
def finiteModelClosedPatchSourceMap : finiteModelClosedPatchSource f hL d V c k r J ⟶ A :=
  Over.homMk (pullback.fst g i ≫ ((v).left ⁻¹ᵁ U).ι)

local notation "u" => finiteModelClosedPatchSourceMap f hL d V c k r J
local notation "t" => finiteModelClosedPatchToModel f hL d V c k r J

/-- The unreduced closed source is an actual pullback of the unchanged finite-model map. -/
theorem finiteModelClosedPatchSource_isPullback :
    IsPullback (u).left (pullback.snd g i) (v).left t :=
  (IsPullback.of_hasPullback g i).paste_horiz
    (isPullback_morphismRestrict (v).left U).flip

/-- Local finite presentation survives without a reducedness assumption. -/
instance finiteModelClosedPatchProjection_locallyOfFinitePresentation :
    LocallyOfFinitePresentation (pullback.snd g i) := inferInstance

/-- The actual entire closed-patch source remains affine. -/
instance finiteModelClosedPatchSource_isAffine :
    IsAffine (finiteModelClosedPatchSource f hL d V c k r J).left :=
  inferInstanceAs (IsAffine (pullback g i))

/-- Every point of a chosen closed patch has an original-source lift. -/
theorem finiteModelClosedPatchProjection_surjective
    (hr : r ∈ finiteModelPrincipalCoefficients f hL d V c k) :
    Surjective (pullback.snd g i) := by
  let _ := finiteModelPrincipalProjection_surjective f hL d V c k r hr
  infer_instance

/-- The full original relation survives on the entire unreduced source. -/
def finiteModelClosedPatchFullRelationIso : (relation f hL d V c (u ≫ k)).left ≅
    SchemeRelationRestriction.doubleDomain (fst f hL d V c k).left
      (snd f hL d V c k).left (u).left :=
  nestedSchemeDoubleIso f hL d V c k u

/-- Every original Picard arrow is coequalized even on nilpotent test schemes. -/
@[reassoc]
theorem finiteModelClosedPatchRelation_condition :
    (fst f hL d V c (u ≫ k)).left ≫ pullback.snd g i =
      (snd f hL d V c (u ≫ k)).left ≫ pullback.snd g i :=
  monicModelRelation_condition f hL d V c k u t (pullback.snd g i)
    (finiteModelClosedPatchSource_isPullback f hL d V c k r J)

end FLT.Mazur.HilbertChart.AffineRestriction
