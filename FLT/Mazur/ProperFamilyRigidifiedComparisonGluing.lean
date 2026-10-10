/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProperFamilyRigidifiedComparisonOverlaps
public import FLT.Mazur.RelativePicardFppfPairs
public import FLT.Mazur.SchemeIndependentCanonicalIsoGluing
public import FLT.Mazur.SchemeIndependentCanonicalPairDetection

/-!
# Gluing local comparisons between global rigidified bundles

Rigidity forces the original member comparisons to agree on every total-space
pair. Fully faithful independent descent glues their underlying isomorphisms.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.SchemePicard
open FCurve.LineSheafSectionRigidity SchemeFppfFamily
variable {X S : Scheme.{0}} (f : X ⟶ S) (e : S ⟶ X) (he : e ≫ f = 𝟙 S)
  [IsLocallyNoetherian S] [IsProper f] [Flat f]
  [GeometricallyConnected f] [GeometricallyReduced f]
  (T : Over S) (𝒰 : Scheme.Cover.{0} Scheme.fppfPrecoverage T.left)
  (L M : RigidifiedBundle (pointedBaseSection f e he T))
  (a : ∀ i, RigidifiedIso (pointedBaseSection f e he (relativeCoverMember T 𝒰 i))
    (rigidifiedBasePullback f e he (relativeCoverArrow T 𝒰 i) L).2
    (rigidifiedBasePullback f e he (relativeCoverArrow T 𝒰 i) M).2)

/-- Arbitrary rigidified member comparisons satisfy the original total-space pair equations. -/
theorem rigidifiedFamilyIso_mapCompatible :
    PairMapCompatible (relativeTotalCover f T 𝒰)
      (IndependentLineData.canonicalObj (relativeTotalCover f T 𝒰) L.1).overlap
      (IndependentLineData.canonicalObj (relativeTotalCover f T 𝒰) M.1).overlap
      (fun i ↦ (a i).val.hom) := by
  intro ij
  have h := rigidifiedComparisons_overlap f e he
    (relativeCoverPairLeft T 𝒰 ij.1 ij.2) (relativeCoverPairRight T 𝒰 ij.1 ij.2)
    (relativeCoverArrow T 𝒰 ij.1) (relativeCoverArrow T 𝒰 ij.2)
    (relativeCoverPairLeft T 𝒰 ij.1 ij.2 ≫ relativeCoverArrow T 𝒰 ij.1)
    rfl (relativeCoverPair_condition T 𝒰 ij.1 ij.2).symm L M (a ij.1) (a ij.2)
  exact SchemeIndependentCanonicalOverlap.pair_compatible_of_chart
    (relativeTotalMap f (relativeCoverArrow T 𝒰 ij.1))
    (relativeTotalMap f (relativeCoverArrow T 𝒰 ij.2))
    (relativeTotalMap f (relativeCoverPairLeft T 𝒰 ij.1 ij.2))
    (relativeTotalMap f (relativeCoverPairRight T 𝒰 ij.1 ij.2))
    (relativeTotalMap f
      (relativeCoverPairLeft T 𝒰 ij.1 ij.2 ≫ relativeCoverArrow T 𝒰 ij.1))
    _ _ (relativeCoverPairTotalIso f T 𝒰 ij.1 ij.2).inv
    (relativeCoverPairTotalIso_inv_fst f T 𝒰 ij.1 ij.2)
    (relativeCoverPairTotalIso_inv_snd f T 𝒰 ij.1 ij.2)
    L.1.val M.1.val (a ij.1).val.hom (a ij.2).val.hom h

/-- Glue the original member comparisons to an actual global underlying line isomorphism. -/
def rigidifiedFamilyComparisonIso : L.1.val ≅ M.1.val :=
  IndependentLineData.glueIso (relativeTotalCover f T 𝒰) (L := L.1) (K := M.1)
    (fun i ↦ (a i).val) (rigidifiedFamilyIso_mapCompatible f e he T 𝒰 L M a)

/-- The global comparison recovers every supplied original member map. -/
theorem rigidifiedFamilyComparisonIso_member (i : 𝒰.I₀) :
    (Scheme.Modules.pullback ((relativeTotalCover f T 𝒰).f i)).map
      (rigidifiedFamilyComparisonIso f e he T 𝒰 L M a).hom = (a i).val.hom :=
  IndependentLineData.glueIso_member (relativeTotalCover f T 𝒰) (L := L.1) (K := M.1)
    (fun i ↦ (a i).val) (rigidifiedFamilyIso_mapCompatible f e he T 𝒰 L M a) i

end FLT.Mazur.SchemePicard
