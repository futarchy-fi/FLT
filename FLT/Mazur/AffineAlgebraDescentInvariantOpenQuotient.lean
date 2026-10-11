/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineAlgebraDescentInvariantOpenScheme
public import FLT.Mazur.RelativeRelationFpqcInvariantQuotient

/-!
# The full invariant quotient on original invariant opens

The constructed descended open is the invariant locally ringed quotient of
the original restricted coaction relation. This keeps the original relative
base and identifies the whole structure sheaf, even for non-affine source opens.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.AffineAlgebraDescent
open RelativeRelationOrbit
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R S B : Type u} [CommRing R] [CommRing S] [CommRing B]
  [Algebra R S] [Algebra R B] [Algebra S B] [IsScalarTower R S B]
  (D : Data R S B) [Module.FaithfullyFlat R S]
  (W : (Spec (.of B)).Opens)
  (hW : overlapFst D ⁻¹ᵁ W = overlapSnd (R := R) (S := S) (B := B) ⁻¹ᵁ W)

/-- The descended open retains its structural map to the original Spec R. -/
def openRelativeTarget : Over (Spec (.of R)) :=
  Over.mk ((descendedOpen D W hW).ι ≫ schemeBase D)

/-- The original open source, regarded over the original base. -/
def openRelativeSource : Over (Spec (.of R)) :=
  Over.mk (openProjection D W hW ≫ (openRelativeTarget D W hW).hom)

/-- The full original restricted overlap, regarded over the original base. -/
def openRelativeOverlap : Over (Spec (.of R)) :=
  Over.mk (openFst D W ≫ (openRelativeSource D W hW).hom)

/-- The actual restricted coefficient projection as a relative map. -/
def openRelativeProjection : openRelativeSource D W hW ⟶ openRelativeTarget D W hW :=
  Over.homMk (openProjection D W hW)

/-- The unchanged first endpoint as a relative map. -/
def openRelativeFst : openRelativeOverlap D W hW ⟶ openRelativeSource D W hW :=
  Over.homMk (openFst D W)

/-- The unchanged second endpoint as a relative map. -/
def openRelativeSnd : openRelativeOverlap D W hW ⟶ openRelativeSource D W hW :=
  Over.homMk (openSnd D W hW) (by
    change openSnd D W hW ≫ (openProjection D W hW ≫ _) = openFst D W ≫ _
    rw [← Category.assoc, ← (open_isPullback D W hW).w, Category.assoc]
    rfl)

/-- The chosen structural map is exactly the original coefficient-open structural map. -/
theorem openRelativeSource_hom : (openRelativeSource D W hW).hom =
    W.ι ≫ Spec.map (CommRingCat.ofHom (algebraMap R B)) := by
  change openProjection D W hW ≫ ((descendedOpen D W hW).ι ≫ schemeBase D) = _
  rw [← Category.assoc, (openProjection_isPullback D W hW).w, Category.assoc]
  exact congrArg (fun k ↦ W.ι ≫ k) (relativeSource_hom D)

/-- The restricted full relation remains the actual kernel pair over Spec R. -/
theorem openRelative_isPullback : IsPullback (openRelativeFst D W hW)
    (openRelativeSnd D W hW) (openRelativeProjection D W hW)
    (openRelativeProjection D W hW) :=
  IsPullback.of_map_of_faithful (Over.forget _) (open_isPullback D W hW)

/-- The restricted original overlap constructs its own full relative equivalence relation. -/
def openRelativeEquivalenceRelation :
    CategoryTheory.EquivalenceRelation (openRelativeFst D W hW) (openRelativeSnd D W hW) :=
  IsKernelPair.equivalenceRelation (openRelativeProjection D W hW)
    (openRelativeFst D W hW) (openRelativeSnd D W hW) (pullback.isLimit _ _)
    (openRelative_isPullback D W hW)

instance openRelativeProjection_flat : Flat (openRelativeProjection D W hW).left :=
  inferInstanceAs (Flat (openProjection D W hW))

instance openRelativeProjection_quasiCompact : QuasiCompact (openRelativeProjection D W hW).left :=
  inferInstanceAs (QuasiCompact (openProjection D W hW))

instance openRelativeProjection_surjective : Surjective (openRelativeProjection D W hW).left :=
  inferInstanceAs (Surjective (openProjection D W hW))

/-- The descended open is the original restricted invariant quotient, including its sheaf. -/
def openInvariantQuotientIso :
    invariantLocallyRingedSpace (openRelativeEquivalenceRelation D W hW) ≅
      (descendedOpen D W hW).toScheme.toLocallyRingedSpace :=
  fpqcInvariantQuotientIso (openRelativeEquivalenceRelation D W hW)
    (openRelativeProjection D W hW) (openRelative_isPullback D W hW)

/-- The quotient isomorphism recovers the unchanged original open-source projection. -/
@[reassoc]
theorem openInvariantQuotientIso_projection :
    invariantLocallyRingedProjection (openRelativeEquivalenceRelation D W hW) ≫
      (openInvariantQuotientIso D W hW).hom = (openProjection D W hW).toLRSHom :=
  fpqcInvariantQuotientIso_projection (openRelativeEquivalenceRelation D W hW)
    (openRelativeProjection D W hW) (openRelative_isPullback D W hW)

/-- The quotient isomorphism retains the original relative base map. -/
theorem openInvariantQuotientIso_baseMap :
    (openInvariantQuotientIso D W hW).hom ≫ (openRelativeTarget D W hW).hom.toLRSHom =
      invariantLocallyRingedBaseMap (openRelativeEquivalenceRelation D W hW) :=
  fpqcInvariantQuotientIso_baseMap (openRelativeEquivalenceRelation D W hW)
    (openRelativeProjection D W hW) (openRelative_isPullback D W hW)

end FLT.Mazur.AffineAlgebraDescent
