/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineAlgebraDescentInvariantNeighborhoods
public import FLT.Mazur.SchemeFpqcOpenSectionDescent

/-!
# Effective descent of original invariant open subschemes

Every invariant open in an affine coaction source descends to an actual open
of the constructed fixed-ring spectrum. The original source open, unchanged
relation endpoints and faithfully flat cover are retained, including functions.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.AffineAlgebraDescent
open SchemeEffectiveEpiSections
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R S B : Type u} [CommRing R] [CommRing S] [CommRing B]
  [Algebra R S] [Algebra R B] [Algebra S B] [IsScalarTower R S B]
  (D : Data R S B) [Module.FaithfullyFlat R S]
  (W : (Spec (.of B)).Opens)
  (hW : overlapFst D ⁻¹ᵁ W = overlapSnd (R := R) (S := S) (B := B) ⁻¹ᵁ W)

/-- The descended open is the actual image of the original invariant open. -/
def descendedOpen : (descendedScheme D).Opens :=
  ⟨schemeProjection D '' (W : Set (Spec (.of B))), projection_isOpen_image D W hW⟩

/-- The descended open reconstructs exactly the original invariant open. -/
theorem preimage_descendedOpen : schemeProjection D ⁻¹ᵁ descendedOpen D W hW = W :=
  TopologicalSpace.Opens.ext (projection_saturation D W hW)

/-- The original invariant source open maps to its constructed descended open scheme. -/
def openProjection : W.toScheme ⟶ (descendedOpen D W hW).toScheme :=
  (schemeProjection D).resLE _ W (preimage_descendedOpen D W hW).symm.le

/-- The original invariant open is the exact scheme pullback of its descended open. -/
theorem openProjection_isPullback : IsPullback (openProjection D W hW) W.ι
    (descendedOpen D W hW).ι (schemeProjection D) := by
  apply IsOpenImmersion.isPullback
  · exact (Scheme.Hom.resLE_comp_ι _ _).symm
  · simpa only [Scheme.Opens.opensRange_ι] using preimage_descendedOpen D W hW

/-- Descent reconstructs the original open by scalar base change, retaining both projections. -/
theorem open_isBaseChange : IsPullback (openProjection D W hW)
    (W.ι ≫ Spec.map (CommRingCat.ofHom (algebraMap S B)))
    ((descendedOpen D W hW).ι ≫ schemeBase D)
    (Spec.map (CommRingCat.ofHom (algebraMap R S))) :=
  (openProjection_isPullback D W hW).paste_vert (scheme_isPullback D)

instance openProjection_flat : Flat (openProjection D W hW) := by
  dsimp only [openProjection]
  infer_instance

instance openProjection_surjective : Surjective (openProjection D W hW) := by
  dsimp only [openProjection]
  rw [(schemeProjection D).resLE_congr _ rfl (preimage_descendedOpen D W hW).symm (@Surjective),
    Scheme.Hom.resLE_eq_morphismRestrict]
  exact IsZariskiLocalAtTarget.restrict (P := @Surjective) inferInstance _

instance openProjection_quasiCompact : QuasiCompact (openProjection D W hW) := by
  dsimp only [openProjection]
  rw [(schemeProjection D).resLE_congr _ rfl (preimage_descendedOpen D W hW).symm (@QuasiCompact),
    Scheme.Hom.resLE_eq_morphismRestrict]
  exact IsZariskiLocalAtTarget.restrict (P := @QuasiCompact) inferInstance _

/-- The first restricted endpoint uses the original relation open. -/
def openFst : (overlapFst D ⁻¹ᵁ W).toScheme ⟶ W.toScheme :=
  (overlapFst D).resLE W _ le_rfl

/-- The second restricted endpoint has the same original relation domain. -/
def openSnd : (overlapFst D ⁻¹ᵁ W).toScheme ⟶ W.toScheme :=
  (overlapSnd (R := R) (S := S) (B := B)).resLE W _ hW.le

/-- The original restricted relation is the full kernel pair of the descended-open cover. -/
theorem open_isPullback : IsPullback (openFst D W) (openSnd D W hW)
    (openProjection D W hW) (openProjection D W hW) := by
  apply Scheme.Hom.isPullback_resLE (overlap_isPullback D)
    (US := descendedOpen D W hW) (preimage_descendedOpen D W hW).symm.le
    (preimage_descendedOpen D W hW).symm.le
  rw [hW, inf_idem]

/-- The constructed open is the effective scheme quotient of its unchanged original relation. -/
def openCoforkIsColimit :
    IsColimit (Cofork.ofπ (openProjection D W hW) (open_isPullback D W hW).w) :=
  isColimitCoforkOfEffectiveEpi (openProjection D W hW) _ (open_isPullback D W hW).isLimit

/-- Its regular functions are exactly those of the original open satisfying the full relation. -/
def openInvariantFunctionsEquiv : Γ((descendedOpen D W hW).toScheme, ⊤) ≃+*
    compatibleFunctions (openFst D W) (openSnd D W hW) :=
  sectionsRingEquiv (open_isPullback D W hW)

end FLT.Mazur.AffineAlgebraDescent
