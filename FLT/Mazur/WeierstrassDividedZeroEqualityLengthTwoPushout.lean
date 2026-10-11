/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroEqualityLengthTwoComponentRestrictions
public import FLT.Mazur.WeierstrassDividedZeroEqualityPositivePushout
import all FLT.Mazur.WeierstrassDividedZeroEqualityLengthTwoGlobalDesc

import all FLT.Mazur.WeierstrassDividedZeroEqualityLengthTwoComponentRestrictions

/-!
# The actual cyclic residue model is the polygon pinching pushout

Descent of compatible projective families supplies the universal property
in schemes over the residue field and hence in schemes.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (hs : 0 + 1 ≤ n)
  (hstart : start = 0) (hk : 2 * (start + 0 + 1) ≤ depth)
  (hp : 2 * (start + 0 + 1) = depth)
local notation "K" => ResidueField R
local notation "p" => pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R K)))
  (finiteGlobalStructure hπ data (0 + 1) hs)
local notation "Z" => zeroEqualityCycleComponent hπ data D 0 hs hstart hk hp
local notation "N" => zeroEqualityCycleNormalization hπ data D 0 hs hstart hk hp
local notation "Q" => zeroEqualityCycleNodes hπ data D 0 hs hk
variable {Y : Over (Spec (.of (ResidueField R)))}
  (f : PolygonPinching.components (ResidueField R) 2 ⟶ Y)
  (g : PolygonPinching.nodes (ResidueField R) 2 ⟶ Y)
  (w : PolygonPinching.toComponents (ResidueField R) 2 (by omega) ≫ f =
    PolygonPinching.toNodes (ResidueField R) 2 ≫ g)
local notation "F" => fun i => Over.Hom.left (PolygonPinching.componentι K 2 i ≫ f)

local notation "wf" => zeroEqualityPositiveCycleCocone_family_compatible 0 f g w
local notation "d" => zeroEqualityLengthTwoGlobalDesc hπ data D hs hstart hk hp F wf

/-- The constructed scheme descent preserves the residue coefficient structure. -/
@[reassoc] theorem zeroEqualityLengthTwoCocone_desc_structure : d ≫ Y.hom = p := by
  apply zeroEqualityCycleComponent_hom_ext_lengthTwo hπ data D hs hstart hk hp
  intro i
  rw [← Category.assoc, zeroEqualityLengthTwoGlobalDesc_component]
  exact (PolygonPinching.componentι K 2 i ≫ f).w.trans (Z i).w.symm

/-- The actual cyclic cocone descends to every target over the residue field. -/
def zeroEqualityLengthTwoCoconeDesc : Over.mk p ⟶ Y :=
  Over.homMk d (zeroEqualityLengthTwoCocone_desc_structure
      hπ data D hs hstart hk hp f g w)

/-- The descended map retains the entire normalization leg. -/
@[reassoc] theorem zeroEqualityLengthTwoCoconeDesc_normalization :
    N ≫ zeroEqualityLengthTwoCoconeDesc hπ data D hs hstart hk hp f g w = f := by
  apply Sigma.hom_ext
  intro i
  change PolygonPinching.componentι K 2 i ≫ N ≫ _ =
    PolygonPinching.componentι K 2 i ≫ f
  rw [zeroEqualityCycleNormalization_ι_assoc hπ data D 0 hs hstart hk hp i]
  apply Over.OverMorphism.ext
  exact zeroEqualityLengthTwoGlobalDesc_component hπ data D hs hstart hk hp F wf i

include w in
/-- The normalization leg gives existence and uniqueness of descent for each actual cocone. -/
theorem zeroEqualityLengthTwoCocone_existsUnique_desc :
    ∃! q : Over.mk p ⟶ Y, N ≫ q = f := by
  refine ⟨zeroEqualityLengthTwoCoconeDesc hπ data D hs hstart hk hp f g w,
    zeroEqualityLengthTwoCoconeDesc_normalization hπ data D hs hstart hk hp f g w, ?_⟩
  intro q hq
  let _ := zeroEqualityCycleNormalization_epi_lengthTwo hπ data D hs hstart hk hp
  apply (cancel_epi N).mp
  exact hq.trans
    (zeroEqualityLengthTwoCoconeDesc_normalization hπ data D hs hstart hk hp f g w).symm

/-- The original component and node cocone is a pushout over the actual residue field. -/
theorem zeroEqualityLengthTwoCocone_isPushout :
    IsPushout (PolygonPinching.toComponents K 2 (by omega))
      (PolygonPinching.toNodes K 2) N Q := by
  let _ : Epi (PolygonPinching.toNodes K 2) :=
    epi_of_epi_fac (PinchingPullbackTransport.nodeRetraction_toNodes K 2)
  apply PinchingPushoutCriterion.isPushout_of_existsUnique
  · exact zeroEqualityCycleCocone_condition hπ data D 0 hs hstart hk hp
  · intro Y f g w
    exact zeroEqualityLengthTwoCocone_existsUnique_desc hπ data D hs hstart hk hp f g w

/-- The constructed original cyclic cocone has the full colimit universal property. -/
def zeroEqualityLengthTwoCoconeIsColimit :
    IsColimit (zeroEqualityCycleCocone hπ data D 0 hs hstart hk hp) :=
  (zeroEqualityLengthTwoCocone_isPushout hπ data D hs hstart hk hp).isColimit

/-- Forgetting coefficient structure gives the full arbitrary-target scheme pushout. -/
theorem zeroEqualityLengthTwoCocone_scheme_isPushout :
    IsPushout (PolygonPinching.toComponents K 2 (by omega)).left
      (PolygonPinching.toNodes K 2).left (N).left (Q).left :=
  (zeroEqualityLengthTwoCocone_isPushout hπ data D hs hstart hk hp).map (Over.forget _)

end FLT.Mazur.WeierstrassDividedDepth
