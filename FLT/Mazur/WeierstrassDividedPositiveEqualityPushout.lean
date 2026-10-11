/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedPositiveEqualityGlobalComponentRestrictions
public import FLT.Mazur.PinchingPullbackTransport
import all FLT.Mazur.WeierstrassDividedPositiveEqualityGlobalDesc
import all FLT.Mazur.WeierstrassDividedPositiveEqualityGlobalComponentRestrictions

/-!
# The positive-start equality residue model is the polygon pinching pushout

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
/-- A cocone on the specified pinching span supplies the exact cyclic endpoint equations. -/
theorem positiveEqualityCycleCocone_family_compatible {K : Type u} [Field K] (s : ℕ)
    {Y : Over (Spec (.of K))} (f : PolygonPinching.components K (2 * s + 4) ⟶ Y)
    (g : PolygonPinching.nodes K (2 * s + 4) ⟶ Y)
    (w : PolygonPinching.toComponents K (2 * s + 4) (by omega) ≫ f =
      PolygonPinching.toNodes K (2 * s + 4) ≫ g) (i : Fin (2 * s + 4)) :
    ProjectiveLine.zero K ≫ (PolygonPinching.componentι K (2 * s + 4) i ≫ f).left =
      ProjectiveLine.infinity K ≫
        (PolygonPinching.componentι K (2 * s + 4)
          (PolygonPinching.next (by omega) i) ≫ f).left := by
  have H (b : Bool) := congrArg (fun q => PolygonPinching.branchι K (2 * s + 4) i b ≫ q) w
  have H₀ := H false
  have H₁ := H true
  simp only [PolygonPinching.branchι_toComponents_zero_assoc,
    PolygonPinching.branchι_toNodes_assoc] at H₀
  simp only [PolygonPinching.branchι_toComponents_infinity_assoc,
    PolygonPinching.branchι_toNodes_assoc] at H₁
  exact congrArg Over.Hom.left (H₀.trans H₁.symm)

variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (s : ℕ) (hs : s + 1 ≤ n)
  (hstart : 0 < start) (hk : 2 * (start + s + 1) ≤ depth)
  (hp : 2 * (start + s + 1) = depth)
local notation "K" => ResidueField R
local notation "p" => pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R K)))
  (finiteGlobalStructure hπ data (s + 1) hs)
local notation "Z" => positiveEqualityCycleComponent hπ data D s hs hstart hk hp
local notation "N" => positiveEqualityCycleNormalization hπ data D s hs hstart hk hp
local notation "Q" => positiveEqualityCycleNodes hπ data D s hs hstart hk
variable {Y : Over (Spec (.of (ResidueField R)))}
  (f : PolygonPinching.components (ResidueField R) (2 * s + 4) ⟶ Y)
  (g : PolygonPinching.nodes (ResidueField R) (2 * s + 4) ⟶ Y)
  (w : PolygonPinching.toComponents (ResidueField R) (2 * s + 4) (by omega) ≫ f =
    PolygonPinching.toNodes (ResidueField R) (2 * s + 4) ≫ g)
local notation "F" => fun i => Over.Hom.left (PolygonPinching.componentι K (2 * s + 4) i ≫ f)

local notation "wf" => positiveEqualityCycleCocone_family_compatible s f g w
local notation "d" => positiveEqualityCycleGlobalDesc hπ data D s hs hstart hk hp F wf

/-- The constructed scheme descent preserves the residue coefficient structure. -/
@[reassoc] theorem positiveEqualityCycleCocone_desc_structure : d ≫ Y.hom = p := by
  apply positiveEqualityCycleComponent_hom_ext hπ data D s hs hstart hk hp
  intro i
  rw [← Category.assoc, positiveEqualityCycleGlobalDesc_component]
  exact (PolygonPinching.componentι K (2 * s + 4) i ≫ f).w.trans (Z i).w.symm

/-- The actual cyclic cocone descends to every target over the residue field. -/
def positiveEqualityCycleCoconeDesc : Over.mk p ⟶ Y :=
  Over.homMk d (positiveEqualityCycleCocone_desc_structure
      hπ data D s hs hstart hk hp f g w)

/-- The descended map retains the entire normalization leg. -/
@[reassoc] theorem positiveEqualityCycleCoconeDesc_normalization :
    N ≫ positiveEqualityCycleCoconeDesc hπ data D s hs hstart hk hp f g w = f := by
  apply Sigma.hom_ext
  intro i
  change PolygonPinching.componentι K (2 * s + 4) i ≫ N ≫ _ =
    PolygonPinching.componentι K (2 * s + 4) i ≫ f
  rw [positiveEqualityCycleNormalization_ι_assoc]
  apply Over.OverMorphism.ext
  exact positiveEqualityCycleGlobalDesc_component hπ data D s hs hstart hk hp F wf i

include w in
/-- The normalization leg gives existence and uniqueness of descent for each actual cocone. -/
theorem positiveEqualityCycleCocone_existsUnique_desc :
    ∃! q : Over.mk p ⟶ Y, N ≫ q = f := by
  refine ⟨positiveEqualityCycleCoconeDesc hπ data D s hs hstart hk hp f g w,
    positiveEqualityCycleCoconeDesc_normalization hπ data D s hs hstart hk hp f g w, ?_⟩
  intro q hq
  let _ := positiveEqualityCycleNormalization_epi hπ data D s hs hstart hk hp
  apply (cancel_epi N).mp
  exact hq.trans
    (positiveEqualityCycleCoconeDesc_normalization hπ data D s hs hstart hk hp f g w).symm

/-- The original component and node cocone is a pushout over the actual residue field. -/
theorem positiveEqualityCycleCocone_isPushout :
    IsPushout (PolygonPinching.toComponents K (2 * s + 4) (by omega))
      (PolygonPinching.toNodes K (2 * s + 4)) N Q := by
  let _ : Epi (PolygonPinching.toNodes K (2 * s + 4)) :=
    epi_of_epi_fac (PinchingPullbackTransport.nodeRetraction_toNodes K (2 * s + 4))
  apply PinchingPushoutCriterion.isPushout_of_existsUnique
  · exact positiveEqualityCycleCocone_condition hπ data D s hs hstart hk hp
  · intro Y f g w
    exact positiveEqualityCycleCocone_existsUnique_desc hπ data D s hs hstart hk hp f g w

/-- The constructed original cyclic cocone has the full colimit universal property. -/
def positiveEqualityCycleCoconeIsColimit :
    IsColimit (positiveEqualityCycleCocone hπ data D s hs hstart hk hp) :=
  (positiveEqualityCycleCocone_isPushout hπ data D s hs hstart hk hp).isColimit

/-- Forgetting coefficient structure gives the full arbitrary-target scheme pushout. -/
theorem positiveEqualityCycleCocone_scheme_isPushout :
    IsPushout (PolygonPinching.toComponents K (2 * s + 4) (by omega)).left
      (PolygonPinching.toNodes K (2 * s + 4)).left (N).left (Q).left :=
  (positiveEqualityCycleCocone_isPushout hπ data D s hs hstart hk hp).map (Over.forget _)

end FLT.Mazur.WeierstrassDividedDepth
