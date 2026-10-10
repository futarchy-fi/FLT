/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroCycleGlobalComponentRestrictions
public import FLT.Mazur.PinchingPullbackTransport
import all FLT.Mazur.WeierstrassDividedZeroCycleGlobalDesc
import all FLT.Mazur.WeierstrassDividedZeroCycleGlobalComponentRestrictions

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
/-- A cocone on the specified pinching span supplies the exact cyclic endpoint equations. -/
theorem zeroSplitCycleCocone_family_compatible {K : Type u} [Field K] (s : ℕ)
    {Y : Over (Spec (.of K))} (f : PolygonPinching.components K (2 * s + 3) ⟶ Y)
    (g : PolygonPinching.nodes K (2 * s + 3) ⟶ Y)
    (w : PolygonPinching.toComponents K (2 * s + 3) (by omega) ≫ f =
      PolygonPinching.toNodes K (2 * s + 3) ≫ g) (i : Fin (2 * s + 3)) :
    ProjectiveLine.zero K ≫ (PolygonPinching.componentι K (2 * s + 3) i ≫ f).left =
      ProjectiveLine.infinity K ≫
        (PolygonPinching.componentι K (2 * s + 3)
          (PolygonPinching.next (by omega) i) ≫ f).left := by
  have H (b : Bool) := congrArg (fun q => PolygonPinching.branchι K (2 * s + 3) i b ≫ q) w
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
  (hstart : start = 0) (hp : 2 * (start + s + 1) < depth)
local notation "K" => ResidueField R
local notation "p" => pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R K)))
  (finiteGlobalStructure hπ data (s + 1) hs)
local notation "Z" => zeroSplitCycleComponent hπ data D s hs hstart (by omega) hp
local notation "N" => zeroSplitCycleNormalization hπ data D s hs hstart (by omega) hp
local notation "Q" => zeroSplitCycleNodes hπ data D s hs (by omega) hp
variable {Y : Over (Spec (.of (ResidueField R)))}
  (f : PolygonPinching.components (ResidueField R) (2 * s + 3) ⟶ Y)
  (g : PolygonPinching.nodes (ResidueField R) (2 * s + 3) ⟶ Y)
  (w : PolygonPinching.toComponents (ResidueField R) (2 * s + 3) (by omega) ≫ f =
    PolygonPinching.toNodes (ResidueField R) (2 * s + 3) ≫ g)
local notation "F" => fun i => Over.Hom.left (PolygonPinching.componentι K (2 * s + 3) i ≫ f)

local notation "wf" => zeroSplitCycleCocone_family_compatible s f g w
local notation "d" => zeroSplitCycleGlobalDesc hπ data D s hs hstart hp F wf

/-- The constructed scheme descent preserves the residue coefficient structure. -/
@[reassoc] theorem zeroSplitCycleCocone_desc_structure : d ≫ Y.hom = p := by
  apply zeroSplitCycleComponent_hom_ext hπ data D s hs hstart (by omega) hp
  intro i
  rw [← Category.assoc, zeroSplitCycleGlobalDesc_component]
  exact (PolygonPinching.componentι K (2 * s + 3) i ≫ f).w.trans (Z i).w.symm

/-- The actual cyclic cocone descends to every target over the residue field. -/
def zeroSplitCycleCoconeDesc : Over.mk p ⟶ Y :=
  Over.homMk d (zeroSplitCycleCocone_desc_structure hπ data D s hs hstart hp f g w)

/-- The descended map retains the entire normalization leg. -/
@[reassoc] theorem zeroSplitCycleCoconeDesc_normalization :
    N ≫ zeroSplitCycleCoconeDesc hπ data D s hs hstart hp f g w = f := by
  apply Sigma.hom_ext
  intro i
  change PolygonPinching.componentι K (2 * s + 3) i ≫ N ≫ _ =
    PolygonPinching.componentι K (2 * s + 3) i ≫ f
  rw [zeroSplitCycleNormalization_ι_assoc]
  apply Over.OverMorphism.ext
  exact zeroSplitCycleGlobalDesc_component hπ data D s hs hstart hp F wf i

include w in
/-- The normalization leg gives existence and uniqueness of descent for each actual cocone. -/
theorem zeroSplitCycleCocone_existsUnique_desc :
    ∃! q : Over.mk p ⟶ Y, N ≫ q = f := by
  refine ⟨zeroSplitCycleCoconeDesc hπ data D s hs hstart hp f g w,
    zeroSplitCycleCoconeDesc_normalization hπ data D s hs hstart hp f g w, ?_⟩
  intro q hq
  apply (cancel_epi N).mp
  exact hq.trans
    (zeroSplitCycleCoconeDesc_normalization hπ data D s hs hstart hp f g w).symm

/-- The original component and node cocone is a pushout over the actual residue field. -/
theorem zeroSplitCycleCocone_isPushout :
    IsPushout (PolygonPinching.toComponents K (2 * s + 3) (by omega))
      (PolygonPinching.toNodes K (2 * s + 3)) N Q := by
  let _ : Epi (PolygonPinching.toNodes K (2 * s + 3)) :=
    epi_of_epi_fac (PinchingPullbackTransport.nodeRetraction_toNodes K (2 * s + 3))
  apply PinchingPushoutCriterion.isPushout_of_existsUnique
  · exact zeroSplitCycleCocone_condition hπ data D s hs hstart (by omega) hp
  · intro Y f g w
    exact zeroSplitCycleCocone_existsUnique_desc hπ data D s hs hstart hp f g w

/-- The constructed original cyclic cocone has the full colimit universal property. -/
def zeroSplitCycleCoconeIsColimit :
    IsColimit (zeroSplitCycleCocone hπ data D s hs hstart (by omega) hp) :=
  (zeroSplitCycleCocone_isPushout hπ data D s hs hstart hp).isColimit

/-- Forgetting coefficient structure gives the full arbitrary-target scheme pushout. -/
theorem zeroSplitCycleCocone_scheme_isPushout :
    IsPushout (PolygonPinching.toComponents K (2 * s + 3) (by omega)).left
      (PolygonPinching.toNodes K (2 * s + 3)).left (N).left (Q).left :=
  (zeroSplitCycleCocone_isPushout hπ data D s hs hstart hp).map (Over.forget _)

end FLT.Mazur.WeierstrassDividedDepth
