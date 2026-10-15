/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedOddCompleteClosedComparison
public import FLT.Mazur.WeierstrassDividedEvenCompleteClosedComparison
public import FLT.Mazur.EllipticResolvedSmoothPoint

import all FLT.Mazur.WeierstrassDividedOddCompleteClosedComparison
import all FLT.Mazur.WeierstrassDividedEvenCompleteClosedComparison

/-!
# The entire actual resolved fiber is a complete closed fiber

The original split-depth coefficients supply the finite arithmetic model.
The proved odd and even pinching cocones include all singular points. This
existence statement retains the residue-field projection and makes no claim
about a map of whole families or an identification of multiplication laws.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonInfinitesimalStages
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
variable {K : Type} [Field K] (A : ValuationSubring K)
  {W : WeierstrassCurve A} {π : A} {depth : ℕ} (D : SplitNodeDepth W π depth)
  (hd : 2 ≤ depth) [NeZero depth]
local notation "F" => ResidueField A

/-- The full arithmetic resolved fiber is isomorphic over its residue field to the closed family. -/
theorem exists_resolvedWholeClosedFiberIso :
    ∃ e : resolvedSplitFiber A D ≅
        pullback (exactVeroneseProjToBase F depth hd) (completeClosedBase F),
      e.hom ≫ pullback.snd _ _ = resolvedSplitStructure A D := by
  obtain ⟨s, hs⟩ : ∃ s, depth / 2 = s + 1 := ⟨depth / 2 - 1, by omega⟩
  have hc : depth = 2 * s + 2 ∨ depth = 2 * s + 3 := by omega
  rcases hc with hc | hc
  · subst depth
    let hπ := SplitNodeDepth.uniformizer_ne_zero D
    let data := splitResolutionData A D
    let t := eqToIso (finiteGlobalTensorModel_index_congr hπ data F
      (le_refl _) (show s + 1 ≤ (2 * s + 2) / 2 by omega) hs)
    refine ⟨t ≪≫ evenCompleteClosedIso hπ data D s (by omega) rfl (by omega), ?_⟩
    rw [Iso.trans_hom, Category.assoc, evenCompleteClosedIso_snd]
    exact finiteGlobalTensorModel_structure_transport hπ data F _ _ hs
  · subst depth
    let hπ := SplitNodeDepth.uniformizer_ne_zero D
    let data := splitResolutionData A D
    let t := eqToIso (finiteGlobalTensorModel_index_congr hπ data F
      (le_refl _) (show s + 1 ≤ (2 * s + 3) / 2 by omega) hs)
    refine ⟨t ≪≫ oddCompleteClosedIso hπ data D s (by omega) rfl (by omega), ?_⟩
    rw [Iso.trans_hom, Category.assoc, oddCompleteClosedIso_snd]
    exact finiteGlobalTensorModel_structure_transport hπ data F _ _ hs

/-- A full closed-fiber comparison supplied by the actual odd or even arithmetic pinching. -/
def resolvedWholeClosedFiberIso : resolvedSplitFiber A D ≅
    pullback (exactVeroneseProjToBase F depth hd) (completeClosedBase F) :=
  (exists_resolvedWholeClosedFiberIso A D hd).choose

/-- The full comparison preserves the original arithmetic residue projection. -/
@[reassoc] theorem resolvedWholeClosedFiberIso_snd :
    (resolvedWholeClosedFiberIso A D hd).hom ≫ pullback.snd _ _ =
      resolvedSplitStructure A D :=
  (exists_resolvedWholeClosedFiberIso A D hd).choose_spec

/-- The entire arithmetic fiber, including its nodes, maps into the complete total scheme. -/
def resolvedWholeClosedInclusion : resolvedSplitFiber A D ⟶ exactVeroneseProj F depth hd :=
  (resolvedWholeClosedFiberIso A D hd).hom ≫ pullback.fst _ _

/-- The full arithmetic fiber is a Cartesian closed fiber over its original residue field. -/
theorem resolvedWholeClosed_isPullback :
    IsPullback (resolvedWholeClosedInclusion A D hd) (resolvedSplitStructure A D)
      (exactVeroneseProjToBase F depth hd) (completeClosedBase F) := by
  apply IsPullback.of_iso_pullback _ (resolvedWholeClosedFiberIso A D hd) rfl
    (resolvedWholeClosedFiberIso_snd A D hd)
  constructor
  change ((resolvedWholeClosedFiberIso A D hd).hom ≫ pullback.fst _ _) ≫ _ = _
  rw [Category.assoc, pullback.condition,
    ← Category.assoc, resolvedWholeClosedFiberIso_snd]

end FLT.Mazur.WeierstrassDividedDepth
