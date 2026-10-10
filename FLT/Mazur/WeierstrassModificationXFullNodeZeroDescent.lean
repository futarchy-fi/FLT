/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXFullNodeConicBranch
public import FLT.Mazur.WeierstrassConicZeroAffineParameter

/-!
# Descent on the original start-zero node with its complete conic parameter

The zero-constant conic branch is an entire affine line. The other branch
retains its original localized denominator. Both original markings are preserved.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Polynomial
namespace FLT.Mazur.WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
universe u
variable {K : Type u} [Field K] (a c : K) (ha : IsUnit a) (hc : c = 0)
local notation "s" => fullNodeNormalizedDenominator a c
local notation "hs" => fullNodeNormalizedDenominator_value a c ha
local notation "E" => conicZeroAffineIso c hc ≪≫ fullNodeConicParameterIso a c ha

/-- The complete conic affine coordinate is the original localized first branch coordinate. -/
@[reassoc] theorem fullNodeZeroParameter_branchOpen :
    (E).hom ≫ NodeLocalDescent.branchOpen K (PolygonNodeEqualizer.first s) = 𝟙 _ := by
  change (Spec.map _ ≫ Spec.map _) ≫ Spec.map _ = _
  rw [← Spec.map_comp, ← Spec.map_comp, ← Spec.map_id]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro p
  change conicZeroAffineEquiv c hc
    (fullNodeConicParameterEquiv a c ha (algebraMap _ _ p)) = p
  rw [fullNodeConicParameterEquiv_base, conicZeroAffineEquiv_base]

/-- The full conic parameter identification preserves the original first localized origin. -/
@[reassoc] theorem fullNodeZeroParameter_origin :
    ProjectiveLine.chartZero K ≫ (E).hom = NodeLocalDescent.firstOrigin K s hs := by
  let _ : IsOpenImmersion (NodeLocalDescent.branchOpen K (PolygonNodeEqualizer.first s)) :=
    IsOpenImmersion.of_isLocalization (PolygonNodeEqualizer.first s)
  apply (cancel_mono (NodeLocalDescent.branchOpen K (PolygonNodeEqualizer.first s))).mp
  simp only [Category.assoc, fullNodeZeroParameter_branchOpen, Category.comp_id,
    NodeLocalDescent.firstOrigin_branchOpen]

/-- Compatible maps on the full conic and localized exterior descend to the actual node. -/
theorem fullNodeZero_exists_unique_desc {Y : Scheme.{u}}
    (f : ProjectiveLine.chart K ⟶ Y)
    (g : Spec (.of (Localization.Away (PolygonNodeEqualizer.second s))) ⟶ Y)
    (w : ProjectiveLine.chartZero K ≫ f = NodeLocalDescent.secondOrigin K s hs ≫ g) :
    ∃! d : Spec (.of (FullNodeOpen a c)) ⟶ Y,
      (E).hom ≫ fullNodeFirstBranch a c ha ≫ d = f ∧ fullNodeSecondBranch a c ha ≫ d = g := by
  let H := fullNodeBranches_isPushout a c ha
  have w' : NodeLocalDescent.firstOrigin K s hs ≫ ((E).inv ≫ f) =
      NodeLocalDescent.secondOrigin K s hs ≫ g := by
    rw [← fullNodeZeroParameter_origin a c ha hc, Category.assoc, Iso.hom_inv_id_assoc]
    exact w
  let d := H.desc ((E).inv ≫ f) g w'
  have hf : fullNodeFirstBranch a c ha ≫ d = (E).inv ≫ f := H.inl_desc _ _ w'
  have hg : fullNodeSecondBranch a c ha ≫ d = g := H.inr_desc _ _ w'
  have he : (E).hom ≫ fullNodeFirstBranch a c ha ≫ d = f := by
    rw [hf, Iso.hom_inv_id_assoc]
  refine ⟨d, ⟨he, hg⟩, ?_⟩
  intro e h
  apply H.hom_ext
  · exact (cancel_epi (E).hom).mp (h.1.trans he.symm)
  · exact h.2.trans hg.symm

end FLT.Mazur.WeierstrassModificationX
