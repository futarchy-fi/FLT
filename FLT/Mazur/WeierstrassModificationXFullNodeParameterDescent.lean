/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXFullNodeConicBranch
public import FLT.Mazur.WeierstrassModificationXConicParameterOrigin

/-!
# Descent on the full original node with an arbitrary conic constant

The complete conic parameter and the exact localized exterior branch
descend from their original marked origins without a vanishing constant.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Polynomial
namespace FLT.Mazur.WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
universe u
variable {K : Type u} [Field K] (a c : K) (ha : IsUnit a)
local notation "s" => fullNodeNormalizedDenominator a c
local notation "hs" => fullNodeNormalizedDenominator_value a c ha
local notation "E" => fullNodeConicParameterIso a c ha

/-- The full parameter comparison retains the actual rational coordinate map. -/
@[reassoc] theorem fullNodeConicParameter_branchOpen :
    (E).hom ≫ NodeLocalDescent.branchOpen K (PolygonNodeEqualizer.first s) =
      Spec.map (CommRingCat.ofHom (algebraMap K[X] (ConicParameterOpen c))) := by
  change Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  exact fullNodeConicParameterEquiv_base a c ha

/-- The rational parameter origin is precisely the original first localized origin. -/
@[reassoc] theorem fullNodeConicParameter_origin :
    Spec.map (CommRingCat.ofHom (conicParameterOrigin c).toRingHom) ≫ (E).hom =
      NodeLocalDescent.firstOrigin K s hs := by
  let _ : IsOpenImmersion (NodeLocalDescent.branchOpen K (PolygonNodeEqualizer.first s)) :=
    IsOpenImmersion.of_isLocalization (PolygonNodeEqualizer.first s)
  apply (cancel_mono (NodeLocalDescent.branchOpen K (PolygonNodeEqualizer.first s))).mp
  rw [Category.assoc, fullNodeConicParameter_branchOpen,
    NodeLocalDescent.firstOrigin_branchOpen, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  exact conicParameterOrigin_base c

/-- Compatible maps on the full conic and localized exterior descend to the actual node. -/
theorem fullNodeConicParameter_exists_unique_desc {Y : Scheme.{u}}
    (f : Spec (.of (ConicParameterOpen c)) ⟶ Y)
    (g : Spec (.of (Localization.Away (PolygonNodeEqualizer.second s))) ⟶ Y)
    (w : Spec.map (CommRingCat.ofHom (conicParameterOrigin c).toRingHom) ≫ f =
      NodeLocalDescent.secondOrigin K s hs ≫ g) :
    ∃! d : Spec (.of (FullNodeOpen a c)) ⟶ Y,
      (E).hom ≫ fullNodeFirstBranch a c ha ≫ d = f ∧ fullNodeSecondBranch a c ha ≫ d = g := by
  let H := fullNodeBranches_isPushout a c ha
  have w' : NodeLocalDescent.firstOrigin K s hs ≫ ((E).inv ≫ f) =
      NodeLocalDescent.secondOrigin K s hs ≫ g := by
    rw [← fullNodeConicParameter_origin a c ha, Category.assoc, Iso.hom_inv_id_assoc]
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
