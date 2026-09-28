/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DivisorLineBundleSumOpenCoherence

/-!
# Nested restriction of the divisor sum comparison

The global sum diagram and naturality of the canonical restriction comparisons
identify the open sum maps on nested opens. The comparison for two successive
inclusions agrees with the direct comparison through the restriction functor's
composition and equality constraints.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace FLT.Mazur.FCurve

variable {X : Scheme.{u}} {I J : X.IdealSheafData}

/-- The open sum diagram is compatible with passage to a nested open. -/
@[reassoc]
lemma divisorLineBundleSumRestrictLE (hI : EffectiveCartier I)
    (hJ : EffectiveCartier J) {U V : X.Opens} (h : V ≤ U) :
    (Scheme.Modules.restrictFunctor (X.homOfLE h)).map
        (divisorLineBundleSumRestrictSourceIso hI hJ U).hom ≫
      (Scheme.Modules.restrictFunctor (X.homOfLE h)).map
        (divisorLineBundleSumOnIso hI hJ U).hom ≫
      (divisorLineBundleRestrictLEIso (I * J) (hI.mul hJ) h).hom =
    (moduleRestrictLEIso
        (ModuleSheafTensor.tensor (divisorLineBundle I hI) (divisorLineBundle J hJ)) h).hom ≫
      (divisorLineBundleSumRestrictSourceIso hI hJ V).hom ≫
        (divisorLineBundleSumOnIso hI hJ V).hom := by
  rw [← Functor.map_comp_assoc, ← divisorLineBundleSumRestrict,
    Functor.map_comp, Category.assoc, divisorLineBundleRestrictLEIso_naturality,
    ← Category.assoc, moduleRestrictLEIso_naturality, Category.assoc,
    divisorLineBundleSumRestrict]

/-- Two nested restrictions of the sum satisfy the composition constraint. -/
lemma divisorLineBundleSumRestrictLE_comp (hI : EffectiveCartier I)
    (hJ : EffectiveCartier J) {U V W : X.Opens} (h : V ≤ U) (k : W ≤ V) :
    (Scheme.Modules.restrictFunctor (X.homOfLE k ≫ X.homOfLE h)).map
        ((divisorLineBundleSumRestrictSourceIso hI hJ U).hom ≫
          (divisorLineBundleSumOnIso hI hJ U).hom) ≫
      (Scheme.Modules.restrictFunctorComp (X.homOfLE k) (X.homOfLE h)).hom.app
        (divisorLineBundleOn (I * J) (hI.mul hJ) U) ≫
      (Scheme.Modules.restrictFunctor (X.homOfLE k)).map
        (divisorLineBundleRestrictLEIso (I * J) (hI.mul hJ) h).hom ≫
      (divisorLineBundleRestrictLEIso (I * J) (hI.mul hJ) k).hom =
    (Scheme.Modules.restrictFunctorCongr (X.homOfLE_homOfLE k h)).hom.app
      ((ModuleSheafTensor.tensor (divisorLineBundle I hI)
        (divisorLineBundle J hJ)).restrict U.ι) ≫
      (moduleRestrictLEIso
        (ModuleSheafTensor.tensor (divisorLineBundle I hI) (divisorLineBundle J hJ))
        (k.trans h)).hom ≫
      (divisorLineBundleSumRestrictSourceIso hI hJ W).hom ≫
        (divisorLineBundleSumOnIso hI hJ W).hom := by
  rw [divisorLineBundleRestrictLEIso_comp,
    (Scheme.Modules.restrictFunctorCongr
      (X.homOfLE_homOfLE k h)).hom.naturality_assoc]
  simp only [Functor.map_comp, Category.assoc]
  rw [divisorLineBundleSumRestrictLE]

end FLT.Mazur.FCurve
