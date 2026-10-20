/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonNilpotentSmoothAffine
public import FLT.Mazur.WeierstrassDiagonalizableLocalLift

/-!
# Whole diagonalizable lifts on nilpotent one-gon smoothings

The entire smooth target is affine, so formal smoothness gives a global
underlying lift on the original character algebra. The integral correction
then gives a unique multiplicative lift, without inverting the subgroup order.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry MonObj

namespace FLT.Mazur.OneGonSmoothing

open WeierstrassIntegralChart WeierstrassDiagonalizableDefect DiagonalizableCobar

local notation "SmoothPoints" => WeierstrassDiagonalizableDefect.Points

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R G : Type} [CommRing R] [AddCommMonoid G]
  (t : R) (ht : IsNilpotent t) (I : Ideal R) (hI : I ^ 2 = ⊥)

include ht hI in
/-- Every original reduced character-scheme map has a global smooth lift. -/
theorem nilpotent_diagonalizable_exists_lift
    (p : SmoothPoints (equation t) (AddMonoidAlgebra (R ⧸ I) G)) :
    ∃ q : SmoothPoints (equation t) (AddMonoidAlgebra R G),
      smoothAlgebraReduction (equation t) (coefficientReduction R G I) q = p := by
  let _ := nilpotent_smooth_isAffine t ht
  obtain ⟨s, hs, hv⟩ := AffineSmoothNilpotentLift.exists_lift (coefficientImmersion (G := G) I)
    ⟨2, coefficientImmersion_ker_sq_zero I hI⟩ (integralSmoothStructure (equation t)) p.left
    (Spec.map (CommRingCat.ofHom (algebraMap R (AddMonoidAlgebra R G))))
    ((smoothAlgebraTestMap (coefficientReduction R G I)).w.trans p.w.symm)
  exact ⟨Over.homMk s hv, Over.OverMorphism.ext hs⟩

include ht hI in
/-- Each multiplicative reduced map has exactly one full multiplicative smooth lift. -/
theorem nilpotent_diagonalizable_existsUnique_lift
    (p : SmoothPoints (equation t) (AddMonoidAlgebra (R ⧸ I) G))
    (hp : defect (equation t) p = 1) :
    ∃! q : SmoothPoints (equation t) (AddMonoidAlgebra R G),
      smoothAlgebraReduction (equation t) (coefficientReduction R G I) q = p ∧
        defect (equation t) q = 1 := by
  obtain ⟨q, hq⟩ := nilpotent_diagonalizable_exists_lift t ht I hI p
  have hm : defect (equation t)
      (smoothAlgebraReduction (equation t) (coefficientReduction R G I) q) = 1 := by
    rw [hq, hp]
  simpa only [hq] using existsUnique_corrected (equation t) I hI q hm

end FLT.Mazur.OneGonSmoothing
