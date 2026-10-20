/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonNilpotentCharacterHom
public import FLT.Mazur.WeierstrassDiagonalizableCoefficientHom
public import FLT.Mazur.WeierstrassSmoothCoefficientGroupIso

/-!
# Lifting original intrinsic group homomorphisms onto a nilpotent smoothing

The input is an actual character-group homomorphism into the reduced smooth
curve. The output is an actual homomorphism into the original smoothing, and
its coefficient reduction is exactly the specified map. No coface equation
or underlying scheme lift is assumed from the caller.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry MonObj

namespace FLT.Mazur.OneGonSmoothing

open WeierstrassIntegralChart WeierstrassDividedDepth WeierstrassDiagonalizableDefect
open DiagonalizableCobar CharacterSchemeBaseChange

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R S G : Type} [CommRing R] [CommRing S] [Algebra R S] [AddCommGroup G]
  (W : WeierstrassCurve R)
  (f : CommGrp.mk (model S G) ⟶ integralSmoothGroup (W.map (algebraMap R S)))

/-- The original intrinsic homomorphism viewed on the extended character test of the old curve. -/
def intrinsicCharacterPoint : WeierstrassDiagonalizableDefect.Points W (AddMonoidAlgebra S G) :=
  coefficientHomPoint W (f ≫ (originalSmoothCoefficientGroupIso S W).hom)

/-- The resulting point is exactly the original morphism followed by coefficient comparison. -/
theorem intrinsicCharacterPoint_left :
    (intrinsicCharacterPoint W f).left =
      f.hom.hom.hom.left ≫ originalSmoothCoefficientMap S W := by
  change (f.hom.hom.hom.left ≫
    (originalSmoothCoefficientGroupIso S W).hom.hom.hom.hom.left) ≫ _ = _
  rw [originalSmoothCoefficientGroupIso_hom, Category.assoc, originalSmoothCoefficientIso_fst]

/-- The original homomorphism supplies the full multiplication equation on its character test. -/
theorem intrinsicCharacterPoint_defect : defect W (intrinsicCharacterPoint W f) = 1 :=
  coefficientHomPoint_defect W (f ≫ (originalSmoothCoefficientGroupIso S W).hom)

variable (t : R) (ht : IsNilpotent t) (I : Ideal R) (hI : I ^ 2 = ⊥)
  (g : CommGrp.mk (model (R ⧸ I) G) ⟶
    integralSmoothGroup ((equation t).map (algebraMap R (R ⧸ I))))

/-- The actual lifted homomorphism from the original character group into the smoothing. -/
def nilpotentIntrinsicHomLift : CommGrp.mk (model R G) ⟶ integralSmoothGroup (equation t) :=
  nilpotentCharacterHom t ht I hI (intrinsicCharacterPoint (equation t) g)
    (intrinsicCharacterPoint_defect (equation t) g)

/-- Reduction of the whole lifted homomorphism is exactly the original intrinsic map. -/
theorem nilpotentIntrinsicHomLift_reduction :
    Spec.map (CommRingCat.ofHom (coefficientReduction R G I).toRingHom) ≫
      (nilpotentIntrinsicHomLift t ht I hI g).hom.hom.hom.left =
        g.hom.hom.hom.left ≫ originalSmoothCoefficientMap (R ⧸ I) (equation t) := by
  exact (congrArg Over.Hom.left (nilpotentCharacterLift_reduction t ht I hI
    (intrinsicCharacterPoint (equation t) g)
    (intrinsicCharacterPoint_defect (equation t) g))).trans
      (intrinsicCharacterPoint_left (equation t) g)

/-- The original reduction characterizes the lifted group homomorphism uniquely. -/
theorem nilpotentIntrinsicHomLift_unique
    (q : CommGrp.mk (model R G) ⟶ integralSmoothGroup (equation t))
    (hq : Spec.map (CommRingCat.ofHom (coefficientReduction R G I).toRingHom) ≫
      q.hom.hom.hom.left =
        g.hom.hom.hom.left ≫ originalSmoothCoefficientMap (R ⧸ I) (equation t)) :
    q = nilpotentIntrinsicHomLift t ht I hI g := by
  apply CommGrp.hom_ext
  apply nilpotentCharacterLift_unique t ht I hI
    (intrinsicCharacterPoint (equation t) g) (intrinsicCharacterPoint_defect (equation t) g)
  apply Over.OverMorphism.ext
  exact hq.trans (intrinsicCharacterPoint_left (equation t) g).symm

end FLT.Mazur.OneGonSmoothing
