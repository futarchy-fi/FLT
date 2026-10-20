/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonNilpotentSurjectiveCharacterLift
public import FLT.Mazur.OneGonNilpotentIntrinsicHomLift

/-!
# Intrinsic group homomorphisms lifted along specified surjections

An original homomorphism into the reduced cubic determines a unique actual
homomorphism into the nilpotent smoothing. Reduction uses the given algebra
map, rather than an unspecified quotient presentation.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry MonObj

namespace FLT.Mazur.OneGonSmoothing

open WeierstrassIntegralChart WeierstrassDiagonalizableDefect WeierstrassDividedDepth
open CharacterSchemeBaseChange

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R S G : Type} [CommRing R] [CommRing S] [Algebra R S] [AddCommGroup G]
  (t : R) (ht : IsNilpotent t) (hs : Function.Surjective (algebraMap R S))
  (hk : RingHom.ker (algebraMap R S) ^ 2 = ⊥)
  (g : CommGrp.mk (model S G) ⟶
    integralSmoothGroup ((equation t).map (algebraMap R S)))

/-- The actual point selected by unique lifting along the given surjection. -/
def surjectiveCharacterLift :
    WeierstrassDiagonalizableDefect.Points (equation t) (AddMonoidAlgebra R G) :=
  (nilpotent_surjective_existsUnique_lift t ht hs hk (intrinsicCharacterPoint (equation t) g)
    (intrinsicCharacterPoint_defect (equation t) g)).exists.choose

/-- The constructed point retains the specified intrinsic coefficient reduction. -/
theorem surjectiveCharacterLift_reduction :
    smoothAlgebraReduction (equation t) (characterCoefficientMap (R := R) (S := S))
      (surjectiveCharacterLift t ht hs hk g) = intrinsicCharacterPoint (equation t) g :=
  (nilpotent_surjective_existsUnique_lift t ht hs hk (intrinsicCharacterPoint (equation t) g)
    (intrinsicCharacterPoint_defect (equation t) g)).exists.choose_spec.1

instance surjectiveCharacterLift_isMonHom :
    IsMonHom (surjectiveCharacterLift t ht hs hk g) :=
  (nilpotent_surjective_existsUnique_lift t ht hs hk (intrinsicCharacterPoint (equation t) g)
    (intrinsicCharacterPoint_defect (equation t) g)).exists.choose_spec.2

/-- The lift is an actual homomorphism of the original commutative group schemes. -/
def nilpotentSurjectiveHomLift : CommGrp.mk (model R G) ⟶ integralSmoothGroup (equation t) :=
  InducedCategory.homMk (Grp.homMk (surjectiveCharacterLift t ht hs hk g))

/-- The full original morphism reduces along precisely the specified coefficient map. -/
theorem nilpotentSurjectiveHomLift_reduction :
    Spec.map (CommRingCat.ofHom
        (characterCoefficientMap (R := R) (S := S) (G := G)).toRingHom) ≫
      (nilpotentSurjectiveHomLift t ht hs hk g).hom.hom.hom.left =
        g.hom.hom.hom.left ≫ originalSmoothCoefficientMap S (equation t) := by
  exact (congrArg Over.Hom.left (surjectiveCharacterLift_reduction t ht hs hk g)).trans
    (intrinsicCharacterPoint_left (equation t) g)

/-- Retaining that original reduction uniquely characterizes the homomorphism. -/
theorem nilpotentSurjectiveHomLift_unique
    (q : CommGrp.mk (model R G) ⟶ integralSmoothGroup (equation t))
    (hq : Spec.map (CommRingCat.ofHom
        (characterCoefficientMap (R := R) (S := S) (G := G)).toRingHom) ≫
      q.hom.hom.hom.left =
        g.hom.hom.hom.left ≫ originalSmoothCoefficientMap S (equation t)) :
    q = nilpotentSurjectiveHomLift t ht hs hk g := by
  apply CommGrp.hom_ext
  apply (nilpotent_surjective_existsUnique_lift t ht hs hk
    (intrinsicCharacterPoint (equation t) g)
    (intrinsicCharacterPoint_defect (equation t) g)).unique
  · refine ⟨?_, inferInstance⟩
    apply Over.OverMorphism.ext
    exact hq.trans (intrinsicCharacterPoint_left (equation t) g).symm
  · exact ⟨surjectiveCharacterLift_reduction t ht hs hk g, inferInstance⟩

end FLT.Mazur.OneGonSmoothing
