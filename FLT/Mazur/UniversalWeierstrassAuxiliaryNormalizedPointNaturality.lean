/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.UniversalWeierstrassAuxiliaryNormalizedLevelPoint

/-!
# Naturality of the actual normalized level-four point

The representing equation point and its factorization through the faithful
open commute with every test-scheme morphism over the coefficient ring.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry MonObj

namespace FLT.Mazur.UniversalWeierstrass

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {R : Type} [CommRing R] (g : AuxiliarySectionRing →+* R)
  {T U : Over (Spec (.of R))}
  (p : (Over.map (auxiliaryCoefficientBase g)).obj T ⟶ levelFour) (k : U ⟶ T)

attribute [local irreducible] auxiliaryNormalizedLevelPoint
  auxiliaryNormalizedUniversalMarking

/-- The represented full marking is natural as an actual equation-scheme morphism. -/
theorem auxiliaryNormalizedHomPoint_natural :
    auxiliaryNormalizedHomPoint g ((Over.map (auxiliaryCoefficientBase g)).map k ≫ p) =
      (Over.map (auxiliaryNormalizedCoefficientBase g)).map k ≫
        auxiliaryNormalizedHomPoint g p := by
  apply AuxiliaryLevel.homScheme_ext
  intro a
  apply Over.OverMorphism.ext
  have hU := congrArg (fun m => (m a).left) (auxiliaryNormalizedHomPoint_marking g
    ((Over.map (auxiliaryCoefficientBase g)).map k ≫ p))
  have hT := congrArg (fun m => (m a).left) (auxiliaryNormalizedHomPoint_marking g p)
  have hn := congrArg Over.Hom.left (auxiliaryNormalizedUniversalMarking_natural g p k a)
  rw [Over.comp_left, ← hU, ← hT] at hn
  change (auxiliaryNormalizedHomPoint g _).left ≫
      (AuxiliaryLevel.value universalGroup (Labels 4) a).left =
    k.left ≫ (auxiliaryNormalizedHomPoint g p).left ≫
      (AuxiliaryLevel.value universalGroup (Labels 4) a).left at hn
  change _ = (k.left ≫ (auxiliaryNormalizedHomPoint g p).left) ≫
    (AuxiliaryLevel.value universalGroup (Labels 4) a).left
  exact hn.trans (Category.assoc _ _ _).symm

/-- Passing to the faithful open retains naturality of the entire normalized auxiliary point. -/
theorem auxiliaryNormalizedLevelPoint_natural :
    auxiliaryNormalizedLevelPoint g ((Over.map (auxiliaryCoefficientBase g)).map k ≫ p) =
      (Over.map (auxiliaryNormalizedCoefficientBase g)).map k ≫
        auxiliaryNormalizedLevelPoint g p := by
  apply (AuxiliaryLevel.faithfulRepresentation universalGroup (Labels 4) _).injective
  apply Subtype.ext
  change auxiliaryNormalizedLevelPoint g _ ≫ auxiliaryInclusion 4 =
    ((Over.map (auxiliaryNormalizedCoefficientBase g)).map k ≫
      auxiliaryNormalizedLevelPoint g p) ≫ auxiliaryInclusion 4
  rw [Category.assoc, auxiliaryNormalizedLevelPoint_inclusion,
    auxiliaryNormalizedLevelPoint_inclusion, auxiliaryNormalizedHomPoint_natural]

/-- Naturality retains the actual underlying scheme maps, including on nonaffine tests. -/
theorem auxiliaryNormalizedLevelPoint_natural_left :
    (auxiliaryNormalizedLevelPoint g ((Over.map (auxiliaryCoefficientBase g)).map k ≫ p)).left =
      k.left ≫ (auxiliaryNormalizedLevelPoint g p).left :=
  congrArg Over.Hom.left (auxiliaryNormalizedLevelPoint_natural g p k)

end FLT.Mazur.UniversalWeierstrass
