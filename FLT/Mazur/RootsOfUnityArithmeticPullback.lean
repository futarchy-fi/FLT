/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CharacterSchemeBaseChange
public import FLT.Mazur.ArithmeticRootsOfUnitySections

/-!
# Actual root sections on arithmetic pullbacks

The original character subgroup pulled back along any ring extension has the
expected root-coordinate sections. Their projection is the original evaluation
map over the old base, not an unspecified isomorphic finite scheme.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory

namespace FLT.Mazur.RootsOfUnityArithmeticPullback

open CharacterAlgebraScalarExtension CharacterSchemeBaseChange RootsOfUnityAlgebraPoints

variable (R A : Type) [CommRing R] [CommRing A] [Algebra R A] (n : ℕ) [NeZero n]

/-- The actual roots-of-unity scheme over the extension is the original scheme pullback. -/
def comparison : RootsOfUnityScheme.model A n ≅
    (Over.pullback (baseMap R A)).obj (RootsOfUnityScheme.model R n) :=
  overIso R A (ZMod n)

omit [NeZero n] in
/-- The comparison retains the original character coefficient map. -/
@[reassoc] theorem comparison_fst :
    (comparison R A n).hom.left ≫ pullback.fst (RootsOfUnityScheme.model R n).hom
      (baseMap R A) = Spec.map (CommRingCat.ofHom (coeff R A (ZMod n)).toRingHom) :=
  overIso_fst R A (ZMod n)

/-- Root evaluation is compatible with changing the character coefficients. -/
theorem evalRoot_coeff (a : Aˣ) (ha : a ^ n = 1) :
    ((evalRoot (R := A) n a ha).restrictScalars R).comp (coeff R A (ZMod n)) =
      evalRoot (R := R) n a ha := by
  apply AddMonoidAlgebra.algHom_ext
  · intro i
    simp [coeff, evalRoot_single]
  · ext

/-- A torsion unit supplies a section of the actual categorical subgroup pullback. -/
def rootSection (a : Aˣ) (ha : a ^ n = 1) :
    𝟙_ (Over (Spec (.of A))) ⟶
      (Over.pullback (baseMap R A)).obj (RootsOfUnityScheme.model R n) :=
  ArithmeticRootsOfUnitySections.rootSection A n a ha ≫ (comparison R A n).hom

/-- Projection of that section is the original root-evaluation scheme map. -/
@[reassoc] theorem rootSection_fst (a : Aˣ) (ha : a ^ n = 1) :
    (rootSection R A n a ha).left ≫ pullback.fst (RootsOfUnityScheme.model R n).hom
      (baseMap R A) = Spec.map (CommRingCat.ofHom (evalRoot (R := R) n a ha).toRingHom) := by
  change (ArithmeticRootsOfUnitySections.rootSection A n a ha).left ≫
    (comparison R A n).hom.left ≫ _ = _
  rw [comparison_fst]
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  exact congrArg (fun f ↦ Spec.map (CommRingCat.ofHom (AlgHom.toRingHom f)))
    (evalRoot_coeff R A n a ha)

/-- Restricting the character root point to the Laurent algebra retains its exact unit. -/
theorem evalRoot_restriction (a : Aˣ) (ha : a ^ n = 1) :
    (evalRoot (R := R) n a ha).comp (RootsOfUnityAlgebra.restriction R n).toAlgHom =
      LaurentUnitPoints.evalUnit (R := R) a := by
  apply LaurentUnitPoints.pointsEquiv.injective
  change LaurentUnitPoints.pointUnit _ = LaurentUnitPoints.pointUnit _
  rw [pointRoot_restriction, pointRoot_evalRoot, LaurentUnitPoints.pointUnit_evalUnit]

/-- The original subgroup inclusion is the prescribed Laurent evaluation on the cover. -/
@[reassoc] theorem rootSection_inclusion_fst (a : Aˣ) (ha : a ^ n = 1) :
    (rootSection R A n a ha).left ≫ pullback.fst (RootsOfUnityScheme.model R n).hom
      (baseMap R A) ≫ (RootsOfUnityScheme.inclusion R n).left =
        Spec.map (CommRingCat.ofHom (LaurentUnitPoints.evalUnit (R := R) a).toRingHom) := by
  rw [← Category.assoc, rootSection_fst, RootsOfUnityScheme.inclusion_left, ← Spec.map_comp]
  exact congrArg (fun f ↦ Spec.map (CommRingCat.ofHom (AlgHom.toRingHom f)))
    (evalRoot_restriction R A n a ha)

end FLT.Mazur.RootsOfUnityArithmeticPullback
