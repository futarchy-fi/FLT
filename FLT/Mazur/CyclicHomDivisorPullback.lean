/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicHomSourceIdealPullback
public import FLT.Mazur.CyclicHomDivisorProduct

/-!
# Cartesian comparison of the actual cyclic divisor

The full ideal comparison induces a cartesian map of the actual finite flat
divisors, retaining the closed immersion into the original source curve.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.UniversalWeierstrass
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] {T U : Scheme}
  (f : T ⟶ (cyclicHomAuxiliaryScheme n).left) (k : U ⟶ T)

/-- The full cyclic divisor map induced by the cartesian source comparison. -/
def cyclicHomDivisorPullbackMap :
    (cyclicHomDivisor n (k ≫ f)).left ⟶ (cyclicHomDivisor n f).left :=
  Scheme.IdealSheafData.subschemeMap _ _ (cyclicHomSourcePullbackMap n f k)
    (Scheme.IdealSheafData.le_map_iff_comap_le.mpr (cyclicHomSourceIdeal_pullback n f k).ge)

/-- The divisor comparison retains its original ambient closed immersion. -/
@[reassoc] theorem cyclicHomDivisorPullbackMap_inclusion :
    cyclicHomDivisorPullbackMap n f k ≫ (cyclicHomSourceIdeal n f).subschemeι =
      (cyclicHomSourceIdeal n (k ≫ f)).subschemeι ≫ cyclicHomSourcePullbackMap n f k :=
  Scheme.IdealSheafData.subschemeMap_subschemeι _ _ _ _

/-- The full closed divisor square is cartesian, including its nilpotent structure. -/
theorem cyclicHomDivisorPullbackMap_closed_isPullback :
    IsPullback (cyclicHomSourceIdeal n (k ≫ f)).subschemeι
      (cyclicHomDivisorPullbackMap n f k) (cyclicHomSourcePullbackMap n f k)
      (cyclicHomSourceIdeal n f).subschemeι := by
  apply isPullback_of_isClosedImmersion
  · exact (cyclicHomDivisorPullbackMap_inclusion n f k).symm
  · simpa only [Scheme.IdealSheafData.ker_subschemeι] using
      (cyclicHomSourceIdeal_pullback n f k).symm

/-- The actual finite locally free divisor is cartesian over the parameter base. -/
theorem cyclicHomDivisorPullbackMap_isPullback :
    IsPullback (cyclicHomDivisorPullbackMap n f k) (cyclicHomDivisor n (k ≫ f)).hom
      (cyclicHomDivisor n f).hom k :=
  (cyclicHomDivisorPullbackMap_closed_isPullback n f k).flip.paste_vert
    (cyclicHomSourcePullbackMap_isPullback n f k)

/-- Comparison with the actual pulled-back divisor in the category over the test base. -/
def cyclicHomDivisorPullbackIso :
    cyclicHomDivisor n (k ≫ f) ≅ (Over.pullback k).obj (cyclicHomDivisor n f) :=
  Over.isoMk (cyclicHomDivisorPullbackMap_isPullback n f k).isoPullback
    (cyclicHomDivisorPullbackMap_isPullback n f k).isoPullback_hom_snd

/-- Projection from the comparison is the original divisor map. -/
@[reassoc] theorem cyclicHomDivisorPullbackIso_fst :
    (cyclicHomDivisorPullbackIso n f k).hom.left ≫
      pullback.fst (cyclicHomDivisor n f).hom k = cyclicHomDivisorPullbackMap n f k :=
  (cyclicHomDivisorPullbackMap_isPullback n f k).isoPullback_hom_fst

end FLT.Mazur.UniversalWeierstrass
