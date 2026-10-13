/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OddWeierstrassCyclicHomSourcePullback
public import FLT.Mazur.OddWeierstrassCyclicHomDivisorPullback
public import FLT.Mazur.RetainedSubgroupCartierMarking

/-!
# Retaining any original cyclic source subgroup under parameter change

The construction pulls back the original subgroup and transports it through
the full source comparison. It preserves Cartier generators and orbit ideals.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory
namespace FLT.Mazur.OddWeierstrassParameter
open GeneralizedEllipticCurve GeneralizedEllipticCurve.FiniteSubgroup
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {T U : Scheme} {n : ℕ} [NeZero n]
  (f : T ⟶ (cyclicHomAuxiliaryScheme n).left) (k : U ⟶ T)
  (H : (cyclicHomSourceCurve n f).FiniteSubgroup n)

/-- Keep the pulled original subgroup on the directly reconstructed cyclic source. -/
def cyclicHomRetainedPullback : (cyclicHomSourceCurve n (k ≫ f)).FiniteSubgroup n :=
  (H.baseChange k).transport (cyclicHomSourcePullbackIso n f k).symm

/-- The retained subgroup agrees with the entire original pulled family. -/
def cyclicHomRetainedPullbackIso :
    CompatibleIso (cyclicHomRetainedPullback f k H) (H.baseChange k) :=
  ((H.baseChange k).transportCompatibleIso (cyclicHomSourcePullbackIso n f k).symm).symm

/-- A pulled original Cartier generator remains Cartier in the direct source. -/
theorem cyclicHomRetainedPullback_generator {P : 𝟙_ (Over T) ⟶ H.carrier}
    (hP : H.IsCartierGenerator P) :
    (cyclicHomRetainedPullback f k H).IsCartierGenerator (H.pullGenerator k P) :=
  (H.baseChange k).transport_cartierGenerator (cyclicHomSourcePullbackIso n f k).symm
    (hP.baseChange H k)

/-- The whole orbit ideal, including repeated factors, survives the refinement. -/
theorem cyclicHomRetainedPullback_ideal (hH : H.ideal = cyclicHomSourceIdeal n f) :
    (cyclicHomRetainedPullback f k H).ideal = cyclicHomSourceIdeal n (k ≫ f) := by
  let a := (H.baseChange k).transportCompatibleIso (cyclicHomSourcePullbackIso n f k).symm
  have hi := ideal_transport (H.baseChange k) _ a.curve a.subgroup a.compatible
  change _ = (H.baseChange k).ideal.comap (cyclicHomSourcePullbackIso n f k).hom.curve.left at hi
  rw [baseChange_ideal, hH, ← Scheme.IdealSheafData.comap_comp] at hi
  exact hi.trans (cyclicHomSourceIdeal_pullback n f k).symm

end FLT.Mazur.OddWeierstrassParameter
