/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteBoundaryTestMarking
public import FLT.Mazur.PolygonCompleteBoundaryCartesian
public import FLT.Mazur.CyclicMarkingOrbitDivisor

/-!
# The full original subgroup divisor on arbitrary boundary tests

The actual cyclic parameter sections cut out the original complete subgroup
after arbitrary boundary base change. Their product retains its relative
Cartier property, finite degree and ample divisor line.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonUniversalAction CyclicBoundaryParameter GeneralizedEllipticCurve FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
  {T : Scheme} (g : T ⟶ Spec (.of K))
  (a : UniversalWeierstrass.Labels 4 →* (Over.mk g ⟶ G K n))
  (b : UniversalWeierstrass.Labels 3 →* (Over.mk g ⟶ G K n))
local notation "J" => completeClosedFiniteSubgroup K n h
local notation "hP" => completeClosedGenerator_isCartierGenerator K n h
local notation "p" => PolygonCyclicAtlas.normalization K n h
local notation "q" => PolygonCyclicAtlas.nodes K n h
local notation "hn" => (Nat.lt_of_lt_of_le (Nat.succ_pos 1) h)
local notation "hp" => PolygonCyclicPushout.isPushout K n h hn
local notation "E" => PolygonGeneralizedCurve.curve K n hn p q hp
local notation "f" => completeBoundaryTestParameter K n h g a b

/-- The product of all actual cyclic labels, in the original pulled-back curve. -/
def completeBoundaryTestIdeal : ((E).baseChange g).curve.left.IdealSheafData :=
  ∏ i : Fin n, ((markedSection (G K n) n g (f) (1, 1, .ofAdd (i.val : ZMod n))) ≫
    ((E).baseChange g).inclusion).left.ker

/-- The actual test ideal is exactly the original base-changed complete closed subgroup. -/
theorem completeBoundaryTestIdeal_eq :
    completeBoundaryTestIdeal K n h g a b = ((J).baseChange g).ideal := by
  unfold completeBoundaryTestIdeal
  simp only [completeBoundaryTestParameter_generator]
  exact ((J).baseChange g).generatorCurveMarking_ideal ((E).baseChange g)
    ((hP).baseChange J g)

/-- The actual test retains the original full complete-family ideal. -/
theorem completeBoundaryTestIdeal_original :
    completeBoundaryTestIdeal K n h g a b =
      (completeMarkingDivisor K n h).comap (completeBoundaryParameterMap K n h g) := by
  rw [completeBoundaryTestIdeal_eq, completeBoundarySubgroup_ideal]

/-- The original relative Cartier property holds on arbitrary, possibly nonreduced tests. -/
theorem completeBoundaryTestIdeal_cartier :
    RelativeEffectiveCartier ((E).baseChange g).curve.hom
      (completeBoundaryTestIdeal K n h g a b) := by
  rw [completeBoundaryTestIdeal_eq]
  exact ((hP).baseChange J g).2.1

/-- Every original cyclic label contributes to the actual finite locally free degree. -/
theorem completeBoundaryTestIdeal_degree :
    FiniteLocallyFreeDegree ((completeBoundaryTestIdeal K n h g a b).subschemeι ≫
      ((E).baseChange g).curve.hom) n := by
  rw [completeBoundaryTestIdeal_original]
  exact completeCyclicDivisor_degree K n h (g ≫ completeClosedBase K)
    (completeBoundaryParameterMap K n h g) ((E).baseChange g).curve.hom
    (completeBoundaryParameter_isPullback K n h g)

/-- The actual complete-family subgroup's ample line is retained on every boundary test. -/
theorem completeBoundaryTestIdeal_ample :
    RelativeAmple ((E).baseChange g).curve.hom
      (divisorLineBundle (completeBoundaryTestIdeal K n h g a b)
        (completeBoundaryTestIdeal_cartier K n h g a b).1) := by
  obtain ⟨hI, hA⟩ := completeBoundarySubgroup_isAmple K n h g
  simpa only [divisorLineBundle, completeBoundaryTestIdeal_eq] using hA

end FLT.Mazur.PolygonInfinitesimalStages
