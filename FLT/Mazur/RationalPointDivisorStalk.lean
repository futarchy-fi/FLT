/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IntegralImageIdealStalk
public import FLT.Mazur.SmoothSectionCartier
public import Mathlib.RingTheory.DiscreteValuationRing.TFAE

/-!
# Rational point factors of full Cartier ideals

A rational point on a separated curve has maximal ideal stalk at its image
and unit ideal stalk elsewhere. Smoothness makes this maximal ideal principal.
On an integral Noetherian curve every Cartier ideal stalk there is a power of it.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.FCurve
open AnnihilatorSubsheaf
set_option backward.isDefEq.respectTransparency false
universe u
variable {k : Type u} [Field k] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of k)) [IsSeparated f]
  (p : Spec (.of k) ⟶ X) (hp : p ≫ f = 𝟙 _)

include hp in
/-- The full rational-point ideal has precisely its one image point as support. -/
theorem rationalPointIdeal_support :
    (p.ker.support : Set X) = {p (IsLocalRing.closedPoint k)} := by
  rw [support_section_ker f p hp]
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact congrArg p (Subsingleton.elim _ _)
  · rintro rfl
    exact Set.mem_range_self _

include hp in
/-- The full point-ideal stalk at the point is the actual maximal ideal. -/
theorem rationalPointIdeal_stalk :
    stalkIdeal p.ker (p (IsLocalRing.closedPoint k)) =
      IsLocalRing.maximalIdeal (X.presheaf.stalk (p (IsLocalRing.closedPoint k))) := by
  let _ := isClosedImmersion_section f p hp
  exact stalkIdeal_image_eq_maximalIdeal p _
    ((stalkClosedPointIso (.of k)).commRingCatIsoToRingEquiv.isField
      (Field.toIsField k))

include hp in
/-- Away from the rational point, its entire ideal stalk is the unit ideal. -/
theorem rationalPointIdeal_stalk_of_ne (x : X)
    (hx : x ≠ p (IsLocalRing.closedPoint k)) : stalkIdeal p.ker x = 1 := by
  rw [Ideal.one_eq_top, ← not_ne_iff, ← mem_support_iff_stalkIdeal_ne_top]
  simpa only [← SetLike.mem_coe, rationalPointIdeal_support f p hp,
    Set.mem_singleton_iff] using hx

include hp in
/-- Smoothness gives a principal maximal ideal at every rational point. -/
theorem rationalPoint_maximalIdeal_isPrincipal [SmoothOfRelativeDimension 1 f] :
    (IsLocalRing.maximalIdeal (X.presheaf.stalk (p (IsLocalRing.closedPoint k)))).IsPrincipal := by
  obtain ⟨a, _, ha⟩ :=
    (smoothSectionCartier f p inferInstance inferInstance hp).1.stalk_generator
      (p (IsLocalRing.closedPoint k))
  rw [rationalPointIdeal_stalk f p hp] at ha
  exact ⟨a, ha⟩

include hp in
/-- Every full Cartier stalk at a smooth rational point is an actual point-ideal power. -/
theorem exists_rationalPointIdeal_stalk_pow [IsIntegral X] [IsLocallyNoetherian X]
    [SmoothOfRelativeDimension 1 f] {I : X.IdealSheafData} (hI : EffectiveCartier I) :
    ∃ n : ℕ, stalkIdeal I (p (IsLocalRing.closedPoint k)) =
      stalkIdeal p.ker (p (IsLocalRing.closedPoint k)) ^ n := by
  let x := p (IsLocalRing.closedPoint k)
  have hne : stalkIdeal I x ≠ ⊥ := by
    obtain ⟨a, ha, he⟩ := hI.stalk_generator x
    rw [he, ne_eq, Ideal.span_singleton_eq_bot]
    exact ha.ne_zero
  rw [rationalPointIdeal_stalk f p hp]
  exact exists_maximalIdeal_pow_eq_of_principal _
    (rationalPoint_maximalIdeal_isPrincipal f p hp) _ hne

end FLT.Mazur.FCurve
