/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicAtlasCoverageUnrestricted
public import FLT.Mazur.CyclicHomLocusModuli
public import FLT.Mazur.OddWeierstrassCyclicHomSourceModuli

/-!
# Actual modular classes on both characteristic charts

Both universal subgroup loci carry ample cyclic levels. Their pullback classes
cover every original smooth ample cyclic object over any base, including
non-etale levels in characteristics two and three.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.CyclicCharacteristicAtlas
open GeneralizedEllipticCurve GeneralizedEllipticCurve.FiniteSubgroup
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n]

/-- Both original characteristic charts carry actual cyclic subgroups. -/
theorem subgroup_isCyclic (b : Bool) : (subgroup n b).IsCyclic := by
  cases b
  · exact UniversalWeierstrass.cyclicHomUniversalSubgroup_isCyclic n
  · exact OddWeierstrassParameter.cyclicHomUniversalSubgroup_isCyclic n

/-- Both original characteristic charts carry ample subgroup divisors. -/
theorem subgroup_isAmple (b : Bool) : (subgroup n b).IsAmple := by
  cases b
  · exact UniversalWeierstrass.cyclicHomUniversalSubgroup_isAmple n
  · exact OddWeierstrassParameter.cyclicHomUniversalSubgroup_isAmple n

/-- The universal class uses the entire original curve and subgroup on each chart. -/
def moduliClass (b : Bool) : ampleCyclicClasses (locus n b) n :=
  Quotient.mk _ ⟨⟨curve n b, subgroup n b⟩, subgroup_isCyclic n b, subgroup_isAmple n b⟩

/-- All original smooth ample cyclic classes are covered without base restrictions. -/
theorem exists_moduli_fppf_cover {S : Scheme} {E : GeneralizedEllipticCurve S}
    [Smooth E.curve.hom] (H : E.FiniteSubgroup n) (hc : H.IsCyclic) (ha : H.IsAmple) :
    ∃ (C : Scheme.Cover.{0} Scheme.fppfPrecoverage S) (b : C.I₀ → Bool)
      (q : ∀ i : C.I₀, C.X i ⟶ locus n (b i)),
      ∀ i, ampleCyclicClassesPullback (q i) n (moduliClass n (b i)) =
        ampleCyclicClassesPullback (C.f i) n (Quotient.mk _ ⟨⟨E, H⟩, hc, ha⟩) := by
  obtain ⟨C, b, q, hq⟩ := exists_original_fppf_cover_unrestricted H hc
  exact ⟨C, b, q, fun i ↦ Quotient.sound (hq i)⟩

end FLT.Mazur.CyclicCharacteristicAtlas
