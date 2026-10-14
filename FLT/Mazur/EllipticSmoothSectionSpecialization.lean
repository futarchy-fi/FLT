/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticE0SectionEquiv
public import FLT.Mazur.EllipticPrimeToResidueSpecialization
public import FLT.Mazur.EllipticSmallRamificationSpecialization

/-!
# Arithmetic injectivity of closed restriction of the original smooth sections

Equality on the closed fiber is equality under the original reduction
homomorphism. Prime-to-residue torsion, and residue-prime torsion under the
small ramification bound, therefore remain distinct as geometric sections.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
namespace FLT.Mazur.WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {K : Type u} [Field K] (A : ValuationSubring K) (W : WeierstrassCurve A)
local notation "q" => Spec.map (CommRingCat.ofHom (residue A))

/-- Geometric equality of closed restrictions is exactly arithmetic reduction equality. -/
theorem e0SmoothSectionEquiv_special_eq_iff (P Q : ellipticE0 A W) :
    q ≫ (e0SmoothSectionEquiv A W P).left =
        q ≫ (e0SmoothSectionEquiv A W Q).left ↔
      smoothReductionHom A W P = smoothReductionHom A W Q := by
  rw [e0SmoothSectionEquiv_special, e0SmoothSectionEquiv_special]
  constructor
  · intro h
    apply projectiveToSmoothOver_injective W
    exact Over.OverMorphism.ext h
  · rintro h
    rw [h]

variable [IsAdicComplete (maximalIdeal A) A]

/-- The actual closed restriction distinguishes prime-to-residue torsion sections. -/
theorem e0SmoothSectionEquiv_special_injOn_torsion
    (p n : ℕ) [CharP (ResidueField A) p] (hn : ¬ p ∣ n) :
    Set.InjOn (fun P : ellipticE0 A W => q ≫ (e0SmoothSectionEquiv A W P).left)
      {P | n • P = 0} := by
  intro P hP Q hQ h
  exact smoothReductionHom_injOn_torsion_of_not_dvd A W p n hn hP hQ
    ((e0SmoothSectionEquiv_special_eq_iff A W P Q).mp h)

/-- A prime-to-residue torsion section is determined by its geometric closed restriction. -/
theorem e0SmoothSectionEquiv_special_torsion_eq_iff
    (p n : ℕ) [CharP (ResidueField A) p] (hn : ¬ p ∣ n)
    (P Q : ellipticE0 A W) (hP : n • P = 0) (hQ : n • Q = 0) :
    q ≫ (e0SmoothSectionEquiv A W P).left =
      q ≫ (e0SmoothSectionEquiv A W Q).left ↔ P = Q :=
  ⟨fun h => e0SmoothSectionEquiv_special_injOn_torsion A W p n hn hP hQ h,
    fun h => by rw [h]⟩

variable [IsDiscreteValuationRing A]

/-- The same geometric restriction is injective on residue-prime torsion at small ramification. -/
theorem e0SmoothSectionEquiv_special_injOn_small_ramification
    (p : ℕ) [Fact p.Prime] (hp0 : (p : A) ≠ 0)
    (he : RaynaudParameters.order (p : A) < p - 1) :
    Set.InjOn (fun P : ellipticE0 A W => q ≫ (e0SmoothSectionEquiv A W P).left)
      {P | p • P = 0} := by
  intro P hP Q hQ h
  exact smoothReduction_prime_torsion_injective_small_ramification A W p hp0 he P Q hP hQ
    ((e0SmoothSectionEquiv_special_eq_iff A W P Q).mp h)

end FLT.Mazur.WeierstrassIntegralChart
