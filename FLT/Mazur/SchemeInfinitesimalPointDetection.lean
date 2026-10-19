/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AdicDiscrepancySeparation
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Stalk

/-!
# Infinitesimal point tests detect full original sections

Positive maximal-ideal powers in the original stalk give compact tests with
singleton image. On a locally Noetherian scheme these tests jointly detect
sections, including nilpotents. No reducedness or flatness of the tests is used.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.SchemeInfinitesimalPointDetection
set_option backward.isDefEq.respectTransparency false
variable (X : Scheme.{0}) (x : X) (k : ℕ)
local notation "A" => X.presheaf.stalk x
local notation "m" => IsLocalRing.maximalIdeal A

/-- The actual positive-order infinitesimal neighborhood in the original stalk. -/
def pointThickening : Scheme := Spec (.of (A ⧸ m ^ (k + 1)))

/-- Its canonical map to the original scheme. -/
def pointThickeningMap : pointThickening X x k ⟶ X :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (m ^ (k + 1)))) ≫ X.fromSpecStalk x

instance pointThickening_affine : IsAffine (pointThickening X x k) := by
  unfold pointThickening
  infer_instance

/-- Every infinitesimal test point has the same unchanged original center. -/
theorem pointThickeningMap_apply (y : pointThickening X x k) :
    pointThickeningMap X x k y = x := by
  let Q : PrimeSpectrum A :=
    PrimeSpectrum.comap (Ideal.Quotient.mk (m ^ (k + 1))) y
  have hpow : m ^ (k + 1) ≤ Q.asIdeal := by
    change m ^ (k + 1) ≤ y.asIdeal.comap _
    simpa only [Ideal.mk_ker] using
      (Ideal.ker_le_comap (Ideal.Quotient.mk (m ^ (k + 1))) :
        RingHom.ker _ ≤ y.asIdeal.comap _)
  have hmQ : m ≤ Q.asIdeal := Q.isPrime.le_of_pow_le hpow
  have hQ : Q = IsLocalRing.closedPoint A := by
    apply PrimeSpectrum.ext
    exact ((IsLocalRing.maximalIdeal.isMaximal A).eq_of_le Q.isPrime.ne_top hmQ).symm
  change X.fromSpecStalk x Q = x
  rw [hQ, Scheme.fromSpecStalk_closedPoint]

/-- Scheme pullback to the test is precisely the quotient of the original germ. -/
theorem pointThickeningMap_eq_zero_iff (a : Γ(X, ⊤)) :
    (pointThickeningMap X x k).appTop a = 0 ↔
      X.presheaf.germ ⊤ x trivial a ∈ m ^ (k + 1) := by
  let q := CommRingCat.ofHom (Ideal.Quotient.mk (m ^ (k + 1)))
  have hfac : pointThickeningMap X x k ≫ X.toSpecΓ =
      Spec.map (X.presheaf.germ ⊤ x trivial ≫ q) := by
    rw [pointThickeningMap, Category.assoc, Scheme.fromSpecStalk_toSpecΓ,
      ← Spec.map_comp]
  have he := congrArg (fun f ↦ f.appTop) hfac
  rw [Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop] at he
  have hv := ConcreteCategory.congr_hom he ((Scheme.ΓSpecIso Γ(X, ⊤)).inv a)
  simp only [ConcreteCategory.comp_apply, Iso.inv_hom_id_apply] at hv
  have hn := ConcreteCategory.congr_hom
    (Scheme.ΓSpecIso_inv_naturality (X.presheaf.germ ⊤ x trivial ≫ q)) a
  simp only [ConcreteCategory.comp_apply] at hn
  have hval : (pointThickeningMap X x k).appTop a =
      (Scheme.ΓSpecIso (.of (A ⧸ m ^ (k + 1)))).inv
        (Ideal.Quotient.mk (m ^ (k + 1)) (X.presheaf.germ ⊤ x trivial a)) :=
    hv.trans hn.symm
  rw [hval]
  constructor
  · intro hz
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    apply (Scheme.ΓSpecIso (.of (A ⧸ m ^ (k + 1)))).commRingCatIsoToRingEquiv.symm.injective
    exact hz.trans (map_zero _).symm
  · intro hz
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hz, map_zero]

/-- All positive infinitesimal orders kill a germ only when the original germ is zero. -/
theorem germ_eq_zero [IsLocallyNoetherian X] (a : Γ(X, ⊤))
    (ha : ∀ k : ℕ, (pointThickeningMap X x k).appTop a = 0) :
    X.presheaf.germ ⊤ x trivial a = 0 := by
  apply AdicDiscrepancySeparation.eq_zero_of_local m (Ideal.IsMaximal.ne_top inferInstance)
  intro k
  simpa only [smul_eq_mul, ← Ideal.one_eq_top, mul_one] using
    (pointThickeningMap_eq_zero_iff X x k a).mp (ha k)

/-- The full family of actual infinitesimal points detects original global sections. -/
theorem section_eq_zero [IsLocallyNoetherian X] (a : Γ(X, ⊤))
    (ha : ∀ (x : X) (k : ℕ), (pointThickeningMap X x k).appTop a = 0) : a = 0 := by
  apply TopCat.Presheaf.section_ext X.sheaf
  intro x hx
  rw [map_zero]
  exact germ_eq_zero X x a (ha x)

end FLT.Mazur.SchemeInfinitesimalPointDetection
