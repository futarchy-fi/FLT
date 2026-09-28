/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.CartierDualTorsor
public import FLT.GroupScheme.CartierDualPointFiltration
public import FLT.GaloisRepresentation.HardlyRamified.CharacterCyclotomicPurity

/-!
# Cyclotomic purity of integral cube-root filtrations

Integral dual torsors show that the Cartier dual of a cube-root filtration
is étale. Its full character group has a trivial-three filtration, so the
constant-filtration arithmetic forces trivial dual action. Character
separation then gives cyclotomic scalar action on the original points.
-/

@[expose] public noncomputable section

namespace ThreeAdicPlan

variable {R : Type} [CommRing R] [Algebra R ℚ] [IsDomain R] [IsPrincipalIdealRing R]

/-- The dual of the zero group again has the base ring as its coordinate algebra. -/
def FiniteFlatObject.cartierDualCoordinateEquivOfTrivial (H : FiniteFlatObject R)
    (e : H.model.CoordinateRing ≃ₐ[R] R) :
    H.cartierDual.model.CoordinateRing ≃ₐ[R] R :=
  AlgEquiv.ofBijective (Bialgebra.counitAlgHom R H.cartierDual.model.CoordinateRing) (by
    constructor
    · intro φ ψ h
      apply WithConv.ext
      ext a
      have ha : algebraMap R H.model.CoordinateRing (e a) = a := by
        apply e.injective
        simp
      rw [← ha]
      change φ.ofConv (algebraMap R H.model.CoordinateRing (e a)) =
        ψ.ofConv (algebraMap R H.model.CoordinateRing (e a))
      rw [Algebra.algebraMap_eq_smul_one, map_smul, map_smul]
      exact congrArg (e a • ·) h
    · intro r
      exact ⟨algebraMap R H.cartierDual.model.CoordinateRing r, by simp⟩)

/-- A filtration with étale Cartier-dual factors has étale Cartier dual. -/
theorem HasFiltration.cartierDual_etale {H Q : FiniteFlatObject R}
    (hF : HasFiltration H Q) (hQ : Algebra.Etale R Q.cartierDual.model.CoordinateRing) :
    Algebra.Etale R H.cartierDual.model.CoordinateRing := by
  induction hF with
  | @zero H Q e => exact Algebra.Etale.of_equiv (H.cartierDualCoordinateEquivOfTrivial e).symm
  | single _ => exact hQ
  | extension E hA ih =>
    let := hQ
    let := ih hQ
    exact E.cartierDual_etale

/-- The Cartier dual of any integral cube-root filtration is étale over `ℤ[1/2]`. -/
theorem HasFiltration.muThree_cartierDual_etale {H : FiniteFlatObject ZInvTwo}
    (hF : HasFiltration H muThree) :
    Algebra.Etale ZInvTwo H.cartierDual.model.CoordinateRing :=
  hF.cartierDual_etale ThreeAdicPlan.muThree_cartierDual_etale

/-- The full geometric character group of a cube-root filtration has trivial Galois action. -/
theorem pure_one_characterDual_of_muThree_filtration (H : FiniteFlatObject ZInvTwo)
    (hF : HasFiltration H muThree) :
    Pure H.points.characterDual
      (1 : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → ℤ) := by
  obtain ⟨F⟩ := hF.cartierDualTrivialThreePoints
  let M : FiniteEtaleModel ZInvTwo H.cartierDual.points :=
    { toHasFiniteFlatModel := H.cartierDual.model, etale := hF.muThree_cartierDual_etale }
  have hp := H.cartierDual.points.pure_one_of_etale_trivialThreeFiltration F M
  intro σ ψ
  obtain ⟨p, rfl⟩ := H.cartierDualPoints_bijective.2 ψ
  change σ • H.cartierDualPoints p = (1 : ℤ) • H.cartierDualPoints p
  rw [one_smul, ← map_smul]
  exact congrArg H.cartierDualPoints (by simpa using hp σ p)

/-- Scalar action on a module killed by `p^n` depends only on reduction modulo `p^n`. -/
theorem padic_smul_eq_nsmul_of_pow_kills {W : Type*} [AddCommGroup W]
    (p n : ℕ) [Fact p.Prime] [Module ℤ_[p] W]
    (hkill : ∀ w : W, (p ^ n) • w = 0) (r : ℤ_[p]) (w : W) :
    r • w = (r.toZModPow n).val • w := by
  have hmem : r - (r.toZModPow n).val ∈ Ideal.span {(p : ℤ_[p]) ^ n} := by
    rw [← PadicInt.ker_toZModPow, RingHom.mem_ker]
    simp
  obtain ⟨s, hs⟩ := (Ideal.mem_span_singleton.mp hmem)
  have hz : (r - (r.toZModPow n).val) • w = 0 := by
    rw [hs, mul_comm, mul_smul, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul, hkill, smul_zero]
  simpa only [sub_smul, sub_eq_zero, Nat.cast_smul_eq_nsmul] using hz

/-- Cyclotomic purity holds for every three-adic module structure on the point group. -/
theorem pure_cyclotomic_of_muThree_filtration (H : FiniteFlatObject ZInvTwo)
    [Module ℤ_[3] H.points] (hD : InCategoryD H) (hF : HasFiltration H muThree) :
    Pure H.points (fun σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ ↦
      (cyclotomicCharacter (AlgebraicClosure ℚ) 3 σ.toRingEquiv).val) := by
  obtain ⟨n, hn⟩ := hD.threePrimary
  have hkill (w : H.points) : (3 ^ n) • w = 0 := by
    rw [← hn]
    exact card_nsmul_eq_zero'
  intro σ w
  rw [padic_smul_eq_nsmul_of_pow_kills 3 n hkill]
  exact H.points.cyclotomic_nsmul_of_characterDual_trivial 3 n hkill
    (pure_one_characterDual_of_muThree_filtration H hF) σ w

/-- The canonical finite-level three-adic scalar action on a category-D point group. -/
abbrev InCategoryD.pointModule {H : FiniteFlatObject ZInvTwo} (hD : InCategoryD H) :
    Module ℤ_[3] H.points :=
  primePowerModule 3 hD.threePrimary.choose (fun w ↦ by
    rw [← hD.threePrimary.choose_spec]
    exact card_nsmul_eq_zero')

/-- A category-D object filtered by cube-root groups has pointwise three-adic
cyclotomic action on its full geometric point group, with its canonical scalar action. -/
theorem D_multiplicative_three_cyclotomic (H : FiniteFlatObject ZInvTwo)
    (hD : InCategoryD H) (hF : HasFiltration H muThree) :
    letI := hD.pointModule
    Pure H.points (fun σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ ↦
      (cyclotomicCharacter (AlgebraicClosure ℚ) 3 σ.toRingEquiv).val) := by
  let := hD.pointModule
  exact pure_cyclotomic_of_muThree_filtration H hD hF

end ThreeAdicPlan
