/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertBasisNeighborhoodBaseChange
public import FLT.Mazur.HilbertBasisSchemeCover
public import FLT.Mazur.HilbertPolynomialBasisNaturality

/-!
# A pulled-back principal cover of the intrinsic basis scheme

The neighborhoods pulled back from the original base cover the full intrinsic
basis scheme after any scalar extension of a finitely presented flat family.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace FLT.Mazur.HilbertChart

set_option backward.isDefEq.respectTransparency false

variable (R : Type u) [CommRing R] (I : Type u) (d : ℕ)
variable (w : Fin d → MvPolynomial I R)
variable (S : Type u) [CommRing S] [Algebra R S] (J : Ideal (MvPolynomial I S))
variable [Module.FinitePresentation S (MvPolynomial I S ⧸ J)]
variable [Module.Flat S (MvPolynomial I S ⧸ J)]
variable (T : Type u) [CommRing T] [Algebra S T] [Algebra R T] [IsScalarTower R S T]

local instance : Module.FinitePresentation T
    (MvPolynomial I T ⧸ J.map (MvPolynomial.map (algebraMap S T))) :=
  polynomialQuotient_finitePresentation_baseChange I S J T

/-- In scheme notation the intrinsic basis open is precisely the inverse image. -/
theorem polynomialBasisOpen_preimage :
    polynomialBasisOpen R I d w T (J.map (MvPolynomial.map (algebraMap S T))) =
      (Spec.map (CommRingCat.ofHom (algebraMap S T))) ⁻¹ᵁ
        polynomialBasisOpen R I d w S J :=
  polynomialBasisOpen_baseChange R I d w S J T

/-- The natural map between the actual intrinsic basis schemes. -/
def polynomialBasisBaseChangeMorphism :
    polynomialBasisScheme R I d w T (J.map (MvPolynomial.map (algebraMap S T))) ⟶
      polynomialBasisScheme R I d w S J :=
  (Spec.map (CommRingCat.ofHom (algebraMap S T))).resLE _ _
    (polynomialBasisOpen_preimage R I d w S J T).le

/-- The neighborhoods from the original base cover the entire new intrinsic basis scheme. -/
def polynomialBasisBaseChangeCover :
    (polynomialBasisScheme R I d w T (J.map (MvPolynomial.map (algebraMap S T)))).OpenCover where
  I₀ := PolynomialBasisNeighborhoods R I d w S J
  X r := (polynomialBasisSchemeCover R I d w T
    (J.map (MvPolynomial.map (algebraMap S T)))).X (baseChangeNeighborhood R I d w S J T r)
  f r := (polynomialBasisSchemeCover R I d w T
    (J.map (MvPolynomial.map (algebraMap S T)))).f (baseChangeNeighborhood R I d w S J T r)
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨fun x ↦ ?_, fun r ↦ inferInstance⟩
    have hx : PrimeSpectrum.comap (algebraMap S T) x.1 ∈ polynomialBasisOpen R I d w S J := by
      exact (polynomialBasisOpen_preimage R I d w S J T).le x.2
    obtain ⟨r, hr⟩ := exists_polynomialBasisNeighborhood R I d w S J _ hx
    refine ⟨r, ⟨x.1, hr⟩, ?_⟩
    apply Subtype.ext
    exact Scheme.homOfLE_apply (neighborhood_basicOpen_le R I d w T
      (J.map (MvPolynomial.map (algebraMap S T))) (baseChangeNeighborhood R I d w S J T r))
      ⟨x.1, hr⟩

end FLT.Mazur.HilbertChart
