/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ClosedOrbitKernel
public import FLT.Mazur.TorusCyclotomicGenerator

/-!
# The intrinsic full orbit product in the roots-of-unity scheme

The cyclotomic equation is pulled back from the torus to the entire roots
scheme. Its full product is zero there, including nilpotent roots and repeated
specialized sections. Every closed embedding therefore retains containment in
its actual ambient orbit divisor.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory MonObj

namespace FLT.Mazur.RootsOfUnityIntrinsicOrbit

open IntegralCyclotomicCoordinates ArithmeticRootsOfUnitySections

set_option backward.isDefEq.respectTransparency false

variable {R : Type} [CommRing R] (n : ℕ) [NeZero n] (φ : Coordinate n →+* R)

/-- The actual specialized cyclotomic section in the original character scheme. -/
def generator : 𝟙_ (Over (Spec (.of R))) ⟶ RootsOfUnityScheme.model R n :=
  rootSection R n (Units.map φ.toMonoidHom (rootUnit n))
    (GeneralizedEllipticCurve.cyclotomicUnit_pow n φ)

/-- The intrinsic generator satisfies the full specified torsion relation. -/
theorem generator_pow : generator n φ ^ n = 1 := section_pow_order R n _ _

/-- Each original power has its exact Laurent unit coordinate after the roots inclusion. -/
theorem generator_orbit (k : ℕ) :
    (generator n φ ^ k) ≫ RootsOfUnityScheme.inclusion R n =
      ArithmeticTorusPoints.point R ((Units.map φ.toMonoidHom (rootUnit n)) ^ k) :=
  section_pow_inclusion R n _ _ k

/-- The full product of all generator-section kernels is zero on the entire roots scheme. -/
theorem orbit_product_zero : ∏ i : Fin n, (generator n φ ^ i.val).left.ker = ⊥ := by
  let j := (RootsOfUnityScheme.inclusion R n).left
  let i := fun k : Fin n ↦ (generator n φ ^ k.val).left
  let _ : IsAffineHom (MultiplicativeGroupScheme.gm R).hom :=
    inferInstanceAs (IsAffineHom (Spec.map
      (CommRingCat.ofHom (algebraMap R (LaurentPolynomial R)))))
  let _ : ∀ k, IsClosedImmersion (i k ≫ j) := fun k ↦
    FCurve.isClosedImmersion_section (MultiplicativeGroupScheme.gm R).hom
      ((generator n φ ^ k.val) ≫ RootsOfUnityScheme.inclusion R n).left (Over.w _)
  have h : j.ker = ∏ k : Fin n, (i k ≫ j).ker := by
    change RootsOfUnityCartier.ideal R n = _
    rw [CyclotomicSchemeOrbit.ideal n φ]
    apply Finset.prod_congr rfl
    intro k _
    rw [← ArithmeticTorusPoints.point_left]
    exact congrArg (fun f ↦ f.left.ker) (generator_orbit n φ k.val).symm
  have hh := congrArg (fun J ↦ J.comap j) h
  rw [ClosedOrbitKernel.ker_comap_self, ClosedOrbitKernel.orbit_comap] at hh
  exact hh.symm

/-- Every monomorphic ambient embedding retains the full scheme-theoretic orbit containment. -/
theorem ambient_orbit_le {X : Scheme} (j : (RootsOfUnityScheme.model R n).left ⟶ X)
    [Mono j] [∀ k : Fin n, IsClosedImmersion ((generator n φ ^ k.val).left ≫ j)] :
    ∏ k : Fin n, ((generator n φ ^ k.val).left ≫ j).ker ≤ j.ker :=
  ClosedOrbitKernel.orbit_le_ker j Finset.univ _ (orbit_product_zero n φ)

end FLT.Mazur.RootsOfUnityIntrinsicOrbit
