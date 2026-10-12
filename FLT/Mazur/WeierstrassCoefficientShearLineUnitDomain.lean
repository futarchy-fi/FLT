/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearRetainedFiber
public import FLT.Mazur.LaurentUnitPointNaturality
import all FLT.Mazur.WeierstrassCoefficientShearRetainedFiber

/-!
# Unrestricted unit inputs on every actual retained line

Every pair of units defines a point of the complete action domain. No affine
smooth-chart denominator is imposed, and the coefficient algebra may be nonreduced.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart WeierstrassSuccessiveX WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (S : Type u) [CommRing S] [Algebra R S] (r : S)
  (t : ℕ) (ht : t ≤ n) (i : Fin t)
  (hs : algebraMap R S (π ^ (start + i.val)) = 0) (hp : algebraMap R S π = 0)
  (h3 : algebraMap R S (Data.b3 (data ⟨i.val + 1, by omega⟩)) = 0)
  (h4 : algebraMap R S (Data.b4 (data ⟨i.val + 1, by omega⟩)) = 0)
  (hr : r ^ 2 + algebraMap R S W.a₁ * r - algebraMap R S W.a₂ = 0)
  (v : S) (hv : v * (v + (rootShearCurve (W.map (algebraMap R S)) r).a₁) = 0)
local notation "L" => coefficientShearRetainedLine hπ data S r t ht i hs hp h3 h4 hr v hv
local notation "g" => coefficientShearGluedStructure hπ data S r t ht
local notation "p" => Spec.map (CommRingCat.ofHom
  (Polynomial.toLaurent : Polynomial S →+* S[T;T⁻¹]))
local notation "pt" => fun q => (laurentUnitOverPoint (R := S) q).left
variable {B : Type u} [CommRing B] [Algebra S B] (q z : Bˣ)

/-- The whole punctured line retains the original coefficient map. -/
theorem coefficientShearLineUnit_structure :
    (pt z ≫ p ≫ L) ≫ g = Spec.map (CommRingCat.ofHom (algebraMap S B)) := by
  simp only [Category.assoc, coefficientShearRetainedLine_structure]
  erw [terminalComponent_algebra_structure (Polynomial.toLaurentAlg (R := S))]
  exact (laurentUnitOverPoint (R := S) z).w

/-- Arbitrary torus and line units form an actual pair over the coefficient scheme. -/
theorem coefficientShearLineUnit_condition :
    pt q ≫ (MultiplicativeGroupScheme.gm S).hom = (pt z ≫ p ≫ L) ≫ g := by
  rw [coefficientShearLineUnit_structure]
  exact (laurentUnitOverPoint (R := S) q).w

end FLT.Mazur.WeierstrassDividedDepth
