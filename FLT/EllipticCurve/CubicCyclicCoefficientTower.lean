/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CubicCoefficientTower
public import FLT.EllipticCurve.CubicLegendreCyclicAutomorphisms
/-! # Composition of cyclic coefficient extension

The scalar-tower identity for curve maps restricts to torsion and nonzero
torsion, then descends to cyclic parameters. Equality of equations transports
the intermediate models and commutes with their inclusions and quotient maps.
Identity extension is proved to induce identity on all three models.

This is composition for actual coefficient morphisms. Naturality of the
descended coordinate maps under parameter changes is still needed to deduce
the involution and braid relations for the Legendre cyclic automorphisms.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace WeierstrassCurve.CubicCharts
universe u
variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
variable [IsNoetherianRing R] [IsDomain R]
variable (W V : WeierstrassCurve R) [W.IsElliptic] [V.IsElliptic]

/-- Identify torsion models of equal Weierstrass equations. -/
def torsionModelCongr (n : ℕ) (h : W = V) : torsionModel W n ≅ torsionModel V n := by
  subst V
  exact Iso.refl _

theorem torsionModelCongr_inclusion (n : ℕ) (h : W = V) :
    (torsionModelCongr W V n h).hom.left ≫ (torsionInclusion V n).left =
      (torsionInclusion W n).left ≫ eqToHom (congrArg scheme h) := by
  subst V
  simp [torsionModelCongr]

variable [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
variable [IsNoetherianRing S] [IsDomain S] [IsNoetherianRing T] [IsDomain T]
theorem coefficientTorsionMorphism_tower (n : ℕ) :
    coefficientTorsionMorphism (W.map (algebraMap R S)) T n ≫
      coefficientTorsionMorphism W S n =
    (torsionModelCongr _ _ n (coefficientTower_curve (S := S) (T := T) W)).hom.left ≫
      coefficientTorsionMorphism W T n := by
  apply (cancel_mono (torsionInclusion W n).left).mp
  rw [Category.assoc, coefficientTorsionMorphism_inclusion,
    ← Category.assoc, coefficientTorsionMorphism_inclusion, Category.assoc,
    coefficientMorphism_tower, Category.assoc, coefficientTorsionMorphism_inclusion]
  simp only [← Category.assoc]
  rw [torsionModelCongr_inclusion]


/-- Identify nonzero torsion models of equal Weierstrass equations. -/
def nonzeroModelCongr (n : ℕ) [NeZero n] (h : W = V) :
    nonzeroTorsionModel W n ≅ nonzeroTorsionModel V n := by
  subst V
  exact Iso.refl _

theorem nonzeroModelCongr_inclusion (n : ℕ) [NeZero n] (h : W = V) :
    (nonzeroModelCongr W V n h).hom.left ≫ (nonzeroTorsionInclusion V n).left =
      (nonzeroTorsionInclusion W n).left ≫ (torsionModelCongr W V n h).hom.left := by
  subst V
  simp [nonzeroModelCongr, torsionModelCongr]

theorem coefficientNonzeroTorsionMorphism_tower (n : ℕ) [NeZero n] :
    coefficientNonzeroTorsionMorphism (W.map (algebraMap R S)) T n ≫
      coefficientNonzeroTorsionMorphism W S n =
    (nonzeroModelCongr _ _ n (coefficientTower_curve (S := S) (T := T) W)).hom.left ≫
      coefficientNonzeroTorsionMorphism W T n := by
  apply (cancel_mono (nonzeroTorsionInclusion W n).left).mp
  rw [Category.assoc, coefficientNonzeroTorsionMorphism_inclusion,
    ← Category.assoc, coefficientNonzeroTorsionMorphism_inclusion, Category.assoc,
    coefficientTorsionMorphism_tower, Category.assoc,
    coefficientNonzeroTorsionMorphism_inclusion]
  simp only [← Category.assoc]
  rw [nonzeroModelCongr_inclusion]

variable (p : ℕ) [Fact p.Prime] [Fact (IsUnit (p : R))]
variable [Fact (IsUnit (p : S))] [Fact (IsUnit (p : T))]

theorem cyclicModelCongr_quotient (h : W = V) :
    (nonzeroModelCongr W V p h).hom.left ≫ (scalarQuotientMap V p).left =
      (scalarQuotientMap W p).left ≫ (cyclicModelCongr W p V h).hom.left := by
  subst V
  simp [nonzeroModelCongr, cyclicModelCongr]

theorem coefficientScalarQuotientMorphism_tower :
    coefficientScalarQuotientMorphism (W.map (algebraMap R S)) T p ≫
      coefficientScalarQuotientMorphism W S p =
    (cyclicModelCongr _ p _ (coefficientTower_curve (S := S) (T := T) W)).hom.left ≫
      coefficientScalarQuotientMorphism W T p := by
  apply (cancel_epi
    (scalarQuotientMap ((W.map (algebraMap R S)).map (algebraMap S T)) p).left).mp
  rw [← Category.assoc, coefficientScalarQuotientMorphism_generators,
    Category.assoc, coefficientScalarQuotientMorphism_generators,
    ← Category.assoc, coefficientNonzeroTorsionMorphism_tower]
  simp only [← Category.assoc]
  rw [← cyclicModelCongr_quotient]
  simp only [Category.assoc, coefficientScalarQuotientMorphism_generators]

theorem coefficientTorsionMorphism_self (n : ℕ) :
    coefficientTorsionMorphism W R n = 𝟙 _ := by
  apply (cancel_mono (torsionInclusion W n).left).mp
  rw [coefficientTorsionMorphism_inclusion, coefficientMorphism_self]
  simp

theorem coefficientNonzeroTorsionMorphism_self (n : ℕ) [NeZero n] :
    coefficientNonzeroTorsionMorphism W R n = 𝟙 _ := by
  apply (cancel_mono (nonzeroTorsionInclusion W n).left).mp
  rw [coefficientNonzeroTorsionMorphism_inclusion, coefficientTorsionMorphism_self]
  simp

theorem coefficientScalarQuotientMorphism_self (p : ℕ) [Fact p.Prime]
    [Fact (IsUnit (p : R))] :
    coefficientScalarQuotientMorphism W R p = 𝟙 _ := by
  apply (cancel_epi (scalarQuotientMap (W.map (algebraMap R R)) p).left).mp
  rw [coefficientScalarQuotientMorphism_generators, coefficientNonzeroTorsionMorphism_self]
  simp
end WeierstrassCurve.CubicCharts
