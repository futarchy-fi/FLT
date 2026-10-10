/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolynomialRelativeAmbient

/-!
# Actual polynomial spectrum charts of relative polynomial spaces

An affine test of the base lifts to its original polynomial spectrum in the
relative ambient space. The square is cartesian and respects maps of bases.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace FLT.Mazur.HilbertChart

set_option backward.isDefEq.respectTransparency false

variable (R I : Type u) [CommRing R]
variable {X Y : Scheme.{u}} (s : X ⟶ Spec (.of R))
variable (S : Type u) [CommRing S] [Algebra R S]
variable (a : Spec (.of S) ⟶ X)
variable (ha : a ≫ s = Spec.map (CommRingCat.ofHom (algebraMap R S)))

/-- The original polynomial spectrum of an affine base test maps to the relative ambient space. -/
def polynomialRelativeAffineChart : Spec (.of (MvPolynomial I S)) ⟶
    polynomialRelativeAmbient R I s :=
  pullback.lift (Spec.map (CommRingCat.ofHom (MvPolynomial.C (R := S) (σ := I))) ≫ a)
    (Spec.map (CommRingCat.ofHom (MvPolynomial.map (algebraMap R S)))) (by
      rw [Category.assoc, ha, ← Spec.map_comp, ← Spec.map_comp]
      congr 1
      apply CommRingCat.hom_ext
      apply RingHom.ext
      intro r
      exact (MvPolynomial.map_C (algebraMap R S) r).symm)

/-- The affine ambient chart lies over its original base test. -/
@[reassoc]
theorem polynomialRelativeAffineChart_fst :
    polynomialRelativeAffineChart R I s S a ha ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (MvPolynomial.C (R := S) (σ := I))) ≫ a :=
  pullback.lift_fst _ _ _

/-- The affine ambient chart preserves the original polynomial-space map. -/
@[reassoc]
theorem polynomialRelativeAffineChart_snd :
    polynomialRelativeAffineChart R I s S a ha ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (MvPolynomial.map (algebraMap R S))) :=
  pullback.lift_snd _ _ _

/-- The original polynomial spectrum is the actual base change along the affine test. -/
theorem polynomialRelativeAffineChart_isPullback :
    IsPullback (polynomialRelativeAffineChart R I s S a ha)
      (Spec.map (CommRingCat.ofHom (MvPolynomial.C (R := S) (σ := I))))
      (pullback.fst _ _) a := by
  have h : IsPullback (Spec.map (CommRingCat.ofHom (MvPolynomial.C (R := S) (σ := I))))
      (polynomialRelativeAffineChart R I s S a ha ≫ pullback.snd _ _) (a ≫ s)
      (Spec.map (CommRingCat.ofHom (MvPolynomial.C (R := R) (σ := I)))) := by
    rw [polynomialRelativeAffineChart_snd, ha]
    exact polynomialSpectrum_isPullback R I S
  exact (h.of_bot (polynomialRelativeAffineChart_fst R I s S a ha).symm
    (IsPullback.of_hasPullback _ _)).flip

/-- Affine polynomial charts commute with maps of the original scheme base. -/
theorem polynomialRelativeAffineChart_comp
    (t : Y ⟶ Spec (.of R)) (g : X ⟶ Y) (hg : g ≫ t = s) :
    polynomialRelativeAffineChart R I s S a ha ≫ polynomialRelativeAmbientMap R I t s g hg =
      polynomialRelativeAffineChart R I t S (a ≫ g) (by rw [Category.assoc, hg, ha]) := by
  apply pullback.hom_ext
  · rw [Category.assoc, polynomialRelativeAmbientMap_fst, ← Category.assoc,
      polynomialRelativeAffineChart_fst, polynomialRelativeAffineChart_fst, Category.assoc]
  · rw [Category.assoc, polynomialRelativeAmbientMap_snd,
      polynomialRelativeAffineChart_snd, polynomialRelativeAffineChart_snd]

end FLT.Mazur.HilbertChart
