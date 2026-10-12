/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GrassmannianPrincipalOverlap
public import FLT.Mazur.GrassmannianSplitChartScheme
public import Mathlib.AlgebraicGeometry.OpenImmersion

/-!
# Scheme structure on the determinant overlaps

The localized polynomial spectrum is an actual principal affine open of the
split chart. Base-preserving affine-test maps represent precisely the quotient
points whose second selected summand is a basis.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.GrassmannianChart
universe u
variable {R : Type u} [CommRing R] {ι : Type u} [Fintype ι] {d : ℕ}
  (P : Matrix (Fin d) (Fin d) R) (Q : Matrix ι (Fin d) R)

/-- The principal affine overlap scheme. -/
def principalOverlapScheme : Scheme.{u} := Spec (.of (principalOverlapRing P Q))

/-- Its inclusion into the original split chart. -/
def principalOverlapInclusion : principalOverlapScheme P Q ⟶ splitChartScheme R ι d :=
  Spec.algebraMap (MvPolynomial (Fin d × ι) R) (principalOverlapRing P Q)

instance : IsAffine (principalOverlapScheme P Q) := inferInstanceAs (IsAffine (Spec _))

instance : IsOpenImmersion (principalOverlapInclusion P Q) :=
  inferInstanceAs (IsOpenImmersion (Spec.map (CommRingCat.ofHom
    (algebraMap (MvPolynomial (Fin d × ι) R) (principalOverlapRing P Q)))))

/-- Its open image is exactly the basic open of the second-basis determinant. -/
theorem principalOverlapInclusion_range :
    (principalOverlapInclusion P Q).opensRange = PrimeSpectrum.basicOpen (overlapPolynomial P Q) :=
  Scheme.Hom.opensRange_localizationAway
    (R := CommRingCat.of (MvPolynomial (Fin d × ι) R)) (overlapPolynomial P Q)

/-- The original coefficient-base morphism of the overlap. -/
def principalOverlapStructure : principalOverlapScheme P Q ⟶ Spec (.of R) :=
  Spec.algebraMap R (principalOverlapRing P Q)

/-- The inclusion respects the original coefficient base. -/
theorem principalOverlapInclusion_over :
    principalOverlapInclusion P Q ≫ splitChartStructure R ι d =
      principalOverlapStructure P Q := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1

variable (S : Type u) [CommRing S] [Algebra R S]

/-- Affine-test scheme maps classify the actual double-chart quotient points. -/
def principalOverlapSchemePointEquiv :
    {f : Spec (.of S) ⟶ principalOverlapScheme P Q //
      f ≫ principalOverlapStructure P Q = Spec.algebraMap R S} ≃
        PrincipalOverlapPoints (S := S) P Q :=
  Spec.homEquivAlgHom.trans (principalOverlapPointEquiv P Q)

/-- Every overlap quotient point has a unique base-preserving classifying scheme map. -/
theorem principalOverlapSchemePoint_unique (N : PrincipalOverlapPoints (S := S) P Q) :
    ∃! f : {f : Spec (.of S) ⟶ principalOverlapScheme P Q //
        f ≫ principalOverlapStructure P Q = Spec.algebraMap R S},
      principalOverlapSchemePointEquiv P Q S f = N :=
  (principalOverlapSchemePointEquiv P Q S).bijective.existsUnique N

end FLT.Mazur.GrassmannianChart
