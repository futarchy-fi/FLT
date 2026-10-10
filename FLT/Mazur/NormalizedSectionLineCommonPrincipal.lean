/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.NormalizedSectionLinePrincipalRechart

/-!
# Common principal refinements for different line coordinates

Localizing at the product of two generator coordinates is their actual
principal-open intersection. Both coordinates become units there, giving
two constructed normalizations of the same line and a comparison preserving
its principal restriction in the ambient coordinate sheaf.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.NormalizedSectionLine
variable {R : Type u} [CommRing R] {ι : Type u}

/-- The product localization is exactly the intersection of the two coordinate principal opens. -/
lemma coordinatePrincipal_inter (i j k : ι) (L : Chart R ι i) :
    PrimeSpectrum.basicOpen (generator R ι i L j * generator R ι i L k) =
      PrimeSpectrum.basicOpen (generator R ι i L j) ⊓
        PrimeSpectrum.basicOpen (generator R ι i L k) :=
  PrimeSpectrum.basicOpen_mul _ _

/-- Either selected coordinate is a unit in the common principal localization. -/
lemma commonCoordinate_isUnit (i j k : ι) (L : Chart R ι i)
    (q : ι) (hq : q = j ∨ q = k) :
    IsUnit (algebraMap R (Localization.Away
      (generator R ι i L j * generator R ι i L k)) (generator R ι i L q)) := by
  have h := IsLocalization.Away.algebraMap_isUnit
    (S := Localization.Away (generator R ι i L j * generator R ι i L k))
    (generator R ι i L j * generator R ι i L k)
  rw [map_mul, IsUnit.mul_iff] at h
  rcases hq with rfl | rfl
  · exact h.1
  · exact h.2

/-- A selected coordinate normalization on the genuine common principal refinement. -/
def commonPrincipalChart (i j k : ι) (L : Chart R ι i) (q : ι) (hq : q = j ∨ q = k) :
    Chart (Localization.Away (generator R ι i L j * generator R ι i L k)) ι q :=
  rechart i q (baseChange (algebraMap R (Localization.Away
    (generator R ι i L j * generator R ι i L k))) i L)
      (commonCoordinate_isUnit i j k L q hq).unit (by
        rw [generator_baseChange]
        exact (commonCoordinate_isUnit i j k L q hq).unit_spec.symm)

/-- Both chosen normalizations use the same actual localized submodule. -/
lemma commonPrincipalChart_val (i j k : ι) (L : Chart R ι i) :
    (commonPrincipalChart i j k L j (Or.inl rfl)).val =
      (commonPrincipalChart i j k L k (Or.inr rfl)).val := rfl

/-- The actual principal restriction is isomorphic to either constructed coordinate chart. -/
def sheafCommonPrincipal (i j k : ι) (L : Chart R ι i) (q : ι) (hq : q = j ∨ q = k) :
    (principalRestriction (generator R ι i L j * generator R ι i L k)).obj (sheaf i L) ≅
      sheaf q (commonPrincipalChart i j k L q hq) :=
  sheafPrincipalRestriction _ i L ≪≫ sheafChartChange i q _ _ rfl

attribute [local irreducible] sheafPrincipalRestriction sheafChartChange
attribute [local irreducible] principalRestriction vectorPrincipalRestriction

/-- Each normalization preserves the actual inclusion of the restricted line. -/
lemma sheafCommonPrincipal_inclusion [Finite ι] (i j k : ι) (L : Chart R ι i)
    (q : ι) (hq : q = j ∨ q = k) :
    (sheafCommonPrincipal i j k L q hq).hom ≫
        sheafInclusion q (commonPrincipalChart i j k L q hq) =
      (principalRestriction (generator R ι i L j * generator R ι i L k)).map
        (sheafInclusion i L) ≫
          (vectorPrincipalRestriction (ι := ι)
            (generator R ι i L j * generator R ι i L k)).hom := by
  simp only [sheafCommonPrincipal, Iso.trans_hom, Category.assoc,
    sheafChartChange_inclusion, sheafPrincipalRestriction_inclusion]

/-- Changing the selected coordinate on the intersection commutes with principal recovery. -/
lemma sheafCommonPrincipal_change [Finite ι] (i j k : ι) (L : Chart R ι i) :
    (sheafCommonPrincipal i j k L j (Or.inl rfl)).hom ≫
        (sheafChartChange j k (commonPrincipalChart i j k L j (Or.inl rfl))
          (commonPrincipalChart i j k L k (Or.inr rfl)) rfl).hom =
      (sheafCommonPrincipal i j k L k (Or.inr rfl)).hom := by
  apply (cancel_mono (sheafInclusion k (commonPrincipalChart i j k L k (Or.inr rfl)))).mp
  simp only [Category.assoc, sheafChartChange_inclusion, sheafCommonPrincipal_inclusion]

end FLT.Mazur.NormalizedSectionLine
