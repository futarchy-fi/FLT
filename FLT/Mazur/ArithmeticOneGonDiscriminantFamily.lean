/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ArithmeticOneGonNilpotentDiscriminant
public import FLT.Mazur.ArithmeticOneGonAlgebraicFamily
public import FLT.Mazur.GeneralizedCurveBaseChangeCompEq

/-!
# A natural arithmetic family with prescribed nilpotent discriminant

The finite-iteration solution constructs a full generalized curve from the
original nilpotent discriminant. Uniqueness makes this construction compatible
with arbitrary coefficient maps, including mixed-characteristic reductions.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.ArithmeticOneGonParameter
open OneGonSmoothing
variable {R A : Type} [CommRing R] [CommRing A]

/-- The unique classifying homomorphism with prescribed nilpotent discriminant. -/
def discriminantSpecialize (d : R) (hd : IsNilpotent d) : ParameterRing →+* R :=
  (exists_unique_nilpotent_discriminant_hom d hd).choose

/-- The classifying homomorphism retains an infinitesimal parameter at the boundary. -/
theorem discriminantSpecialize_nilpotent (d : R) (hd : IsNilpotent d) :
    IsNilpotent (discriminantSpecialize d hd parameter) :=
  (exists_unique_nilpotent_discriminant_hom d hd).choose_spec.1.1

/-- The constructed cubic has exactly the original prescribed discriminant. -/
theorem discriminantSpecialize_discriminant (d : R) (hd : IsNilpotent d) :
    discriminantSpecialize d hd (equation parameter).Δ = d :=
  (exists_unique_nilpotent_discriminant_hom d hd).choose_spec.1.2

/-- Original coefficient maps preserve the entire unique classifying homomorphism. -/
theorem discriminantSpecialize_natural (d : R) (hd : IsNilpotent d) (f : R →+* A) :
    f.comp (discriminantSpecialize d hd) = discriminantSpecialize (f d) (hd.map f) := by
  apply (exists_unique_nilpotent_discriminant_hom (f d) (hd.map f)).choose_spec.2
  constructor
  · exact (discriminantSpecialize_nilpotent d hd).map f
  · change f (discriminantSpecialize d hd (equation parameter).Δ) = f d
    rw [discriminantSpecialize_discriminant]

/-- The full generalized curve constructed from the original nilpotent discriminant. -/
def discriminantCurve (d : R) (hd : IsNilpotent d) :
    GeneralizedEllipticCurve (Spec (.of R)) :=
  universalCurve.baseChange (Spec.map (CommRingCat.ofHom (discriminantSpecialize d hd)))

/-- The entire constructed curve, including its action, commutes with coefficient change. -/
def discriminantCurveBaseChangeIso (d : R) (hd : IsNilpotent d) (f : R →+* A) :
    discriminantCurve (f d) (hd.map f) ≅
      (discriminantCurve d hd).baseChange (Spec.map (CommRingCat.ofHom f)) := by
  apply universalCurve.baseChangeCompEqIso
  rw [← Spec.map_comp]
  exact congrArg Spec.map (CommRingCat.hom_ext (discriminantSpecialize_natural d hd f).symm)

end FLT.Mazur.ArithmeticOneGonParameter
