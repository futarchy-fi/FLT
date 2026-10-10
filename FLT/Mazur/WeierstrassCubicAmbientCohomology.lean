/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.ProjectiveTwistCohomology

/-!
# Ambient cohomology for the plane cubic exact sequence

The only all-negative exponent of total degree -3 on the projective plane is
(-1,-1,-1). The existing base-linear Cech comparison therefore computes actual
H2(O(-3)) as the coefficient ring. The neighboring H1 groups and positive
cohomology of O vanish. These are inputs to the cubic's genus computation;
the exact sequence identifying the cubic's H1 is a separate construction.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open FLT.Mazur.FCurve FLT.Mazur.ProjectiveSpace
open FLT.Mazur.ProjectiveSpace.TwistCechCohomology
open FLT.Mazur.ProjectiveSpace.TwistGradedCech
open FLT.Mazur.ProjectiveSpace.LocalizationDegree
open scoped DirectSum

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace FLT.Mazur.WeierstrassCubicAmbientCohomology

/-- The unique top-cohomology monomial for a plane cubic has exponent (-1,-1,-1). -/
def cubicNegativeExponent : NegativeExponent (Fin 3) (-3) :=
  ⟨⟨Finsupp.equivFunOnFinite.symm (fun _ => -1), by
    simp [Finsupp.degree_eq_sum]⟩, by simp⟩

/-- The total degree and strict negativity force each of the three exponents to be -1. -/
theorem cubicNegativeExponent_coordinate (e : NegativeExponent (Fin 3) (-3)) (i : Fin 3) :
    e.val.val i = -1 := by
  have hd := e.val.property
  rw [Finsupp.degree_eq_sum, Fin.sum_univ_succ, Fin.sum_univ_succ,
    Fin.sum_univ_succ] at hd
  simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero] at hd
  have h0 := e.property 0
  have h1 := e.property 1
  have h2 := e.property 2
  fin_cases i <;> dsimp at * <;> omega

/-- There is one coefficient summand in the ambient top cohomology. -/
instance cubicNegativeExponentUnique : Unique (NegativeExponent (Fin 3) (-3)) where
  default := cubicNegativeExponent
  uniq e := by
    apply Subtype.ext
    apply Subtype.ext
    ext i
    exact cubicNegativeExponent_coordinate e i

variable (R : Type) [CommRing R]

/-- The standard-cover calculation of H2(O(-3)) on the projective plane. -/
def cubicNegativeTwistCechIso :
    (sheafComplex R (Fin 3) (-3)).homology 2 ≅ ModuleCat.of R R :=
  sheafPositiveHomologyIso R (Fin 3) (-3) 1 ≪≫
    (DFinsupp.mapRange.linearEquiv (fun e : NegativeExponent (Fin 3) (-3) =>
      (negativeExponentHomologyIso R (Fin 3) (-3) e.val.val
        e.val.property e.property).toLinearEquiv)).toModuleIso ≪≫
    (DirectSum.lid R R (NegativeExponent (Fin 3) (-3))).toModuleIso

/-- Actual Ext cohomology H2(O(-3)) is the base ring, with its canonical scalar action. -/
def cubicNegativeTwistH2Equiv :
    let _ := Module.compHom (ModuleH (twistingSheaf R (Fin 3) (-3)) 2)
      (constantSection R (Fin 3) ⊤)
    ModuleH (twistingSheaf R (Fin 3) (-3)) 2 ≃ₗ[R] R :=
  (twistModuleHEquiv R (Fin 3) (-3) 2).symm.trans
    (cubicNegativeTwistCechIso R).toLinearEquiv

/-- Every twist on the projective plane has vanishing H1. -/
theorem planeTwistH1_zero (d : ℤ) :
    Subsingleton (ModuleH (twistingSheaf R (Fin 3) d) 1) := by
  let _ := ModuleCat.isZero_iff_subsingleton.mp
    (sheaf_isZero_homology_off_top R (Fin 3) d 0 (by decide))
  exact (twistModuleHEquiv R (Fin 3) d 1).surjective.subsingleton

/-- The untwisted projective plane has no positive structure cohomology. -/
theorem planeUntwisted_positive_zero (q : ℕ) :
    Subsingleton (ModuleH (twistingSheaf R (Fin 3) 0) (q + 1)) := by
  let _ := ModuleCat.isZero_iff_subsingleton.mp
    (sheaf_isZero_homology_large R (Fin 3) 0 (by decide) q)
  exact (twistModuleHEquiv R (Fin 3) 0 (q + 1)).surjective.subsingleton

/-- The negative cubic twist has no global sections. -/
theorem cubicNegativeTwistH0_zero :
    Subsingleton (ModuleH (twistingSheaf R (Fin 3) (-3)) 0) := by
  let _ := ModuleCat.isZero_iff_subsingleton.mp
    (sheaf_isZero_homology_zero_negative R (Fin 3) (-3) (by decide) (by decide))
  exact (twistModuleHEquiv R (Fin 3) (-3) 0).surjective.subsingleton

/-- Over a field the ambient top cohomology has dimension exactly one. -/
theorem cubicNegativeTwistH2_finrank (K : Type) [Field K] :
    let _ := Module.compHom (ModuleH (twistingSheaf K (Fin 3) (-3)) 2)
      (constantSection K (Fin 3) ⊤)
    Module.finrank K (ModuleH (twistingSheaf K (Fin 3) (-3)) 2) = 1 := by
  let _ := Module.compHom (ModuleH (twistingSheaf K (Fin 3) (-3)) 2)
    (constantSection K (Fin 3) ⊤)
  exact (cubicNegativeTwistH2Equiv K).finrank_eq.trans (Module.finrank_self K)

end FLT.Mazur.WeierstrassCubicAmbientCohomology
