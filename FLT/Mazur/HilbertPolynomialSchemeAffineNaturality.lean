/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineMorphismAlgebraMap
public import FLT.Mazur.HilbertPolynomialSchemeAffineParameter
public import FLT.Mazur.PolynomialRelativeAffineNaturality

/-!
# Naturality of local parameters from scheme ideal families

The local classifying morphisms agree after every affine test map. The proof
uses equality of the full coordinate ideals and injectivity of the actual
affine representing equivalence, rather than choosing compatible bases.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open FLT.Mazur.FCurve

universe u

namespace FLT.Mazur.HilbertChart

set_option backward.isDefEq.respectTransparency false

variable (R I : Type u) [CommRing R] (d : ℕ)
variable {X : Scheme.{u}} (s : X ⟶ Spec (.of R))
variable (J : (polynomialRelativeAmbient R I s).IdealSheafData)
variable (hJ : FiniteLocallyFreeDegree (J.subschemeι ≫ pullback.fst _ _) d)
variable (S T : Type u) [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
variable (a : Spec (.of S) ⟶ X)
variable (ha : a ≫ s = Spec.map (CommRingCat.ofHom (algebraMap R S)))
variable (b : Spec (.of T) ⟶ X)
variable (hb : b ≫ s = Spec.map (CommRingCat.ofHom (algebraMap R T)))

/-- Local family parameters commute with every coefficient algebra map of affine tests. -/
theorem polynomialSchemeAffineParameter_natural (f : S →ₐ[R] T)
    (hf : Spec.map (CommRingCat.ofHom f.toRingHom) ≫ a = b) :
    Spec.map (CommRingCat.ofHom f.toRingHom) ≫
        (polynomialSchemeAffineParameter R I d s J hJ S a ha).val =
      (polynomialSchemeAffineParameter R I d s J hJ T b hb).val := by
  let F := polynomialSchemeAffineParameter R I d s J hJ S a ha
  let G := polynomialSchemeAffineParameter R I d s J hJ T b hb
  have hF : (Spec.map (CommRingCat.ofHom f.toRingHom) ≫ F.val) ≫
      polynomialHilbertStructure R I d = Spec.map (CommRingCat.ofHom (algebraMap R T)) := by
    rw [Category.assoc, F.property, ← Spec.map_comp]
    congr 1
    exact CommRingCat.hom_ext f.comp_algebraMap
  apply polynomialParameterIdeal_injective R I d T _ hF G.val G.property
  rw [polynomialParameterIdeal_baseChange R I d S F.val F.property T f _ hF rfl]
  rw [polynomialSchemeAffineParameter_ideal, polynomialSchemeAffineParameter_ideal]
  exact (polynomialRelativeCoordinateIdeal_natural R I s S T a ha b hb f hf J).symm

/-- Arbitrary affine scheme test maps preserve the local classifying morphism. -/
theorem polynomialSchemeAffineParameter_test
    (q : Spec (.of T) ⟶ Spec (.of S)) (hq : q ≫ a = b) :
    q ≫ (polynomialSchemeAffineParameter R I d s J hJ S a ha).val =
      (polynomialSchemeAffineParameter R I d s J hJ T b hb).val := by
  have hqs : q ≫ Spec.map (CommRingCat.ofHom (algebraMap R S)) =
      Spec.map (CommRingCat.ofHom (algebraMap R T)) := by
    rw [← ha, ← Category.assoc, hq, hb]
  let f := affineOverAlgHom R S T q hqs
  have hf : Spec.map (CommRingCat.ofHom f.toRingHom) = q :=
    affineOverAlgHom_spec R S T q hqs
  rw [← hf]
  exact polynomialSchemeAffineParameter_natural R I d s J hJ S T a ha b hb f
    (by rw [hf, hq])

end FLT.Mazur.HilbertChart
