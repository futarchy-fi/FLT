/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineMorphismAlgebraMap
public import FLT.Mazur.HilbertAmbientRelationImage
public import FLT.Mazur.HilbertPolynomialParameterChart

/-!
# Full ambient relation ideals on polynomial Hilbert overlaps

Every common scheme test pulls back the same relation ideal sheaf from either
prescribed-basis chart. Affine tests compare actual polynomial ideals and full
equation ideals, so the assertion includes nonreduced overlap structure.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open FLT.Mazur.BaseAdicThickening

universe u

namespace FLT.Mazur.HilbertChart

set_option backward.isDefEq.respectTransparency false

variable (R I : Type u) [CommRing R] (d : ℕ)
variable (K : Ideal (MvPolynomial I R))

/-- Cache the coefficient ring for scheme overlap equations. -/
local instance relationOverlapCoefficientsRing : CommRing (Coefficients R I d) := inferInstance
/-- Cache each chart ring for scheme overlap equations. -/
local instance relationOverlapChartRing (w : Fin d → MvPolynomial I R) :
    CommRing (ChartRing R I d w) := inferInstance

/-- The full closed ambient equation ideal sheaf on a prescribed-basis chart. -/
def ambientRelationsSheaf (w : Fin d → MvPolynomial I R) :
    (Spec (.of (ChartRing R I d w))).IdealSheafData :=
  baseIdeal (.of (ChartRing R I d w)) (ambientRelationsIdeal R I d w K)

variable (w v : Fin d → MvPolynomial I R)

attribute [local irreducible] pointIdeal polynomialParameterIdeal

/-- Equal affine parameters recover identical full point ideals in either basis. -/
theorem pointIdeal_commonParameter (S : Type u) [CommRing S] [Algebra R S]
    (f : ChartRing R I d w →ₐ[R] S) (g : ChartRing R I d v →ₐ[R] S)
    (h : Spec.map (CommRingCat.ofHom f.toRingHom) ≫ polynomialHilbertChartι R I d w =
      Spec.map (CommRingCat.ofHom g.toRingHom) ≫ polynomialHilbertChartι R I d v) :
    pointIdeal R I d w f = pointIdeal R I d v g := by
  have hf : (Spec.map (CommRingCat.ofHom f.toRingHom) ≫ polynomialHilbertChartι R I d w) ≫
      polynomialHilbertStructure R I d = Spec.map (CommRingCat.ofHom (algebraMap R S)) := by
    rw [Category.assoc, polynomialHilbertChartι_over, ← Spec.map_comp]
    exact congrArg Spec.map (CommRingCat.hom_ext f.comp_algebraMap)
  have hg : (Spec.map (CommRingCat.ofHom g.toRingHom) ≫ polynomialHilbertChartι R I d v) ≫
      polynomialHilbertStructure R I d = Spec.map (CommRingCat.ofHom (algebraMap R S)) := by
    rw [← h]
    exact hf
  rw [← polynomialParameterIdeal_chart R I d S w f hf,
    ← polynomialParameterIdeal_chart R I d S v g hg]
  exact congrArg (fun p : { a : Spec (.of S) ⟶ polynomialHilbertScheme R I d //
      a ≫ polynomialHilbertStructure R I d =
        Spec.map (CommRingCat.ofHom (algebraMap R S)) } ↦
      polynomialParameterIdeal R I d S p.val p.property)
    (show (⟨_, hf⟩ : { a // a ≫ polynomialHilbertStructure R I d =
      Spec.map (CommRingCat.ofHom (algebraMap R S)) }) = ⟨_, hg⟩ from Subtype.ext h)

/-- Common affine chart tests have equal full equation ideals. -/
theorem ambientRelationsSheaf_affineTest (S : Type u) [CommRing S] [Algebra R S]
    (f : ChartRing R I d w →ₐ[R] S) (g : ChartRing R I d v →ₐ[R] S)
    (h : Spec.map (CommRingCat.ofHom f.toRingHom) ≫ polynomialHilbertChartι R I d w =
      Spec.map (CommRingCat.ofHom g.toRingHom) ≫ polynomialHilbertChartι R I d v) :
    (ambientRelationsSheaf R I d K w).comap (Spec.map (CommRingCat.ofHom f.toRingHom)) =
      (ambientRelationsSheaf R I d K v).comap (Spec.map (CommRingCat.ofHom g.toRingHom)) := by
  unfold ambientRelationsSheaf
  rw [baseIdeal_comap_specMap, baseIdeal_comap_specMap]
  exact congrArg (baseIdeal (.of S)) (ambientRelationsIdeal_map_eq R I d w v K f g
    (pointIdeal_commonParameter R I d w v S f g h))

/-- Arbitrary common scheme tests pull back the same full ambient equation sheaf. -/
theorem ambientRelationsSheaf_commonTest {X : Scheme.{u}}
    (f : X ⟶ Spec (.of (ChartRing R I d w)))
    (g : X ⟶ Spec (.of (ChartRing R I d v)))
    (h : f ≫ polynomialHilbertChartι R I d w = g ≫ polynomialHilbertChartι R I d v) :
    (ambientRelationsSheaf R I d K w).comap f =
      (ambientRelationsSheaf R I d K v).comap g := by
  apply idealSheaf_ext_of_affineTests
  intro S a
  let s := a ≫ f ≫ Spec.map (CommRingCat.ofHom (algebraMap R (ChartRing R I d w)))
  let _ : Algebra R S := (Spec.preimage s).hom.toAlgebra
  have hs : Spec.map (CommRingCat.ofHom (algebraMap R S)) = s := Spec.map_preimage _
  have hf : (a ≫ f) ≫ Spec.map (CommRingCat.ofHom (algebraMap R (ChartRing R I d w))) =
      Spec.map (CommRingCat.ofHom (algebraMap R S)) := by
    rw [hs]
    exact Category.assoc _ _ _
  have hg : (a ≫ g) ≫ Spec.map (CommRingCat.ofHom (algebraMap R (ChartRing R I d v))) =
      Spec.map (CommRingCat.ofHom (algebraMap R S)) := by
    calc
      _ = a ≫ (g ≫ polynomialHilbertChartι R I d v) ≫
          polynomialHilbertStructure R I d := by
        rw [Category.assoc, Category.assoc, polynomialHilbertChartι_over]
      _ = a ≫ (f ≫ polynomialHilbertChartι R I d w) ≫
          polynomialHilbertStructure R I d := by rw [h]
      _ = _ := by
        rw [Category.assoc, polynomialHilbertChartι_over, ← Category.assoc]
        exact hf
  let F := affineOverAlgHom R (ChartRing R I d w) S (a ≫ f) hf
  let G := affineOverAlgHom R (ChartRing R I d v) S (a ≫ g) hg
  have hF : Spec.map (CommRingCat.ofHom F.toRingHom) = a ≫ f :=
    affineOverAlgHom_spec R _ _ _ hf
  have hG : Spec.map (CommRingCat.ofHom G.toRingHom) = a ≫ g :=
    affineOverAlgHom_spec R _ _ _ hg
  rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp, ← hF, ← hG]
  apply ambientRelationsSheaf_affineTest R I d K w v S F G
  rw [hF, hG, Category.assoc, Category.assoc, h]

/-- The closed equation sheaves agree on the actual categorical chart intersection. -/
theorem ambientRelationsSheaf_pullbackOverlap :
    (ambientRelationsSheaf R I d K w).comap
        (pullback.fst (polynomialHilbertChartι R I d w) (polynomialHilbertChartι R I d v)) =
      (ambientRelationsSheaf R I d K v).comap
        (pullback.snd (polynomialHilbertChartι R I d w) (polynomialHilbertChartι R I d v)) :=
  ambientRelationsSheaf_commonTest R I d K w v _ _ pullback.condition

end FLT.Mazur.HilbertChart
