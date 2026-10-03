/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DisjointClosedCoproduct
public import FLT.Mazur.PolygonBoundaryDivisor
public import FLT.Mazur.ScalarCohomology
public import Mathlib.LinearAlgebra.Dimension.Constructions
/-!
# A finite free presentation of the polygon boundary divisor

The actual divisor subscheme is the disjoint union of its marked sections.
The comparison with `Spec (Fin n → K)` respects the structure morphism.
Its global sections, with scalars from that morphism, have an explicit basis
indexed by `Fin n`. This works even when the characteristic divides n.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.PolygonDivisorCoproduct
open PolygonPinching PolygonMarkedSections PolygonBoundaryDivisor
variable (K : Type) [Field K] (n : ℕ) [NeZero n]
  {C : Over (Spec (.of K))} (p : components K n ⟶ C)
  (hn : 0 < n) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)
  (a : Fin n → Kˣ)

/-- The divisor is the disjoint union of the actual marked sections. -/
def coproductIso : (∐ fun _ : Fin n ↦ Spec (.of K)) ≅ (ideal K n p a).subscheme := by
  let := PolygonSeparated.cocone K n hn p q h
  let s := fun i ↦ sectionMap K n p (a i) i
  have (i : Fin n) : IsClosedImmersion (s i) :=
    FCurve.isClosedImmersion_section C.hom _ (section_base K n p (a i) i)
  exact DisjointClosedCoproduct.iso s fun _ _ hij ↦ section_disjoint K n p hn q h _ _ hij

/-- The coproduct comparison preserves the closed immersion. -/
@[reassoc (attr := simp)]
theorem coproductIso_hom_ι :
    (coproductIso K n p hn q h a).hom ≫ (ideal K n p a).subschemeι =
      Sigma.desc (fun i ↦ sectionMap K n p (a i) i) :=
  by
  let := PolygonSeparated.cocone K n hn p q h
  have (i : Fin n) : IsClosedImmersion (sectionMap K n p (a i) i) :=
    FCurve.isClosedImmersion_section C.hom _ (section_base K n p (a i) i)
  exact DisjointClosedCoproduct.iso_hom_ι _
    (fun _ _ hij ↦ section_disjoint K n p hn q h _ _ hij)

/-- Each coproduct component maps identically to the base field. -/
@[reassoc]
theorem component_base (i : Fin n) :
    Sigma.ι _ i ≫ (coproductIso K n p hn q h a).hom ≫
      (ideal K n p a).subschemeι ≫ C.hom = 𝟙 _ := by
  rw [coproductIso_hom_ι_assoc, Sigma.ι_comp_desc_assoc, section_base]

/-- A global affine presentation of the divisor by the product algebra. -/
def coordinateIso : (ideal K n p a).subscheme ≅ Spec (.of (Fin n → K)) :=
  (coproductIso K n p hn q h a).symm ≪≫ asIso (sigmaSpec (fun _ : Fin n ↦ .of K))

/-- The presentation is over the specified base field. -/
@[reassoc (attr := simp)]
theorem coordinateIso_base :
    (coordinateIso K n p hn q h a).hom ≫
        Spec.map (CommRingCat.ofHom (algebraMap K (Fin n → K))) =
      (ideal K n p a).subschemeι ≫ C.hom := by
  apply (cancel_epi (coproductIso K n p hn q h a).hom).mp
  apply Sigma.hom_ext
  intro i
  simp only [coordinateIso, Iso.trans_hom, Iso.symm_hom, asIso_hom,
    Category.assoc, Iso.hom_inv_id_assoc, ι_sigmaSpec_assoc, component_base]
  rw [← Spec.map_comp, ← Spec.map_id]
  congr 1

/-- The finite free presentation as an isomorphism over the field. -/
def coordinateOverIso : Over.mk ((ideal K n p a).subschemeι ≫ C.hom) ≅
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K (Fin n → K)))) :=
  Over.isoMk (coordinateIso K n p hn q h a) (coordinateIso_base K n p hn q h a)

/-- Global functions on the divisor are coordinate functions on the components. -/
def sectionsIso : Γ((ideal K n p a).subscheme, ⊤) ≅ CommRingCat.of (Fin n → K) :=
  Scheme.Γ.mapIso (coordinateIso K n p hn q h a).symm.op ≪≫ Scheme.ΓSpecIso _

/-- The coordinate comparison respects scalars from the actual structure map. -/
theorem sectionsIso_scalar (r : K) :
    (sectionsIso K n p hn q h a).hom
      (FCurve.structureScalarMap ((ideal K n p a).subschemeι ≫ C.hom) r) =
        algebraMap K (Fin n → K) r := by
  have he : (coordinateIso K n p hn q h a).inv ≫
      (ideal K n p a).subschemeι ≫ C.hom =
      Spec.map (CommRingCat.ofHom (algebraMap K (Fin n → K))) := by
    rw [← coordinateIso_base K n p hn q h a, Iso.inv_hom_id_assoc]
  have he' := congrArg (fun f ↦ FCurve.structureScalarMap f r) he
  change (Scheme.ΓSpecIso _).hom
    ((coordinateIso K n p hn q h a).inv.appTop
      (FCurve.structureScalarMap ((ideal K n p a).subschemeι ≫ C.hom) r)) = _
  rw [show (coordinateIso K n p hn q h a).inv.appTop
      (FCurve.structureScalarMap ((ideal K n p a).subschemeι ≫ C.hom) r) =
      FCurve.structureScalarMap (Spec.map
        (CommRingCat.ofHom (algebraMap K (Fin n → K)))) r from he']
  change ((Scheme.ΓSpecIso (.of K)).inv ≫
    (Spec.map (CommRingCat.ofHom (algebraMap K (Fin n → K)))).appTop ≫
      (Scheme.ΓSpecIso (.of (Fin n → K))).hom).hom r = _
  rw [Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
  rfl

/-- The coordinate comparison is linear for the actual base-field action. -/
def sectionsLinearEquiv :
    letI := Module.compHom Γ((ideal K n p a).subscheme, ⊤)
      (FCurve.structureScalarMap ((ideal K n p a).subschemeι ≫ C.hom))
    Γ((ideal K n p a).subscheme, ⊤) ≃ₗ[K] (Fin n → K) := by
  letI := Module.compHom Γ((ideal K n p a).subscheme, ⊤)
    (FCurve.structureScalarMap ((ideal K n p a).subschemeι ≫ C.hom))
  refine
    { toAddEquiv := ((sectionsIso K n p hn q h a).commRingCatIsoToRingEquiv).toAddEquiv
      map_smul' := ?_ }
  intro r x
  change (sectionsIso K n p hn q h a).hom
    (FCurve.structureScalarMap ((ideal K n p a).subschemeι ≫ C.hom) r * x) = _
  rw [map_mul, sectionsIso_scalar]
  rfl

/-- An explicit rank-n basis of global functions on the divisor. -/
def sectionsBasis :
    letI := Module.compHom Γ((ideal K n p a).subscheme, ⊤)
      (FCurve.structureScalarMap ((ideal K n p a).subschemeι ≫ C.hom))
    Module.Basis (Fin n) K Γ((ideal K n p a).subscheme, ⊤) := by
  letI := Module.compHom Γ((ideal K n p a).subscheme, ⊤)
    (FCurve.structureScalarMap ((ideal K n p a).subschemeι ≫ C.hom))
  exact (Pi.basisFun K (Fin n)).map (sectionsLinearEquiv K n p hn q h a).symm

include h in
/-- The rank of the actual divisor algebra is n. -/
theorem sections_rank :
    letI := Module.compHom Γ((ideal K n p a).subscheme, ⊤)
      (FCurve.structureScalarMap ((ideal K n p a).subschemeι ≫ C.hom))
    Module.finrank K Γ((ideal K n p a).subscheme, ⊤) = n := by
  let := Module.compHom Γ((ideal K n p a).subscheme, ⊤)
    (FCurve.structureScalarMap ((ideal K n p a).subschemeι ≫ C.hom))
  simpa using Module.finrank_eq_card_basis (sectionsBasis K n p hn q h a)

include h in
/-- The actual divisor subscheme is affine. -/
theorem affine : IsAffine (ideal K n p a).subscheme :=
  .of_isIso (coordinateIso K n p hn q h a).hom

end FLT.Mazur.PolygonDivisorCoproduct
