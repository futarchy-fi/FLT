/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction

/-!
# Algebra specializations from arbitrary schemes into affine charts

Global sections turn compatible affine chart morphisms into algebra maps.
The Gamma-Spec adjunction detects equality, with no affineness or reducedness
assumption on the common source scheme.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {X : Scheme.{u}} {A B R : Type u} [CommRing A] [CommRing B] [CommRing R]

/-- The ring specialization induced by a morphism into an affine chart. -/
def specSectionHom (f : X ⟶ Spec (.of A)) : A →+* Γ(X, ⊤) :=
  ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom

/-- Chart composition is ring-map composition on global sections. -/
theorem specSectionHom_comp (f : X ⟶ Spec (.of A)) (g : B →+* A) :
    specSectionHom (f ≫ Spec.map (CommRingCat.ofHom g)) = (specSectionHom f).comp g := by
  unfold specSectionHom
  rw [Scheme.Hom.comp_appTop, ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality,
    Category.assoc]
  rfl

/-- Ring specializations detect equality of arbitrary morphisms into the same spectrum. -/
theorem specSectionHom_injective :
    Function.Injective (specSectionHom (X := X) (A := A)) := by
  intro f g h
  apply ext_to_Spec
  exact CommRingCat.hom_ext h

variable [Algebra R A] [Algebra R B]

/-- A scheme over the coefficient spectrum gives an algebra structure on global sections. -/
@[instance_reducible] def specSectionAlgebra (s : X ⟶ Spec (.of R)) : Algebra R Γ(X, ⊤) :=
  (specSectionHom s).toAlgebra

/-- A chart morphism over the base yields an actual coefficient-preserving algebra map. -/
def specSectionAlgHom (s : X ⟶ Spec (.of R)) (f : X ⟶ Spec (.of A))
    (hf : f ≫ Spec.map (CommRingCat.ofHom (algebraMap R A)) = s) :
    let _ := specSectionAlgebra s
    A →ₐ[R] Γ(X, ⊤) := by
  let _ := specSectionAlgebra s
  refine { specSectionHom f with commutes' := ?_ }
  intro r
  exact DFunLike.congr_fun ((specSectionHom_comp f (algebraMap R A)).symm.trans
    (congrArg specSectionHom hf)) r

/-- Compatible chart morphisms give compatible algebra specializations. -/
theorem specSectionAlgHom_comp (s : X ⟶ Spec (.of R))
    (f : X ⟶ Spec (.of A)) (g : X ⟶ Spec (.of B))
    (hf : f ≫ Spec.map (CommRingCat.ofHom (algebraMap R A)) = s)
    (hg : g ≫ Spec.map (CommRingCat.ofHom (algebraMap R B)) = s)
    (a : B →ₐ[R] A) (h : f ≫ Spec.map (CommRingCat.ofHom a.toRingHom) = g) :
    let _ := specSectionAlgebra s
    (specSectionAlgHom s f hf).comp a = specSectionAlgHom s g hg := by
  let _ := specSectionAlgebra s
  apply AlgHom.coe_ringHom_injective
  exact (specSectionHom_comp f a.toRingHom).symm.trans (congrArg specSectionHom h)

/-- Equality of two input morphisms gives equality of their algebra specializations. -/
theorem specSectionAlgHom_comp_eq (s : X ⟶ Spec (.of R))
    (f : X ⟶ Spec (.of A)) (g : X ⟶ Spec (.of B))
    (hf : f ≫ Spec.map (CommRingCat.ofHom (algebraMap R A)) = s)
    (hg : g ≫ Spec.map (CommRingCat.ofHom (algebraMap R B)) = s)
    {C : Type u} [CommRing C] [Algebra R C] (a : C →ₐ[R] A) (b : C →ₐ[R] B)
    (h : f ≫ Spec.map (CommRingCat.ofHom a.toRingHom) =
      g ≫ Spec.map (CommRingCat.ofHom b.toRingHom)) :
    let _ := specSectionAlgebra s
    (specSectionAlgHom s f hf).comp a = (specSectionAlgHom s g hg).comp b := by
  let _ := specSectionAlgebra s
  apply AlgHom.coe_ringHom_injective
  exact (specSectionHom_comp f a.toRingHom).symm.trans
    ((congrArg specSectionHom h).trans (specSectionHom_comp g b.toRingHom))

/-- An algebra comparison of outputs descends back to morphisms of schemes. -/
theorem specSectionAlgHom_compare (s : X ⟶ Spec (.of R))
    (f : X ⟶ Spec (.of A)) (g : X ⟶ Spec (.of B))
    (hf : f ≫ Spec.map (CommRingCat.ofHom (algebraMap R A)) = s)
    (hg : g ≫ Spec.map (CommRingCat.ofHom (algebraMap R B)) = s)
    {C : Type u} [CommRing C] [Algebra R C] (a : C →ₐ[R] A) (b : C →ₐ[R] B)
    (h : let _ := specSectionAlgebra s
      (specSectionAlgHom s f hf).comp a = (specSectionAlgHom s g hg).comp b) :
    f ≫ Spec.map (CommRingCat.ofHom a.toRingHom) =
      g ≫ Spec.map (CommRingCat.ofHom b.toRingHom) := by
  let _ := specSectionAlgebra s
  apply specSectionHom_injective
  rw [specSectionHom_comp, specSectionHom_comp]
  exact congrArg AlgHom.toRingHom h

end FLT.Mazur.WeierstrassIntegralChart
