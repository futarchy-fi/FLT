/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineOverlapMapSections
public import FLT.Mazur.AffineReverseGeometricOverlap

/-!
# Geometric overlap compatibility on coefficient maps

A commutative square between the actual projection pullbacks gives precisely
the tensor-overlap compatibility needed for descent of morphisms.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct
open Scheme.Modules
universe u
namespace FLT.Mazur.AffineGeometricMapComparison
open AffineOverlapTensor AffineOverlapPullback AffineGeometricOverlap
open AffineOverlapMapSections
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

private theorem square_apply {A : CommRingCat.{u}} {P Q U V : (Spec A).Modules}
    (a : P ⟶ Q) (b : Q ⟶ V) (c : P ⟶ U) (d : U ⟶ V)
    (h : a ≫ b = c ≫ d) (x : moduleSpecΓFunctor.obj P) :
    moduleSpecΓFunctor.map b (moduleSpecΓFunctor.map a x) =
      moduleSpecΓFunctor.map d (moduleSpecΓFunctor.map c x) := by
  rw [← ModuleCat.comp_apply, ← Functor.map_comp, h, Functor.map_comp, ModuleCat.comp_apply]

private theorem square_of_sections {A : CommRingCat.{u}}
    {P Q U V : (Spec A).Modules} [P.IsQuasicoherent]
    (a : P ⟶ Q) (b : Q ⟶ V) (c : P ⟶ U) (d : U ⟶ V)
    (h : ∀ x : moduleSpecΓFunctor.obj P,
      moduleSpecΓFunctor.map b (moduleSpecΓFunctor.map a x) =
        moduleSpecΓFunctor.map d (moduleSpecΓFunctor.map c x)) : a ≫ b = c ≫ d := by
  apply AffineSectionsReconstruction.map_injective
  apply ModuleCat.hom_ext
  exact LinearMap.ext h

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
variable (M N : (Spec (.of S)).Modules) [M.IsQuasicoherent] [N.IsQuasicoherent]
attribute [local instance] AffineOverlapPullback.instModuleCarrierCarrierOfCoefficients
local instance (P : (Spec (.of S)).Modules) : IsScalarTower R S (coefficients S P) :=
  IsScalarTower.of_algebraMap_smul (fun _ _ ↦ rfl)
variable (e : Overlap R S M) (e' : Overlap R S N) (f : M ⟶ N)

/-- Compatibility is the square of the actual two projection pullbacks. -/
def Compatible : Prop :=
  e.hom ≫ (pullback (Spec.map (CommRingCat.ofHom (right R S)))).map f =
    (pullback (Spec.map (CommRingCat.ofHom (left R S)))).map f ≫ e'.hom

set_option maxRecDepth 2048 in
/-- A geometric compatible map intertwines both tensor overlap maps. -/
theorem tensor_compatible (h : Compatible R S M N e e' f)
    (x : coefficients S M ⊗[R] S) :
    ((moduleSpecΓFunctor.map f).hom.restrictScalars R).lTensor S (tensorEquiv R S M e x) =
      tensorEquiv R S N e'
        (((moduleSpecΓFunctor.map f).hom.restrictScalars R).rTensor S x) := by
  apply (secondSections R S N).injective
  have ha := (secondSections_map R S M N f (tensorEquiv R S M e x)).symm
  have hb := congrArg
    (moduleSpecΓFunctor.map ((pullback (Spec.map (CommRingCat.ofHom (right R S)))).map f))
    (tensorEquiv_sections R S M e x)
  have hc := square_apply e.hom
    ((pullback (Spec.map (CommRingCat.ofHom (right R S)))).map f)
    ((pullback (Spec.map (CommRingCat.ofHom (left R S)))).map f) e'.hom h
    (firstSections R S M x)
  have hd := congrArg (moduleSpecΓFunctor.map e'.hom) (firstSections_map R S M N f x)
  exact ha.trans (hb.trans (hc.trans (hd.trans (tensorEquiv_sections R S N e' _).symm)))

set_option maxRecDepth 2048 in
/-- In particular the geometric square gives the pure-tensor compatibility law. -/
theorem tensor_compatible_tmul (h : Compatible R S M N e e' f)
    (n : coefficients S M) (s : S) :
    ((moduleSpecΓFunctor.map f).hom.restrictScalars R).lTensor S
        (tensorEquiv R S M e (n ⊗ₜ[R] s : coefficients S M ⊗[R] S)) =
      tensorEquiv R S N e' (moduleSpecΓFunctor.map f n ⊗ₜ[R] s : coefficients S N ⊗[R] S) :=
  tensor_compatible R S M N e e' f h (n ⊗ₜ[R] s)

set_option maxRecDepth 2048 in
/-- Tensor compatibility detects the actual geometric square. -/
theorem compatible_of_tensor
    (h : ∀ x : coefficients S M ⊗[R] S,
      ((moduleSpecΓFunctor.map f).hom.restrictScalars R).lTensor S (tensorEquiv R S M e x) =
        tensorEquiv R S N e'
          (((moduleSpecΓFunctor.map f).hom.restrictScalars R).rTensor S x)) :
    Compatible R S M N e e' f := by
  have : ((pullback (Spec.map (CommRingCat.ofHom (left R S)))).obj M).IsQuasicoherent :=
    AffineModulePullbackSections.isQuasicoherent_pullback (CommRingCat.ofHom (left R S)) M
  apply square_of_sections
  intro y
  obtain ⟨x, rfl⟩ := (firstSections R S M).surjective y
  have ha := congrArg
    (moduleSpecΓFunctor.map ((pullback (Spec.map (CommRingCat.ofHom (right R S)))).map f))
    (tensorEquiv_sections R S M e x).symm
  have hb := secondSections_map R S M N f (tensorEquiv R S M e x)
  have hc := congrArg (secondSections R S N) (h x)
  have hd := tensorEquiv_sections R S N e'
    (((moduleSpecΓFunctor.map f).hom.restrictScalars R).rTensor S x)
  have he := congrArg (moduleSpecΓFunctor.map e'.hom) (firstSections_map R S M N f x).symm
  exact ha.trans (hb.trans (hc.trans (hd.trans he)))

/-- Geometric and coefficient compatibility describe exactly the same maps. -/
theorem compatible_iff_tensor : Compatible R S M N e e' f ↔
    ∀ x : coefficients S M ⊗[R] S,
      ((moduleSpecΓFunctor.map f).hom.restrictScalars R).lTensor S (tensorEquiv R S M e x) =
        tensorEquiv R S N e'
          (((moduleSpecΓFunctor.map f).hom.restrictScalars R).rTensor S x) :=
  ⟨tensor_compatible R S M N e e' f, compatible_of_tensor R S M N e e' f⟩

end FLT.Mazur.AffineGeometricMapComparison
