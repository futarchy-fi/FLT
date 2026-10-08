/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.MultiplicativeGroupScheme
public import FLT.Mazur.LaurentUnitPoints
public import FLT.Mazur.WeierstrassSpecSectionMorphism

/-!
# Unit evaluation is categorical torus multiplication

The tensor pairing of two Laurent evaluations composed with comultiplication
is evaluation at their product. The Gamma-Spec adjunction upgrades this to
the actual group-scheme multiplication on every source scheme.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonObj
open scoped LaurentPolynomial TensorProduct

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R A B S : Type u} [CommRing R] [CommRing A] [CommRing B] [CommRing S]
  [Algebra R A] [Algebra R B] [Algebra R S]

/-- Laurent comultiplication followed by the tensor pairing evaluates at the product unit. -/
theorem laurentUnit_product_comul (p q : Sˣ) :
    (Algebra.TensorProduct.productMap (LaurentUnitPoints.evalUnit (R := R) p)
        (LaurentUnitPoints.evalUnit q)).comp (Bialgebra.comulAlgHom R R[T;T⁻¹]) =
      LaurentUnitPoints.evalUnit (p * q) := by
  apply LaurentUnitPoints.hom_ext <;>
    simp [AlgHom.comp_apply, Bialgebra.comulAlgHom_apply, LaurentPolynomial.comul_T,
      mul_comm]

variable {X : Scheme.{u}} [Algebra R Γ(X, ⊤)]

/-- A tensor pairing on global sections represents the categorical pairing of morphisms. -/
theorem specSectionMorphism_product
    (f : A →ₐ[R] Γ(X, ⊤)) (g : B →ₐ[R] Γ(X, ⊤))
    (h : specSectionMorphism f.toRingHom ≫
        Spec.map (CommRingCat.ofHom (algebraMap R A)) =
      specSectionMorphism g.toRingHom ≫ Spec.map (CommRingCat.ofHom (algebraMap R B))) :
    pullback.lift (specSectionMorphism f.toRingHom) (specSectionMorphism g.toRingHom) h ≫
        (pullbackSpecIso R A B).hom =
      specSectionMorphism (Algebra.TensorProduct.productMap f g).toRingHom := by
  apply (cancel_mono (pullbackSpecIso R A B).inv).mp
  rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  apply pullback.hom_ext
  · rw [pullback.lift_fst, Category.assoc, pullbackSpecIso_inv_fst,
      ← specSectionMorphism_comp]
    congr 1
    exact (congrArg AlgHom.toRingHom (Algebra.TensorProduct.productMap_left f g)).symm
  · rw [pullback.lift_snd, Category.assoc, pullbackSpecIso_inv_snd,
      ← specSectionMorphism_comp]
    congr 1
    exact (congrArg AlgHom.toRingHom (Algebra.TensorProduct.productMap_right f g)).symm

/-- The actual torus multiplication evaluates at the product on arbitrary source schemes. -/
theorem laurentUnit_scheme_multiplication (p q : Γ(X, ⊤)ˣ)
    (h : specSectionMorphism (LaurentUnitPoints.evalUnit (R := R) p).toRingHom ≫
        (MultiplicativeGroupScheme.gm R).hom =
      specSectionMorphism (LaurentUnitPoints.evalUnit (R := R) q).toRingHom ≫
        (MultiplicativeGroupScheme.gm R).hom) :
    pullback.lift
        (specSectionMorphism (LaurentUnitPoints.evalUnit (R := R) p).toRingHom)
        (specSectionMorphism (LaurentUnitPoints.evalUnit (R := R) q).toRingHom) h ≫
      μ[MultiplicativeGroupScheme.gm R].left =
        specSectionMorphism (LaurentUnitPoints.evalUnit (R := R) (p * q)).toRingHom := by
  rw [MultiplicativeGroupScheme.multiplication_left, ← Category.assoc,
    specSectionMorphism_product, ← specSectionMorphism_comp]
  congr 1
  exact congrArg AlgHom.toRingHom (laurentUnit_product_comul (R := R) p q)

end FLT.Mazur.WeierstrassIntegralChart
