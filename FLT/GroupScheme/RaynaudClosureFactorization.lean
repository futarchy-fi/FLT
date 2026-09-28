/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudTorsionFiltration

/-!
# Integral factorization through flat subgroup closures

An integral morphism whose generic fibre lands in a subgroup factors uniquely
through that subgroup's flat closure. This is a universal property among the
finite flat models `FF`; it does not assert flatness of a scheme-theoretic kernel.
-/

@[expose] public noncomputable section

open scoped TensorProduct

universe u

namespace Bialgebra.Quotient

variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Bialgebra R A] [Bialgebra R B]

/-- Descend a bialgebra morphism that kills a biideal to the quotient. -/
def liftBialgHom (I : Ideal A) [(I.restrictScalars R).IsCoideal]
    (f : A →ₐc[R] B) (hf : ∀ a ∈ I, f a = 0) : (A ⧸ I) →ₐc[R] B := by
  let e := Ideal.Quotient.liftₐ I f.toAlgHom hf
  let π := mkBialgHom (R := R) I
  have he (a : A) : e (π a) = f a := rfl
  apply BialgHom.ofAlgHom e
  · ext x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    change Coalgebra.counit (e (π a)) = Coalgebra.counit (π a)
    rw [he, CoalgHomClass.counit_comp_apply, CoalgHomClass.counit_comp_apply]
  · ext x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    change _root_.TensorProduct.map e.toLinearMap e.toLinearMap (Coalgebra.comul (π a)) =
      Coalgebra.comul (e (π a))
    rw [← CoalgHomClass.map_comp_comul_apply π, _root_.TensorProduct.map_map]
    have hel : e.toLinearMap.comp (π : A →ₗ[R] A ⧸ I) = (f : A →ₗ[R] B) := rfl
    rw [hel, he]
    exact CoalgHomClass.map_comp_comul_apply f a

/-- The descended morphism agrees with the original one on quotient representatives. -/
@[simp] theorem liftBialgHom_mk (I : Ideal A) [(I.restrictScalars R).IsCoideal]
    (f : A →ₐc[R] B) (hf : ∀ a ∈ I, f a = 0) (a : A) :
    liftBialgHom I f hf (Ideal.Quotient.mk I a) = f a := rfl

end Bialgebra.Quotient

namespace ThreeAdicPlan

variable {R K : Type u} [CommRing R] [Field K] [Algebra R K] [PerfectField K]

/-- Generic coordinate maps reverse composition of maps of points. -/
theorem GenericGaloisHom.toBialgHom_comp {X Y Z : FF R K}
    (f : GenericGaloisHom X Y) (g : GenericGaloisHom Y Z) :
    (show GenericGaloisHom X Z from g.comp f).toBialgHom = f.toBialgHom.comp g.toBialgHom := by
  ext a
  apply (GaloisModule.GenericFiber.genericEvalAlgEquiv K (AlgebraicClosure K)
    (K ⊗[R] X.CoordinateRing)).injective
  ext p
  have h₁ := (show GenericGaloisHom X Z from g.comp f).toBialgHom_points (Additive.ofMul p)
  have h₂ := g.toBialgHom_points
    (BialgHom.precompPoints f.toBialgHom (Additive.ofMul p))
  rw [f.toBialgHom_points] at h₂
  exact AlgHom.congr_fun (congrArg Additive.toMul
    (Z.points_bijective.1 (h₁.trans h₂.symm))) a

variable [IsDedekindDomain R] [IsFractionRing R K]

omit [IsDedekindDomain R] in
/-- An integral map kills the equations of a subgroup closure whenever its generic
map factors through the subgroup. -/
theorem GenericGaloisHom.closureIdeal_le_ker {X Y Z : FF R K}
    (f : GenericGaloisHom X Y) (g : ModelHom Z Y) (h : GenericGaloisHom Z X)
    (hg : genericHom g = f.comp h) : f.closureIdeal ≤ RingHom.ker g.toAlgHom.toRingHom := by
  intro a ha
  change g a = 0
  apply Algebra.TensorProduct.includeRight_injective (A := K)
    (IsFractionRing.injective R K)
  have he : g.baseChange = h.toBialgHom.comp f.toBialgHom := by
    rw [← g.toBialgHom_genericHom, hg, GenericGaloisHom.toBialgHom_comp]
  change f.toBialgHom (1 ⊗ₜ[R] a) = 0 at ha
  change g.baseChange (1 ⊗ₜ[R] a) = 1 ⊗ₜ[R] (0 : Z.CoordinateRing)
  rw [he, BialgHom.comp_apply, ha, map_zero, TensorProduct.tmul_zero]

/-- Factor an integral morphism through a flat subgroup closure using its generic
factorization. -/
def GenericGaloisHom.closureLift {X Y Z : FF R K}
    (f : GenericGaloisHom X Y) (hf : Function.Injective f)
    (g : ModelHom Z Y) (h : GenericGaloisHom Z X)
    (hg : genericHom g = f.comp h) : ModelHom Z (f.closure hf) :=
  Bialgebra.Quotient.liftBialgHom f.closureIdeal g (f.closureIdeal_le_ker g h hg)

/-- The factorization through closure recovers the original integral map. -/
@[simp] theorem GenericGaloisHom.closureLift_comp_inclusion {X Y Z : FF R K}
    (f : GenericGaloisHom X Y) (hf : Function.Injective f)
    (g : ModelHom Z Y) (h : GenericGaloisHom Z X)
    (hg : genericHom g = f.comp h) :
    (f.closureLift hf g h hg).comp (f.closureInclusion hf) = g := by
  ext a
  rfl

/-- The integral factorization induces the prescribed generic factorization. -/
@[simp] theorem GenericGaloisHom.genericHom_closureLift {X Y Z : FF R K}
    (f : GenericGaloisHom X Y) (hf : Function.Injective f)
    (g : ModelHom Z Y) (h : GenericGaloisHom Z X)
    (hg : genericHom g = f.comp h) (z : Z.Points) :
    genericHom (f.closureLift hf g h hg) z = h z := by
  apply hf
  have he := congrArg (fun k : ModelHom Z Y ↦ genericHom k z)
    (f.closureLift_comp_inclusion hf g h hg)
  rw [genericHom_comp, f.genericHom_closureInclusion, hg] at he
  exact he

/-- Factorization through a flat subgroup closure is unique as an integral map. -/
theorem GenericGaloisHom.closureLift_unique {X Y Z : FF R K}
    (f : GenericGaloisHom X Y) (hf : Function.Injective f)
    (g : ModelHom Z Y) (h : GenericGaloisHom Z X)
    (hg : genericHom g = f.comp h) (l : ModelHom Z (f.closure hf))
    (hl : l.comp (f.closureInclusion hf) = g) : l = f.closureLift hf g h hg := by
  ext a
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  exact congrArg (fun k : ModelHom Z Y ↦ k a)
    (hl.trans (f.closureLift_comp_inclusion hf g h hg).symm)

end ThreeAdicPlan
