/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudClosureFactorization
public import FLT.GroupScheme.RaynaudModelArithmetic

/-!
# Integral multiplication and flat torsion closures

Multiplication factors integrally through the flat closure of its generic image.
The existing flat torsion closure has the kernel universal property when tested
against finite flat models. No claim is made that the full scheme-theoretic kernel
is flat, or that the map onto the flat image is faithfully flat.
-/

@[expose] public noncomputable section

namespace ThreeAdicPlan

variable {R K : Type} [CommRing R] [Field K] [Algebra R K]
    [PerfectField K] [IsDedekindDomain R] [IsFractionRing R K]

/-- Inclusion of the generic multiplication image into the original point group. -/
def FF.multipleInclusion (X : FF R K) (n : ℕ) :
    GenericGaloisHom (X.multipleModel n) X where
  toFun := Subtype.val
  map_zero' := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The flat closure of the generic multiplication image inside the chosen model. -/
@[implicit_reducible]
def FF.multipleClosure (X : FF R K) (n : ℕ) : FF R K :=
  (X.multipleInclusion n).closure Subtype.val_injective

/-- The integral inclusion of the flat multiplication-image closure. -/
def FF.multipleClosureInclusion (X : FF R K) (n : ℕ) :
    ModelHom (X.multipleClosure n) X :=
  (X.multipleInclusion n).closureInclusion Subtype.val_injective

/-- The flat multiplication-image inclusion is a closed immersion. -/
theorem FF.multipleClosureInclusion_surjective (X : FF R K) (n : ℕ) :
    Function.Surjective (X.multipleClosureInclusion n) := Ideal.Quotient.mk_surjective

/-- The flat multiplication-image inclusion induces inclusion of point groups. -/
@[simp] theorem FF.genericHom_multipleClosureInclusion (X : FF R K) (n : ℕ)
    (x : (X.multipleClosure n).Points) :
    genericHom (X.multipleClosureInclusion n) x = x.val :=
  (X.multipleInclusion n).genericHom_closureInclusion Subtype.val_injective x

/-- Integral multiplication factors through inclusion of its generic image on points. -/
theorem FF.genericHom_multiply_factorization (X : FF R K) (n : ℕ) :
    genericHom (X.multiply n) = (X.multipleInclusion n).comp (X.multiplyGeneric n) := by
  ext x
  exact X.genericHom_multiply n x

/-- Multiplication as an integral morphism to its specified flat image closure. -/
def FF.multiplyToClosure (X : FF R K) (n : ℕ) : ModelHom X (X.multipleClosure n) :=
  (X.multipleInclusion n).closureLift Subtype.val_injective
    (X.multiply n) (X.multiplyGeneric n) (X.genericHom_multiply_factorization n)

/-- Composition with the image inclusion recovers integral multiplication. -/
@[simp] theorem FF.multiplyToClosure_comp_inclusion (X : FF R K) (n : ℕ) :
    (X.multiplyToClosure n).comp (X.multipleClosureInclusion n) = X.multiply n :=
  (X.multipleInclusion n).closureLift_comp_inclusion Subtype.val_injective
    (X.multiply n) (X.multiplyGeneric n) (X.genericHom_multiply_factorization n)

/-- The integral multiplication-image map induces the expected surjection of points. -/
@[simp] theorem FF.genericHom_multiplyToClosure (X : FF R K) (n : ℕ) (x : X.Points) :
    genericHom (X.multiplyToClosure n) x = X.multiplyGeneric n x :=
  (X.multipleInclusion n).genericHom_closureLift Subtype.val_injective
    (X.multiply n) (X.multiplyGeneric n) (X.genericHom_multiply_factorization n) x

/-- The integral multiplication-image map is surjective on generic points. -/
theorem FF.genericHom_multiplyToClosure_surjective (X : FF R K) (n : ℕ) :
    Function.Surjective (genericHom (X.multiplyToClosure n)) := by
  intro y
  obtain ⟨x, hx⟩ := X.multiplyGeneric_surjective n y
  exact ⟨x, (X.genericHom_multiplyToClosure n x).trans hx⟩

/-- The multiplication-image map is injective on integral coordinate rings. -/
theorem FF.multiplyToClosure_injective (X : FF R K) (n : ℕ) :
    Function.Injective (X.multiplyToClosure n) := by
  apply ModelHom.injective_of_baseChange_injective
  rw [← ModelHom.toBialgHom_genericHom]
  exact (genericHom (X.multiplyToClosure n)).toBialgHom_injective
    (X.genericHom_multiplyToClosure_surjective n)

/-- The specified integral multiplication-image closure lowers an annihilating exponent. -/
theorem FF.multipleClosure_killed (X : FF R K) (p n : ℕ)
    (hX : ∀ x : X.Points, p ^ (n + 1) • x = 0)
    (y : (X.multipleClosure p).Points) : p ^ n • y = 0 :=
  X.multipleModel_killed p n hX y

/-- The torsion closure is killed by integral multiplication, not just on generic points. -/
theorem FF.torsionClosureInclusion_comp_multiply (X : FF R K) (n : ℕ) :
    (X.torsionClosureInclusion n).comp (X.multiply n) =
      ModelHom.zero (X.torsionClosure n) X := by
  apply genericHom_injective
  ext x
  rw [genericHom_comp, FF.genericHom_multiply, ModelHom.genericHom_zero,
    FF.genericHom_torsionClosureInclusion]
  exact x.property

/-- A map annihilated by integral multiplication factors uniquely through the flat
 torsion closure. The universal property is tested on finite flat models. -/
theorem FF.torsionClosure_kernel (X Z : FF R K) (n : ℕ) (g : ModelHom Z X)
    (hg : g.comp (X.multiply n) = ModelHom.zero Z X) :
    ∃! l : ModelHom Z (X.torsionClosure n), l.comp (X.torsionClosureInclusion n) = g := by
  have hn (z : Z.Points) : n • genericHom g z = 0 := by
    have he := congrArg (fun k : ModelHom Z X ↦ genericHom k z) hg
    simpa only [genericHom_comp, FF.genericHom_multiply, ModelHom.genericHom_zero] using he
  let h : GenericGaloisHom Z (X.torsionAuxModel n) :=
    { toFun := fun z ↦ ⟨genericHom g z, hn z⟩
      map_zero' := Subtype.ext (map_zero (genericHom g))
      map_add' := fun a b ↦ Subtype.ext (map_add (genericHom g) a b)
      map_smul' := fun σ z ↦ Subtype.ext (map_smul (genericHom g) σ z) }
  let i : GenericGaloisHom (X.torsionAuxModel n) X := X.torsionInclusion n
  have he : genericHom g = i.comp h := by ext z; rfl
  exact ⟨i.closureLift Subtype.val_injective g h he,
    i.closureLift_comp_inclusion Subtype.val_injective g h he,
    fun l hl ↦ i.closureLift_unique Subtype.val_injective g h he l hl⟩

/-- The generic kernel of the integral multiplication-image map is exactly the flat
 torsion closure's point group. -/
theorem FF.multiplyToClosure_eq_zero_iff (X : FF R K) (n : ℕ) (x : X.Points) :
    genericHom (X.multiplyToClosure n) x = 0 ↔
      ∃ t : (X.torsionClosure n).Points, genericHom (X.torsionClosureInclusion n) t = x := by
  rw [FF.genericHom_multiplyToClosure]
  exact X.multiplyGeneric_eq_zero_iff n x

/-- The flat torsion closure is the kernel of the integral map onto the flat image
when tested on finite flat models. This does not assert faithful flatness. -/
theorem FF.multiplyToClosure_kernel (X Z : FF R K) (n : ℕ) (g : ModelHom Z X)
    (hg : g.comp (X.multiplyToClosure n) = ModelHom.zero Z (X.multipleClosure n)) :
    ∃! l : ModelHom Z (X.torsionClosure n), l.comp (X.torsionClosureInclusion n) = g := by
  apply X.torsionClosure_kernel Z n g
  apply genericHom_injective
  ext z
  have he := congrArg (fun k : ModelHom Z (X.multipleClosure n) ↦ genericHom k z) hg
  rw [genericHom_comp, FF.genericHom_multiplyToClosure, ModelHom.genericHom_zero] at he
  rw [genericHom_comp, FF.genericHom_multiply, ModelHom.genericHom_zero]
  exact congrArg Subtype.val he

end ThreeAdicPlan
