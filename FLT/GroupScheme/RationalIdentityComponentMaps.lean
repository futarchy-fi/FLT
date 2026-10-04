/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RationalIdentityComponentModel
public import FLT.GroupScheme.BialgebraSurjectiveFactor

/-! # Original integral morphisms restrict functorially to the identity components -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance 2000] IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
  IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion
namespace ThreeAdicPlan.ModelHom
attribute [local instance] rationalFiniteFlat_henselian rationalSpecialFiber_artinian
variable {p : ℕ} [Fact p.Prime]
local notation "O" =>
  IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ (LocalCyclotomic.rationalPlace p)
local notation "K" =>
  IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ (LocalCyclotomic.rationalPlace p)

/-- An integral group morphism takes the identity component into the identity component. -/
theorem rationalIdentity_idempotent {X Y : FF ((LocalCyclotomic.rationalPlace
  p).adicCompletionIntegers ℚ)
      ((LocalCyclotomic.rationalPlace p).adicCompletion ℚ)} (f : ModelHom X Y) :
    (FF.rationalIdentityComponentProjection (p := p) X)
      (f ((FF.rationalComponentIdempotent (p := p) Y) (FF.rationalIdentityComponentIndex (p := p)
        Y))) = 1 := by
  apply (FF.rationalIdentityComponent_idempotent_eq_one (p := p) X)
  · exact ((componentIdempotent_isIdempotent _ _).map f.toAlgHom.toRingHom).map
      (FF.rationalIdentityComponentProjection (p := p) X).toRingHom
  · rw [(FF.rationalIdentityComponentCounit_projection (p := p) X), CoalgHomClass.counit_comp_apply,
      (FF.counit_rationalIdentityComponentIdempotent (p := p) Y)]

/-- The original coordinate map descends to the actual component quotients. -/
def rationalIdentityAlgHom {X Y : FF ((LocalCyclotomic.rationalPlace p).adicCompletionIntegers ℚ)
      ((LocalCyclotomic.rationalPlace p).adicCompletion ℚ)} (f : ModelHom X Y) :
    (FF.rationalIdentityComponent (p := p) Y).CoordinateRing →ₐ[O] (FF.rationalIdentityComponent
      (p := p) X).CoordinateRing :=
  Ideal.Quotient.liftₐ (FF.rationalIdentityComponentIdeal (p := p) Y)
    ((FF.rationalIdentityComponentProjection (p := p) X).comp f.toAlgHom) (by
      change Y.rationalIdentityComponentIdeal ≤ RingHom.ker
        ((X.rationalIdentityComponentProjection).comp f.toAlgHom).toRingHom
      apply Ideal.span_le.mpr
      rintro a (rfl : a = _)
      change (FF.rationalIdentityComponentProjection (p := p) X)
        (f (1 - (FF.rationalComponentIdempotent (p := p) Y) (FF.rationalIdentityComponentIndex (p
          := p) Y))) = 0
      rw [map_sub, map_one, map_sub, map_one, (rationalIdentity_idempotent (p := p) (X := X) (Y
        := Y) f), sub_self])

/-- The restriction is a genuine integral group morphism. -/
def rationalIdentityMap {X Y : FF ((LocalCyclotomic.rationalPlace p).adicCompletionIntegers ℚ)
      ((LocalCyclotomic.rationalPlace p).adicCompletion ℚ)} (f : ModelHom X Y) : ModelHom
  (FF.rationalIdentityComponent (p := p) X) (FF.rationalIdentityComponent (p := p) Y) :=
  BialgHom.descendAlongSurjective (FF.rationalIdentityComponentInclusion (p := p) Y)
    (FF.rationalIdentityComponentInclusion_surjective (p := p) Y)
    ((FF.rationalIdentityComponentInclusion (p := p) X).comp f) (rationalIdentityAlgHom (p := p)
      (X := X) (Y := Y) f) (by ext; rfl)

/-- The identity-component inclusion commutes with the original integral map. -/
theorem rationalIdentityMap_naturality {X Y : FF ((LocalCyclotomic.rationalPlace
  p).adicCompletionIntegers ℚ)
      ((LocalCyclotomic.rationalPlace p).adicCompletion ℚ)} (f : ModelHom X Y) :
    (rationalIdentityMap (p := p) (X := X) (Y := Y) f).comp
      (FF.rationalIdentityComponentInclusion (p := p) Y) =
      (FF.rationalIdentityComponentInclusion (p := p) X).comp f := by
  ext a
  rfl

/-- The actual restriction is uniquely determined by its inclusion square. -/
theorem rationalIdentityMap_unique {X Y : FF ((LocalCyclotomic.rationalPlace
  p).adicCompletionIntegers ℚ)
      ((LocalCyclotomic.rationalPlace p).adicCompletion ℚ)} (f : ModelHom X Y)
    (g : ModelHom (FF.rationalIdentityComponent (p := p) X) (FF.rationalIdentityComponent (p :=
      p) Y))
    (hg : g.comp (FF.rationalIdentityComponentInclusion (p := p) Y) =
      (FF.rationalIdentityComponentInclusion (p := p) X).comp f) : g = (rationalIdentityMap (p :=
        p) (X := X) (Y := Y) f) := by
  ext a
  obtain ⟨a, rfl⟩ := (FF.rationalIdentityComponentInclusion_surjective (p := p) Y) a
  exact DFunLike.congr_fun hg a

/-- Restriction preserves identities. -/
theorem rationalIdentityMap_id {X : FF ((LocalCyclotomic.rationalPlace p).adicCompletionIntegers ℚ)
      ((LocalCyclotomic.rationalPlace p).adicCompletion ℚ)} :
    rationalIdentityMap (p := p) (X := X) (Y := X) (BialgHom.id O X.CoordinateRing) =
      BialgHom.id O (FF.rationalIdentityComponent (p := p) X).CoordinateRing := by
  symm
  apply rationalIdentityMap_unique
  ext a
  rfl

/-- Restriction preserves the original contravariant composition. -/
theorem rationalIdentityMap_comp {X Y Z : FF ((LocalCyclotomic.rationalPlace
  p).adicCompletionIntegers ℚ)
      ((LocalCyclotomic.rationalPlace p).adicCompletion ℚ)} (f : ModelHom X Y)
    (g : ModelHom Y Z) :
    rationalIdentityMap (p := p) (X := X) (Y := Z) (f.comp g) = (rationalIdentityMap (p := p) (X
      := X) (Y := Y) f).comp (rationalIdentityMap (p := p) (X := Y) (Y := Z) g) := by
  symm
  apply rationalIdentityMap_unique
  rw [BialgHom.comp_assoc, rationalIdentityMap_naturality, ← BialgHom.comp_assoc,
    rationalIdentityMap_naturality, BialgHom.comp_assoc]

/-- Restriction retains multiplication by the same integer on the actual connected model. -/
theorem rationalIdentityMap_multiply
    (X : FF ((LocalCyclotomic.rationalPlace p).adicCompletionIntegers ℚ)
      ((LocalCyclotomic.rationalPlace p).adicCompletion ℚ)) (n : ℕ) :
    rationalIdentityMap (X.multiply n) = X.rationalIdentityComponent.multiply n := by
  symm
  apply rationalIdentityMap_unique
  apply genericHom_injective
  ext x
  simp only [genericHom_comp, FF.genericHom_multiply, map_nsmul]

end ThreeAdicPlan.ModelHom
