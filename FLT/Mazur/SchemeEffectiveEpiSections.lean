/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.CategoryTheory.Limits.Shapes.RegularMono

/-!
# Regular functions descend along effective scheme epimorphisms

Global functions are represented by the affine line over the integers.
Consequently a scheme effective epimorphism with its actual kernel pair
also gives existence and uniqueness for compatible regular functions.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace FLT.Mazur.SchemeEffectiveEpiSections

/-- A fixed affine scheme representing one regular function in the given universe. -/
def functionScheme : Scheme.{u} :=
  Spec (.of (MvPolynomial (ULift.{u} Unit) (ULift.{u} ℤ)))

/-- Morphisms to the fixed affine line are precisely global regular functions. -/
def functionEquiv (X : Scheme.{u}) : (X ⟶ functionScheme) ≃ Γ(X, ⊤) :=
  (AffineSpace.toSpecMvPolyIntEquiv (ULift.{u} Unit)).trans (Equiv.funUnique _ _)

/-- The representing equivalence sends composition to actual function pullback. -/
theorem functionEquiv_comp {X Y : Scheme.{u}} (a : X ⟶ Y) (k : Y ⟶ functionScheme) :
    functionEquiv X (a ≫ k) = a.appTop (functionEquiv Y k) := rfl

/-- An epimorphism of schemes detects equality of global regular functions. -/
theorem appTop_injective {X Y : Scheme.{u}} (g : Y ⟶ X) [Epi g] :
    Function.Injective g.appTop := by
  intro s t h
  have he : g ≫ (functionEquiv X).symm s = g ≫ (functionEquiv X).symm t := by
    apply (functionEquiv Y).injective
    simpa only [functionEquiv_comp, Equiv.apply_symm_apply] using h
  exact (functionEquiv X).symm.injective ((cancel_epi g).mp he)

/-- Every regular function equal on the actual kernel pair descends uniquely. -/
theorem sections_existsUnique {X Y P : Scheme.{u}} {g : Y ⟶ X} [EffectiveEpi g]
    {a b : P ⟶ Y} (H : IsPullback a b g g) (s : Γ(Y, ⊤))
    (hs : a.appTop s = b.appTop s) : ∃! t : Γ(X, ⊤), g.appTop t = s := by
  let k := (functionEquiv Y).symm s
  have hk : a ≫ k = b ≫ k := by
    apply (functionEquiv P).injective
    simpa only [functionEquiv_comp, k, Equiv.apply_symm_apply] using hs
  let C := isColimitCoforkOfEffectiveEpi g H.cone H.isLimit
  let t := functionEquiv X (C.desc (Cofork.ofπ k hk))
  have ht : g.appTop t = s := by
    dsimp only [t]
    rw [← functionEquiv_comp]
    exact (congrArg (functionEquiv Y) (Cofork.IsColimit.π_desc C)).trans
      ((functionEquiv Y).apply_symm_apply s)
  exact ⟨t, ht, fun z hz ↦ appTop_injective g (hz.trans ht.symm)⟩

/-- Compatible source functions form the actual equalizer subring. -/
def compatibleFunctions {Y P : Scheme.{u}} (a b : P ⟶ Y) : Subring Γ(Y, ⊤) :=
  RingHom.eqLocus a.appTop.hom b.appTop.hom

/-- Descent identifies the target ring with the actual compatible-function subring. -/
def sectionsRingEquiv {X Y P : Scheme.{u}} {g : Y ⟶ X} [EffectiveEpi g]
    {a b : P ⟶ Y} (H : IsPullback a b g g) : Γ(X, ⊤) ≃+* compatibleFunctions a b := by
  let φ : Γ(X, ⊤) →+* compatibleFunctions a b :=
    g.appTop.hom.codRestrict (compatibleFunctions a b) (fun t ↦
      congrArg (fun k : P ⟶ X ↦ k.appTop t) H.w)
  apply RingEquiv.ofBijective φ
  constructor
  · intro t u h
    exact appTop_injective g (congrArg Subtype.val h)
  · intro s
    obtain ⟨t, ht, _⟩ := sections_existsUnique H s.val s.property
    exact ⟨t, Subtype.ext ht⟩

end FLT.Mazur.SchemeEffectiveEpiSections
