/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProperLocalAdicIdealSeparation
public import FLT.Mazur.CartesianIdentityFactorization
public import FLT.Mazur.PolygonDivisorPowerPullback
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# A finite comparison is invertible from its actual adic identities

The diagonal ideal vanishes on every adic test and hence vanishes globally.
The finite comparison is then a closed immersion; the same argument kills
its defining ideal. This proves existence of the global inverse.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace FLT.Mazur.ProperLocalAdic
open FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : CommRingCat.{u}} [IsLocalRing R] {X Y : Scheme.{u}}
  [IsLocallyNoetherian Y] (f : X ⟶ Y) [IsFinite f]
  (g : Y ⟶ Spec R) [IsProper g] (I : (Spec R).IdealSheafData)
  (hI : IsLocalRing.closedPoint R ∈ I.support)
  (T : ℕ → Scheme.{u}) (i : ∀ m, T m ⟶ X)
  (hc : ∀ m, IsClosedImmersion (i m ≫ f))
  (hk : ∀ m, (i m ≫ f).ker = I.comap g ^ (m + 1))
  (hp : ∀ m, IsPullback (𝟙 (T m)) (i m) (i m ≫ f) f)

include hI hc hk hp

/-- The actual adic cartesian identities make the finite comparison a monomorphism. -/
theorem mono_of_cartesian_identities : Mono f := by
  let W := pullback f f
  let a : W ⟶ X := pullback.fst f f
  let b : W ⟶ X := pullback.snd f f
  let p : W ⟶ Spec R := (a ≫ f) ≫ g
  let _ : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian (a ≫ f)
  have hdiag : (pullback.diagonal f).ker = ⊥ := by
    apply ideal_eq_bot_of_le_powers p I hI
    intro m
    let _ := hc m
    let k := pullback.fst (a ≫ f) (i m ≫ f)
    let t := pullback.snd (a ≫ f) (i m ≫ f)
    have hab : k ≫ a = k ≫ b := by
      apply CartesianIdentity.eq_of_factorization (i m) f (hp m) t
      · exact (pullback.condition (f := a ≫ f) (g := i m ≫ f)).symm.trans
          (Category.assoc k a f).symm
      · rw [Category.assoc, Category.assoc]
        exact congrArg (k ≫ ·) (pullback.condition (f := f) (g := f))
    have hl : (k ≫ a) ≫ pullback.diagonal f = k := by
      apply pullback.hom_ext
      · simp only [Category.assoc, pullback.diagonal_fst, Category.comp_id, a]
      · simpa only [Category.assoc, pullback.diagonal_snd, Category.comp_id] using hab
    have hj := (k ≫ a).le_ker_comp (pullback.diagonal f)
    rw [hl] at hj
    have hker : k.ker = I.comap p ^ (m + 1) := by
      rw [Scheme.IdealSheafData.ker_fst_of_isClosedImmersion, hk,
        idealSheaf_comap_pow, ← Scheme.IdealSheafData.comap_comp]
    exact hj.trans_eq hker
  have : IsIso (pullback.diagonal f) := IsClosedImmersion.isIso_iff_ker_eq_bot.mpr hdiag
  exact (pullback.isIso_diagonal_iff f).mp this

/-- A finite morphism with all the actual adic cartesian identities is an isomorphism. -/
theorem isIso_of_cartesian_identities : IsIso f := by
  let _ := mono_of_cartesian_identities f g I hI T i hc hk hp
  let _ : IsClosedImmersion f :=
    (IsClosedImmersion.iff_isFinite_and_mono f).mpr ⟨inferInstance, inferInstance⟩
  apply IsClosedImmersion.isIso_iff_ker_eq_bot.mpr
  apply ideal_eq_bot_of_le_powers g I hI
  intro m
  exact ((i m).le_ker_comp f).trans_eq (hk m)

end FLT.Mazur.ProperLocalAdic
