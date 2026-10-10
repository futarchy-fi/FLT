/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProperFamilyOriginalOrbits
public import FLT.Mazur.ProperFamilyTwistDescent

/-!
# The original relative Cartier Abel fiber is represented on every test base

Descent of the actual total-space line isomorphism identifies the original
base-line orbit relation with equality of full relative Cartier divisors.
The equivalence retains the original test family and its actual atlas map.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
namespace FLT.Mazur.CartierAbel
open ProperFamilyAtlas FCurve LineSectionBaseChange DualAtlasLineQuotient
open LocallyFreeDualProjectiveAtlas
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] ModuleSheafTensor.tensor twistedSectionPushforwardEquiv
attribute [local irreducible] LocallyFreeDualProjectiveAtlas.space
attribute [local irreducible] LocallyFreeDualProjectiveAtlas.projection
variable {P X T S : Scheme.{0}} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
  {p : P ⟶ X} {q : P ⟶ T} {f : X ⟶ S} {g : T ⟶ S}
  [IsProper f] [Flat f] [GeometricallyIntegral f] (h : IsPullback p q f g)
  (L : X.Modules) (hL : LocallyFreeRankOne L)
  (hV : ∀ (z : PrimeSpectrum Γ(S, ⊤)) n,
    Subsingleton (ModuleH (residueAlgebraFiberLine f L z) (n + 1)))

local notation "M" => Functor.obj (pushforward f) L
local notation "hM" => properLinePushforward_locallyFiniteFree f L hL hV
local notation "N" => Functor.obj (pushforward q) (Functor.obj (pullback p) L)
local notation "e" => properLineArbitraryBaseChangeIso h L hL hV


local notation "R" => RelativeSection q (Functor.obj (pullback p) L) (hL.pullback p)

/-- On every test family the base-line and total-space section relations coincide. -/
lemma familyBaseLineSetoid_iff_sectionSetoid (s t : R) :
    (familyBaseLineSetoid h L hL hV).r s t ↔
      (relativeSectionSetoid q ((pullback p).obj L) (hL.pullback p)).r s t := by
  let _ : IsLocallyNoetherian S := isLocallyNoetherian_of_affine_cover
    (S := fun _ : Unit ↦ ⟨⊤, isAffineOpen_top S⟩) (by simp) (fun _ ↦ inferInstance)
  let _ : GeometricallyConnected f := ⟨by
    intro K _ a Y p q H
    let _ := GeometricallyIntegral.geometrically_isIntegral (f := f) a p q H
    infer_instance⟩
  exact (familyBaseLineSetoid_iff_iso h L hL hV s t).trans
    (ProperFamilyLineDescent.sectionSetoid_iff_originalTwistRelation h
      ((pullback p).obj L) (hL.pullback p) s.val t.val).symm

/-- Equality of actual original atlas maps is exactly equality of the full original divisors. -/
lemma toFamilyAtlas_eq_iff_fiber (s t : R) :
    s.toFamilyAtlas h L hL hV = t.toFamilyAtlas h L hL hV ↔
      relativeSectionToFiber q ((pullback p).obj L) (hL.pullback p) s =
        relativeSectionToFiber q ((pullback p).obj L) (hL.pullback p) t :=
  (toFamilyAtlas_eq_iff h L hL hV s t).trans
    ((familyBaseLineSetoid_iff_sectionSetoid h L hL hV s t).trans
      (relativeSectionToFiber_eq_iff q ((pullback p).obj L) (hL.pullback p) s t).symm)

/-- The full relative Cartier divisor of an actual original atlas morphism. -/
def familyAtlasToFiber (a : TestMorphism L hL hV (g := g)) :
    RelativeFiber q ((pullback p).obj L) (hL.pullback p) :=
  relativeSectionToFiber q ((pullback p).obj L) (hL.pullback p)
    (familySectionOfAtlas h L hL hV a)

/-- The atlas assignment retains every original relative section's full zero divisor. -/
lemma familyAtlasToFiber_toFamilyAtlas (s : R) :
    familyAtlasToFiber h L hL hV (s.toFamilyAtlas h L hL hV) =
      relativeSectionToFiber q ((pullback p).obj L) (hL.pullback p) s :=
  (toFamilyAtlas_eq_iff_fiber h L hL hV _ s).mp
    (toFamilyAtlas_familySectionOfAtlas h L hL hV (s.toFamilyAtlas h L hL hV))

/-- Full original relative Cartier divisors distinguish the actual atlas morphisms. -/
lemma familyAtlasToFiber_injective : Function.Injective (familyAtlasToFiber h L hL hV) := by
  intro a b hab
  have he := (toFamilyAtlas_eq_iff_fiber h L hL hV
    (familySectionOfAtlas h L hL hV a) (familySectionOfAtlas h L hL hV b)).mpr hab
  simpa only [toFamilyAtlas_familySectionOfAtlas] using he

/-- Every divisor in the actual relative Abel fiber is obtained on the original atlas. -/
lemma familyAtlasToFiber_surjective : Function.Surjective (familyAtlasToFiber h L hL hV) := by
  intro D
  obtain ⟨s, hs⟩ := relativeQuotientToFiber_surjective q ((pullback p).obj L) (hL.pullback p) D
  induction s using Quotient.inductionOn with | h s =>
    exact ⟨s.toFamilyAtlas h L hL hV, (familyAtlasToFiber_toFamilyAtlas h L hL hV s).trans hs⟩

/-- The actual original scheme atlas represents the relative Cartier Abel fiber on every base. -/
def familyAtlasRelativeFiberEquiv : TestMorphism L hL hV (g := g) ≃
    RelativeFiber q ((pullback p).obj L) (hL.pullback p) :=
  Equiv.ofBijective (familyAtlasToFiber h L hL hV)
    ⟨familyAtlasToFiber_injective h L hL hV, familyAtlasToFiber_surjective h L hL hV⟩

/-- The representing equivalence preserves the full independently supplied original divisor. -/
lemma familyAtlasRelativeFiberEquiv_toFamilyAtlas (s : R) :
    familyAtlasRelativeFiberEquiv h L hL hV (s.toFamilyAtlas h L hL hV) =
      relativeSectionToFiber q ((pullback p).obj L) (hL.pullback p) s :=
  familyAtlasToFiber_toFamilyAtlas h L hL hV s

/-- Every original divisor recovers exactly the atlas map of each of its original sections. -/
lemma familyAtlasRelativeFiberEquiv_symm_section (s : R) :
    (familyAtlasRelativeFiberEquiv h L hL hV).symm
      (relativeSectionToFiber q ((pullback p).obj L) (hL.pullback p) s) =
        s.toFamilyAtlas h L hL hV := by
  rw [← familyAtlasRelativeFiberEquiv_toFamilyAtlas h L hL hV s, Equiv.symm_apply_apply]

end FLT.Mazur.CartierAbel
