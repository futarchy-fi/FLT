/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OrderedHilbertFaithfulRestrictedIso
public import FLT.Mazur.SchemeRelationIsoInvariants

/-!
# Unchanged original invariant coefficients on the faithful affine tests

The original and localized full relations define literally the same invariant
subring in the unchanged affine source. Every invariant open, including every
principal affine domain from a genuine invariant coefficient, is retained.
Existence of enough such domains to fill the tensor envelope is separate.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.OrderedHilbertFaithfulTestCover
open HilbertChart CartierAbel SchemePicard FCurve AffineEtaleFaithfulNeighborhood
open OrderedHilbertAffineEtaleTestCover RelativeRelationOrbit SchemeEffectiveEpiSections
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (T : Over (Spec (.of R))) (s : (relativeFppfSheaf f).obj.obj (op T))
local notation "E" => fun x ↦ Sigma.fst (Sigma.snd (chartData f hL T s x))
local notation "b" => fun x ↦ spectrumBase
  (Over.hom (Sigma.fst (Sigma.snd (chartData f hL T s x))))
    (Sigma.fst (data f hL T s x))
local notation "q" => fun x ↦ FaithfulNeighborhoodCurve.map f
  (Over.hom (Sigma.fst (Sigma.snd (chartData f hL T s x))))
    (Sigma.fst (data f hL T s x))
local notation "degree" => fun x ↦ Prod.snd (Sigma.fst (chartData f hL T s x))

local notation "h" => fun x ↦ fixedBaseAmple f (b x) hL
local notation "c" => fun x ↦ chartClass f hL T s x
local notation "c'" => fun x ↦ localTranslationClass f hL T s x
local notation "k" => fun x ↦ toOriginalChart f hL T s x
local notation "l" => fun x ↦ localChartParameter f hL T s x
local notation "V" => fun x ↦ localTranslation f hL T s x
local notation "e" => fun x ↦ AffineRestriction.equivalence f hL (degree x) (E x) (c x) (k x)
local notation "e'" => fun x ↦
  AffineRestriction.equivalence (q x) (h x) (degree x) (V x) (c' x) (l x)

local notation "p" => fun x ↦ AffineRestriction.fst f hL (degree x) (E x) (c x) (k x)
local notation "r" => fun x ↦ AffineRestriction.snd f hL (degree x) (E x) (c x) (k x)
local notation "p'" => fun x ↦ AffineRestriction.fst (q x) (h x) (degree x) (V x) (c' x) (l x)
local notation "r'" => fun x ↦ AffineRestriction.snd (q x) (h x) (degree x) (V x) (c' x) (l x)

/-- Every invariant source open is retained and reflected by the actual localized relation. -/
theorem localRestricted_invariantOpen_iff (x : T.left) (W : (test f hL T s x).left.Opens) :
    (p x).left ⁻¹ᵁ W = (r x).left ⁻¹ᵁ W ↔
      (p' x).left ⁻¹ᵁ W = (r' x).left ⁻¹ᵁ W :=
  relationIso_invariantOpen_iff _ _ _ _
    ((Over.forget _).mapIso (localRestrictedRelationIso f hL T s x))
    (localRestrictedRelationProjection_fst f hL T s x)
    (localRestrictedRelationProjection_snd f hL T s x) W

/-- Original coefficient invariance is exactly invariance for the full localized relation. -/
theorem localRestricted_invariant_iff (x : T.left) (a : Γ((test f hL T s x).left, ⊤)) :
    (p x).left.appTop a = (r x).left.appTop a ↔
      (p' x).left.appTop a = (r' x).left.appTop a :=
  relationIso_invariant_iff _ _ _ _
    ((Over.forget _).mapIso (localRestrictedRelationIso f hL T s x))
    (localRestrictedRelationProjection_fst f hL T s x)
    (localRestrictedRelationProjection_snd f hL T s x) a

/-- The constructed comparison retains literally the original invariant coefficient subring. -/
theorem localRestricted_invariantSubring (x : T.left) :
    compatibleFunctions (p x).left (r x).left = compatibleFunctions (p' x).left (r' x).left :=
  relationIso_compatibleFunctions _ _ _ _
    ((Over.forget _).mapIso (localRestrictedRelationIso f hL T s x))
    (localRestrictedRelationProjection_fst f hL T s x)
    (localRestrictedRelationProjection_snd f hL T s x)

/-- A localized invariant coefficient defines an ORIGINAL invariant affine principal domain. -/
theorem localRestricted_invariant_principal (x : T.left)
    (a : compatibleFunctions (p' x).left (r' x).left) :
    IsAffineOpen ((test f hL T s x).left.basicOpen a.val) ∧
      (p x).left ⁻¹ᵁ (test f hL T s x).left.basicOpen a.val =
        (r x).left ⁻¹ᵁ (test f hL T s x).left.basicOpen a.val := by
  have ha : a.val ∈ compatibleFunctions (p x).left (r x).left := by
    rw [localRestricted_invariantSubring]
    exact a.property
  let _ : IsAffine (test f hL T s x).left := data_affine f hL T s x
  exact ⟨compatibleFunctions_basicOpen_affine _ _ ⟨a.val, ha⟩,
    compatibleFunctions_basicOpen _ _ ⟨a.val, ha⟩⟩

end FLT.Mazur.OrderedHilbertFaithfulTestCover
