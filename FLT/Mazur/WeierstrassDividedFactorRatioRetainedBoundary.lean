/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFactorRatioPolygonMaps
public import FLT.Mazur.WeierstrassModificationXFactorRatioLaurentEquiv

/-!
# Corrected original initial boundaries at the retained cyclic labels

The exact squared-factor parameter reaches both original retained labels with
the cyclic inversion. Reparametrizing by its inverse gives the standard edge.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (ha : IsUnit W.a₁)
  (s τ : R) (hτ : s = W.a₁ ^ 2 * τ) [Fact (IsNilpotent τ)] (k : ℕ) (hk : 0 < k)
  (b3 b4 b6 : R) (I : Ideal R) (hI : IsNilpotent I) (hs : s ∈ I)
  (h2 : W.a₂ ∈ I) (h3 : b3 ∈ I) (h4 : b4 ∈ I) (h6 : b6 ∈ I)
local notation "r" => polynomialSlopeRoot W b3 b4 b6 I hI ha h2 h3 h4 h6
local notation "hr" => polynomialSlopeRoot_equation W b3 b4 b6 I hI ha h2 h3 h4 h6
local notation "hm" => polynomialSlopeRoot_mem W b3 b4 b6 I hI ha h2 h3 h4 h6
local notation "F" => factorRatioInitialPolygonMap W ha s τ hτ k b3 b4 b6 r hr I hI hm h3
local notation "E" => factorRatioLaurentIso W ha s b3 b4 b6 I hI hs h2 h3 h4 h6
local notation "G" => Spec.map (CommRingCat.ofHom (AlgHom.toRingHom
  (laurentNodeRestriction W s b3 b4 b6 I hI ha hs h2 h3 h4 h6)))

/-- Both original initial Laurent boundaries keep the full correction at their retained labels. -/
@[reassoc] theorem factorRatioInitialPolygonMap_retained_boundary (b : Bool) :
    G ≫ F b = (E).hom ≫ precedingBranch R τ ≫ retainedPolygonMap R τ k ⟨0, hk⟩ b := by
  rw [factorRatioInitialPolygonMap, ← Category.assoc,
    factorRatioLaurentIso_boundary W ha s b3 b4 b6 I hI hs h2 h3 h4 h6 τ hτ,
    Category.assoc, initialPolygonLabel_retained_boundary τ k hk]

/-- The entire inverse corrected parameter recovers the standard retained edge in cyclic order. -/
@[reassoc] theorem factorRatioInitialPolygonMap_retained_inv_boundary (b : Bool) :
    (E).inv ≫ G ≫ F b = precedingBranch R τ ≫ retainedPolygonMap R τ k ⟨0, hk⟩ b := by
  rw [factorRatioInitialPolygonMap_retained_boundary W ha s τ hτ k hk, Iso.inv_hom_id_assoc]

/-- The retained right-edge formula exhibits both the full correction and cyclic inversion. -/
@[reassoc] theorem factorRatioInitialPolygonMap_retained_right_boundary (b : Bool) :
    G ≫ F b = ((E).hom ≫ (edgeInversion R).hom) ≫ rightBranchOpen R τ ≫
      retainedPolygonMap R τ k ⟨0, hk⟩ b := by
  rw [factorRatioInitialPolygonMap_retained_boundary W ha s τ hτ k hk]
  simp only [precedingBranch, Category.assoc]

end FLT.Mazur.WeierstrassDividedDepth
