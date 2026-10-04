/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModulePullbackMapEquality
public import FLT.Mazur.PolygonCubicComponentSection

/-!
# Sealed component maps for canonical polygon ratios

The actual normalization morphism and the divisor comparison are sealed
separately. The section value is also sealed with its defining equality. Transporting
that value through the sealed sheaf comparison remains a separate lemma.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules
@[expose] public noncomputable section
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.PolygonCubicSections
open FCurve PolygonPinching PolygonPowerNodeEndpoints ProjectiveLineMarkedSectionTransition
variable (K : Type u) [Field K] (n : ℕ) [NeZero n] (hn : 0 < n)
  {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q) (a : Fin n → Kˣ)

/-- The actual component normalization morphism with an opaque implementation. -/
irreducible_def canonicalComponentMap (i : Fin n) : ProjectiveLine.scheme K ⟶ C.left :=
  (componentι K n i ≫ p).left

/-- The actual cubic divisor comparison on the sealed component map. -/
irreducible_def canonicalComponentIso (i : Fin n) :
    (Scheme.Modules.pullback (canonicalComponentMap K n p i)).obj (polygonLine K n hn p q h a 3) ≅
      line K (a i) 3 :=
  pullbackMapEqIso (canonicalComponentMap_def K n p i) (polygonLine K n hn p q h a 3) ≪≫
    PolygonDirectPowerComparison.lineIso K n hn p q h a i 3

/-- The existing component-section value, sealed independently of its sheaf comparison. -/
irreducible_def canonicalComponentSection (i : Fin n)
    (s : Γ(polygonLine K n hn p q h a 3, ⊤)) : Γ(line K (a i) 3, ⊤) :=
  componentSection K n hn p q h a s i

/-- The unsealed comparison acts by the established component-section definition. -/
lemma canonicalComponent_raw_section (i : Fin n)
    (s : Γ(polygonLine K n hn p q h a 3, ⊤)) :
    (PolygonDirectPowerComparison.lineIso K n hn p q h a i 3).hom.app ⊤
      (pullGlobal (componentι K n i ≫ p).left (polygonLine K n hn p q h a 3) s) =
      canonicalComponentSection K n hn p q h a i s :=
  (canonicalComponentSection_def K n hn p q h a i s).symm

end FLT.Mazur.PolygonCubicSections
