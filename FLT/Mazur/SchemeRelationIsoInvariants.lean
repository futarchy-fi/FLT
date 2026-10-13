/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeEffectiveEpiSections

/-!
# Original invariant coefficients under an isomorphism of relation schemes

When the source scheme is unchanged, an isomorphism retaining both relation
endpoints preserves literally the invariant subring of original functions.
It also preserves all invariant opens and their principal affine domains.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
namespace FLT.Mazur.SchemeEffectiveEpiSections
variable {X A A' : Scheme.{u}} (p q : A ⟶ X) (p' q' : A' ⟶ X)
  (r : A' ≅ A) (hp : r.hom ≫ p = p') (hq : r.hom ≫ q = q')

include hp hq in
/-- Invariance of every original open is reflected by the actual relation isomorphism. -/
theorem relationIso_invariantOpen_iff (W : X.Opens) :
    p ⁻¹ᵁ W = q ⁻¹ᵁ W ↔ p' ⁻¹ᵁ W = q' ⁻¹ᵁ W := by
  constructor
  · intro h
    have hh := congrArg (fun U : A.Opens ↦ r.hom ⁻¹ᵁ U) h
    simpa only [← Scheme.Hom.comp_preimage, hp, hq] using hh
  · intro h
    have hh := congrArg (fun U : A'.Opens ↦ r.inv ⁻¹ᵁ U) h
    simpa only [← Scheme.Hom.comp_preimage, ← hp, ← hq,
      Iso.inv_hom_id_assoc] using hh

include hp hq in
/-- The full relation detects exactly the same original invariant regular functions. -/
theorem relationIso_invariant_iff (s : Γ(X, ⊤)) :
    p.appTop s = q.appTop s ↔ p'.appTop s = q'.appTop s := by
  rw [← hp, ← hq, Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop]
  exact (appTop_injective r.hom).eq_iff.symm

include hp hq in
/-- The invariant subrings are literally equal inside the ORIGINAL source coefficient ring. -/
theorem relationIso_compatibleFunctions : compatibleFunctions p q = compatibleFunctions p' q' := by
  ext s
  exact relationIso_invariant_iff p q p' q' r hp hq s

/-- A genuine invariant coefficient defines a principal domain invariant under the full relation. -/
theorem compatibleFunctions_basicOpen (s : compatibleFunctions p q) :
    p ⁻¹ᵁ X.basicOpen s.val = q ⁻¹ᵁ X.basicOpen s.val := by
  rw [Scheme.Hom.preimage_basicOpen_top, Scheme.Hom.preimage_basicOpen_top]
  exact congrArg A.basicOpen (show p.appTop s.val = q.appTop s.val from s.property)

/-- On an affine source these invariant principal domains are actual affine opens. -/
theorem compatibleFunctions_basicOpen_affine [IsAffine X] (s : compatibleFunctions p q) :
    IsAffineOpen (X.basicOpen s.val) := (isAffineOpen_top X).basicOpen s.val

end FLT.Mazur.SchemeEffectiveEpiSections
