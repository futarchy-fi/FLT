/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RingPairInvariantLocalization
public import FLT.Mazur.SchemeRelationOpenInvariantRings
public import FLT.Mazur.SchemeRelationIsoInvariants
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-!
# Actual invariant sections on principal opens

For a qcqs source and full relation, invariant principal localization agrees
with the equalizer in actual geometric open sections. No affine relation or
effective quotient is assumed.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
universe u
namespace FLT.Mazur.SchemeRelationPrincipalLocalization
open SchemeEffectiveEpiSections
set_option backward.isDefEq.respectTransparency false
variable {D A : Scheme.{u}} (p q : D ⟶ A) (s : compatibleFunctions p q)
local notation "W" => A.basicOpen s.val
local notation "hW" => compatibleFunctions_basicOpen p q s

/-- The original top-to-open restriction algebra on relation coefficients. -/
@[instance_reducible]
def relationAlgebra : Algebra Γ(D, ⊤) Γ(D, p ⁻¹ᵁ W) :=
  (D.presheaf.map (homOfLE le_top : (p ⁻¹ᵁ W) ⟶ ⊤).op).hom.toAlgebra

/-- Top sections and actual open pullbacks commute, including the second endpoint. -/
theorem restriction_square (g : D ⟶ A) (h : (p ⁻¹ᵁ W) ≤ g ⁻¹ᵁ W) (a : Γ(A, ⊤)) :
    g.appLE W (p ⁻¹ᵁ W) h (algebraMap Γ(A, ⊤) Γ(A, W) a) =
      D.presheaf.map (homOfLE le_top : (p ⁻¹ᵁ W) ⟶ ⊤).op (g.appTop a) := by
  change (A.presheaf.map _ ≫ g.appLE W (p ⁻¹ᵁ W) h) a =
    (g.appTop ≫ D.presheaf.map _) a
  rw [Scheme.Hom.map_appLE]
  rfl

variable [CompactSpace A] [QuasiSeparatedSpace A]
  [CompactSpace D] [QuasiSeparatedSpace D]

omit [CompactSpace A] [QuasiSeparatedSpace A] in
/-- The full relation's actual principal-preimage sections are its localized top sections. -/
theorem relation_isLocalization :
    let _ := relationAlgebra p q s
    IsLocalization.Away (p.appTop s.val) Γ(D, p ⁻¹ᵁ W) := by
  have H (U : D.Opens) (hU : U = D.basicOpen (p.appTop s.val)) :
      let _ := (D.presheaf.map (homOfLE le_top : U ⟶ ⊤).op).hom.toAlgebra
      IsLocalization.Away (p.appTop s.val) Γ(D, U) := by
    subst U
    exact isLocalization_basicOpen_of_qcqs isCompact_univ isQuasiSeparated_univ _
  exact H _ (Scheme.Hom.preimage_basicOpen_top p s.val)

/-- Exact localization of the original full invariants in the geometric principal-open sections. -/
def openEquiv : Localization.Away s ≃+* relationOpenFunctions p q W hW := by
  let _ := relationAlgebra p q s
  let _ := relation_isLocalization p q s
  let _ : IsLocalization.Away s.val Γ(A, W) :=
    isLocalization_basicOpen_of_qcqs isCompact_univ isQuasiSeparated_univ _
  let _ := RingPairInvariantLocalization.invariantAlgebra p.appTop.hom q.appTop.hom
    (p.app W).hom (q.appLE W (p ⁻¹ᵁ W) (hW).le).hom
    (fun a ↦ by
      simpa only [relationAlgebra, RingHom.algebraMap_toAlgebra,
        Scheme.Hom.appLE_eq_app] using restriction_square p q s p le_rfl a)
    (restriction_square p q s q (hW).le)
  exact (RingPairInvariantLocalization.equivalence p.appTop.hom q.appTop.hom
    (p.app W).hom (q.appLE W (p ⁻¹ᵁ W) (hW).le).hom
    (fun a ↦ by
      simpa only [relationAlgebra, RingHom.algebraMap_toAlgebra,
        Scheme.Hom.appLE_eq_app] using restriction_square p q s p le_rfl a)
    (restriction_square p q s q (hW).le) s).toRingEquiv

/-- The geometric comparison retains the literal restriction of every original invariant. -/
theorem openEquiv_algebraMap (a : compatibleFunctions p q) :
    (openEquiv p q s (algebraMap _ (Localization.Away s) a)).val =
      algebraMap Γ(A, ⊤) Γ(A, W) a.val := by
  let _ := relationAlgebra p q s
  let _ := relation_isLocalization p q s
  let _ : IsLocalization.Away s.val Γ(A, W) :=
    isLocalization_basicOpen_of_qcqs isCompact_univ isQuasiSeparated_univ _
  exact RingPairInvariantLocalization.equivalence_algebraMap p.appTop.hom q.appTop.hom
    (p.app W).hom (q.appLE W (p ⁻¹ᵁ W) (hW).le).hom
    (fun a ↦ by
      simpa only [relationAlgebra, RingHom.algebraMap_toAlgebra,
        Scheme.Hom.appLE_eq_app] using restriction_square p q s p le_rfl a)
    (restriction_square p q s q (hW).le) s a

/-- Every geometrically invariant principal section has an original invariant numerator. -/
theorem exists_invariant_numerator (z : relationOpenFunctions p q W hW) :
    ∃ (a : compatibleFunctions p q) (n : ℕ),
      z.val * algebraMap Γ(A, ⊤) Γ(A, W) (s.val ^ n) =
        algebraMap Γ(A, ⊤) Γ(A, W) a.val := by
  let _ := relationAlgebra p q s
  let _ := relation_isLocalization p q s
  let _ : IsLocalization.Away s.val Γ(A, W) :=
    isLocalization_basicOpen_of_qcqs isCompact_univ isQuasiSeparated_univ _
  exact RingPairInvariantLocalization.invariant_numerator p.appTop.hom q.appTop.hom
    (p.app W).hom (q.appLE W (p ⁻¹ᵁ W) (hW).le).hom
    (fun a ↦ by
      simpa only [relationAlgebra, RingHom.algebraMap_toAlgebra,
        Scheme.Hom.appLE_eq_app] using restriction_square p q s p le_rfl a)
    (restriction_square p q s q (hW).le) s z

end FLT.Mazur.SchemeRelationPrincipalLocalization
