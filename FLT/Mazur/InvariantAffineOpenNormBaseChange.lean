/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.InvariantAffineOpenNormCoefficient

/-!
# Full norm coefficients under exact changes of invariant domains

An arbitrary Cartesian relation change preserves the local norm on exact
preimage domains. This includes the nonflat closed transitions of a rank
thickening and retains the entire relation in the pullback square.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.InvariantAffineOpenNormCoefficient
set_option backward.isDefEq.respectTransparency false
variable {D X D' X' : Scheme.{0}} (p q : D ⟶ X) (p' q' : D' ⟶ X')
  [IsFinite p] [Flat p] [LocallyOfFinitePresentation p]
  [IsFinite p'] [Flat p'] [LocallyOfFinitePresentation p']
  (e : CategoryTheory.EquivalenceRelation p q) (e' : CategoryTheory.EquivalenceRelation p' q')
  (f : X' ⟶ X) (g : D' ⟶ D) (H : IsPullback g p' p f) (hq : g ≫ q = q' ≫ f)
  (U : X.Opens) (V : X'.Opens) (hU : p ⁻¹ᵁ U = q ⁻¹ᵁ U)
  (hV : p' ⁻¹ᵁ V = q' ⁻¹ᵁ V) (haU : IsAffineOpen U) (haV : IsAffineOpen V)
  (hUV : V = f ⁻¹ᵁ U)

include H hq in
/-- Norms commute with every exact Cartesian transition of affine invariant domains. -/
theorem coefficient_baseChange (a : Γ(X, ⊤)) :
    (coefficient p' q' e' V hV haV (f.appTop a)).val =
      (f.resLE U V hUV.le).appTop (coefficient p q e U hU haU a).val := by
  let _ : IsAffine U.toScheme := haU
  let _ : IsAffine V.toScheme := haV
  let _ : IsFinite (p.resLE U _ le_rfl) := by
    rw [Scheme.Hom.resLE_eq_morphismRestrict]; infer_instance
  let _ : IsFinite (p'.resLE V _ le_rfl) := by
    rw [Scheme.Hom.resLE_eq_morphismRestrict]; infer_instance
  let _ : IsAffine (p ⁻¹ᵁ U).toScheme := isAffine_of_isAffineHom (p.resLE U _ le_rfl)
  let _ : IsAffine (p' ⁻¹ᵁ V).toScheme := isAffine_of_isAffineHom (p'.resLE V _ le_rfl)
  have hb : p' ⁻¹ᵁ V = g ⁻¹ᵁ (p ⁻¹ᵁ U) := by
    rw [hUV, ← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, H.w]
  let b := g.resLE (p ⁻¹ᵁ U) (p' ⁻¹ᵁ V) hb.le
  have hp : IsPullback b (p'.resLE V _ le_rfl) (p.resLE U _ le_rfl)
      (f.resLE U V hUV.le) := by
    apply Scheme.Hom.isPullback_resLE H hUV.le le_rfl
    rw [← hb, inf_idem]
  have hs : b ≫ q.resLE U _ hU.le = q'.resLE V _ hV.le ≫ f.resLE U V hUV.le := by
    apply (cancel_mono U.ι).mp
    simp only [Category.assoc, Scheme.Hom.resLE_comp_ι,
      Scheme.Hom.resLE_comp_ι_assoc, b, hq]
  let eU := EquivalenceRelationFiber.invariantRestrictionEquivalence e
    (first_isPullback p U) (Scheme.Hom.resLE_comp_ι q hU.le).symm
  let eV := EquivalenceRelationFiber.invariantRestrictionEquivalence e'
    (first_isPullback p' V) (Scheme.Hom.resLE_comp_ι q' hV.le).symm
  have he := FiniteFlatRelationNormCoefficient.coefficient_baseChange
    _ _ eU _ _ eV _ _ hp hs (U.ι.appTop a)
  have ht : (f.resLE U V hUV.le).appTop (U.ι.appTop a) = V.ι.appTop (f.appTop a) := by
    change (f.resLE U V hUV.le ≫ U.ι).appTop a = (V.ι ≫ f).appTop a
    rw [Scheme.Hom.resLE_comp_ι]
  rw [ht] at he
  exact he

end FLT.Mazur.InvariantAffineOpenNormCoefficient
