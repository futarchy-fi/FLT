/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonActionAssociativity
public import FLT.Mazur.ProjectiveLineProductTorusRestriction

/-!
# Parameterized polygon maps are detected on the original component tori

Flat parameter change retains the epic normalization. For Laurent parameters,
density then extends equality on each torus across all nodes of the polygon.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory
namespace FLT.Mazur.PolygonPinching
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u

/-- Products with a finite coproduct are detected on the original summands. -/
theorem parameterized_coproduct_hom_ext {S : Scheme.{u}} {I : Type} [Finite I]
    (X : Over S) (Y : I → Over S) {Z : Over S} (f g : X ⊗ (∐ Y) ⟶ Z)
    (h : ∀ i, X ◁ Sigma.ι Y i ≫ f = X ◁ Sigma.ι Y i ≫ g) : f = g := by
  let e := coproductUniqueIso (fun _ : PUnit => X)
  apply (cancel_epi (e.hom ▷ (∐ Y))).mp
  apply PolygonSplitGroup.tensor_hom_ext (fun _ : PUnit => X) Y
  intro i j
  simpa only [e, tensorHom_comp_whiskerRight_assoc, ι_coproductUniqueIso_hom,
    eqToHom_refl, id_tensorHom] using h j

variable (K : Type u) [Field K] (n : ℕ) [NeZero n] (hn : 0 < n)
variable {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)

include h in
/-- The complete normalization detects morphisms after any flat parameter change. -/
theorem parameterized_hom_ext (X : Over (Spec (.of K))) [Flat X.hom]
    {Y : Over (Spec (.of K))} (f g : X ⊗ C ⟶ Y)
    (he : ∀ i, X ◁ (componentι K n i ≫ p) ≫ f =
      X ◁ (componentι K n i ≫ p) ≫ g) : f = g := by
  let _ := PolygonActionAssociativity.tensor_normalization_epi K n hn p q h X
  apply (cancel_epi (X ◁ p)).mp
  apply parameterized_coproduct_hom_ext X (fun _ : Fin n => component K)
  intro i
  simpa only [componentι, ← whiskerLeft_comp_assoc] using he i

include h in
/-- Each torus suffices for a Laurent-parameter family of maps into a separated target. -/
theorem gm_hom_ext_tori {Y : Over (Spec (.of K))} [IsSeparated Y.hom]
    (f g : MultiplicativeGroupScheme.gm K ⊗ C ⟶ Y)
    (he : ∀ i, MultiplicativeGroupScheme.gm K ◁
      (torusToComponent K ≫ componentι K n i ≫ p) ≫ f =
      MultiplicativeGroupScheme.gm K ◁
        (torusToComponent K ≫ componentι K n i ≫ p) ≫ g) : f = g := by
  apply parameterized_hom_ext K n hn p q h
  intro i
  apply ProjectiveLineProductCharts.product_hom_ext_torus K (LaurentPolynomial K)
  change MultiplicativeGroupScheme.gm K ◁ torusToComponent K ≫
      MultiplicativeGroupScheme.gm K ◁ (componentι K n i ≫ p) ≫ f =
    MultiplicativeGroupScheme.gm K ◁ torusToComponent K ≫
      MultiplicativeGroupScheme.gm K ◁ (componentι K n i ≫ p) ≫ g
  simpa only [← whiskerLeft_comp_assoc] using he i

end FLT.Mazur.PolygonPinching
