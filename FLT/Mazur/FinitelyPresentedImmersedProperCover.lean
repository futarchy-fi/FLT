/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SeparatedFinitePresentationModel
public import FLT.Mazur.ImmersedProperCoverBaseChange
public import FLT.Mazur.ChowAffineBasePropernessCriterion

/-!
# Constructed immersed proper covers over arbitrary affine bases

A separated finitely presented scheme descends to a Noetherian integer
model. Its Chow modification and proper projective ambient scheme pull
back to give an actual immersed proper cover over the original ring.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits AlgebraicGeometry
open FLT.Mazur.Chow.AffineBase

namespace FLT.Mazur.Approximation

universe u

/-- Build an immersed proper cover without any Noetherian assumption on the affine base. -/
theorem exists_finitelyPresented_immersed_proper_cover {R : Type u} [CommRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R))
    [IsSeparated f] [QuasiCompact f] [LocallyOfFinitePresentation f] :
    ∃ (Z P : Scheme.{u}) (π : Z ⟶ X) (p : P ⟶ Spec (.of R)) (h : Z ⟶ P),
      IsProper π ∧ Surjective π ∧ IsProper p ∧ IsImmersion h ∧
        QuasiCompact h ∧ h ≫ p = π ≫ f := by
  obtain ⟨S, hS, _, Y, q, a, hsep, hqc, hfp, ha⟩ :=
    exists_separated_finite_presentation_model f ∅ Set.finite_empty
  let _ : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing ℤ S
  let _ : Surjective (graphClosureπ q) := ⟨graphClosureπ_surjective q⟩
  have he : graphClosureToProduct q ≫ (chartData q).projectiveProductProjection =
      graphClosureπ q ≫ q := graphClosureToProduct_projection q
  let _ : QuasiCompact
      (graphClosureToProduct q ≫ (chartData q).projectiveProductProjection) :=
    he.symm ▸ inferInstanceAs (QuasiCompact (graphClosureπ q ≫ q))
  let _ : QuasiCompact (graphClosureToProduct q) :=
    QuasiCompact.of_comp _ (chartData q).projectiveProductProjection
  exact exists_immersed_proper_cover_of_isPullback a f q _ ha (graphClosureπ q)
    (chartData q).projectiveProductProjection (graphClosureToProduct q) he

end FLT.Mazur.Approximation
