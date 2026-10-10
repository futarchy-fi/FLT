/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IncreasingCechLocalizedCartesian

/-!
# Generic comparison over the structural ring of an affine base

The canonical affine isomorphism normalizes the scalar action. Thus the generic
kernel theorem applies to the actual structural differential, and gives actual
cartesian functions on one principal open without a kernel hypothesis.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.IncreasingCechCartesian
open IncreasingCechScalars FCurve Chow.AffineBase

variable {X S : Scheme.{0}} [IsAffine S] (f : X ⟶ S)

/-- Passing to the canonical affine presentation preserves the structural scalar map. -/
lemma affinePresentation_scalars :
    baseCohomologyScalars (f ≫ S.isoSpec.hom) = f.appTop.hom := by
  unfold baseCohomologyScalars
  change ((Scheme.ΓSpecIso Γ(S, ⊤)).inv ≫ (f ≫ S.toSpecΓ).appTop).hom = _
  rw [Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop, Iso.inv_hom_id_assoc]

variable [IsNoetherianRing Γ(S, ⊤)] [IsDomain Γ(S, ⊤)]
  [IsProper f] [Flat f] [X.IsSeparated]
  {ι : Type} [LinearOrder ι] [Finite ι] (U : ι → X.Opens)
  (hU : ∀ i, IsAffineOpen (U i)) (hCover : iSup U = ⊤)

include hU hCover in
/-- One nonzero structural section works for all tensor kernels and all coefficients. -/
theorem exists_affine_generic_tensorKer_bijective :
    ∃ r : Γ(S, ⊤), r ≠ 0 ∧
      ∀ (n : ℕ) (B : Type) [AddCommGroup B] [Module (Localization.Away r) B],
        Function.Bijective (LinearMap.tensorKer (Localization.Away r) B
          (localD (structureModule X) U f.appTop.hom (Submonoid.powers r) n)) := by
  have h := exists_generic_structure_tensorKer_bijective (f ≫ S.isoSpec.hom) U hU hCover
  rw [affinePresentation_scalars] at h
  exact h

include hU hCover in
/-- Every affine cartesian base change over that localization has actual section comparison. -/
theorem exists_affine_generic_sectionsComparison_bijective :
    ∃ r : Γ(S, ⊤), r ≠ 0 ∧ ∀ {P T : Scheme.{0}}
      {p : P ⟶ X} {q : P ⟶ T} {g : T ⟶ S}
      (h : IsPullback p q f g) [IsAffine T],
      let _ : Algebra Γ(S, ⊤) Γ(T, ⊤) := g.appTop.hom.toAlgebra
      ∀ [Algebra (Localization.Away r) Γ(T, ⊤)]
        [IsScalarTower Γ(S, ⊤) (Localization.Away r) Γ(T, ⊤)],
        Function.Bijective (localizedSectionsComparison h U hU hCover (Submonoid.powers r)) := by
  obtain ⟨r, hr, hk⟩ := exists_affine_generic_tensorKer_bijective f U hU hCover
  refine ⟨r, hr, ?_⟩
  intro P T p q g h _
  dsimp only
  let _ : Algebra Γ(S, ⊤) Γ(T, ⊤) := g.appTop.hom.toAlgebra
  intro _ _
  exact localizedSectionsComparison_bijective h U hU hCover (Submonoid.powers r)
    (hk 0 Γ(T, ⊤))

end FLT.Mazur.IncreasingCechCartesian
