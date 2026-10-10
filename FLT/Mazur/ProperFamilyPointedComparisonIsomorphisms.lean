/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProperFamilyPointedFppfSheaf
public import FLT.Mazur.RigidifiedPicardFppfComparison
public import Mathlib.CategoryTheory.Sites.LocallyBijective

/-!
# Actual pointed and rigidified comparison isomorphisms

With sheafness proved by unique effective descent, the original locally
bijective comparisons are isomorphisms. Their underlying maps are unchanged.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.SchemePicard
variable {X S : Scheme.{0}} (f : X ⟶ S) (e : S ⟶ X) (he : e ≫ f = 𝟙 S)
  [IsLocallyNoetherian S] [IsProper f] [Flat f]
  [GeometricallyConnected f] [GeometricallyReduced f]

instance pointedFppfComparison_isIso : IsIso (pointedFppfComparison f e he) := by
  let q : pointedKernelFppfSheaf f e he ⟶ relativeFppfSheaf f :=
    ⟨pointedFppfComparison f e he⟩
  let _ : IsIso q := (Sheaf.isLocallyBijective_iff_isIso q).mp
    ⟨pointedFppfComparison_locallyInjective f e he,
      pointedFppfComparison_locallySurjective f e he⟩
  change IsIso ((sheafToPresheaf (Scheme.fppfTopology.over S) CommGrpCat).map q)
  infer_instance

/-- The pointed kernel comparison is an actual isomorphism under the proper-family hypotheses. -/
def pointedFppfIso : pointedKernelPresheaf f e he ≅ (relativeFppfSheaf f).obj :=
  asIso (pointedFppfComparison f e he)

/-- The pointed isomorphism retains the original comparison on every class. -/
theorem pointedFppfIso_hom : (pointedFppfIso f e he).hom = pointedFppfComparison f e he := rfl

instance rigidifiedFppfComparison_isIso : IsIso (rigidifiedFppfComparison f e he) := by
  unfold rigidifiedFppfComparison
  infer_instance

/-- The original rigidified comparison is an actual isomorphism of presheaves. -/
def rigidifiedFppfIso :
    rigidifiedPresheaf f e he ≅ (relativeFppfSheaf f).obj ⋙ forget CommGrpCat :=
  asIso (rigidifiedFppfComparison f e he)

/-- The rigidified isomorphism retains the original comparison on every class. -/
theorem rigidifiedFppfIso_hom :
    (rigidifiedFppfIso f e he).hom = rigidifiedFppfComparison f e he := rfl

end FLT.Mazur.SchemePicard
