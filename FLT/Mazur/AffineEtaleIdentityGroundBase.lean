/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineEtaleTranslationFiniteBranch

/-!
# The affine translation itself as a coefficient spectrum

Changing the ground base to the translation spectrum gives an identity
translation. The comparison with the original translation is an isomorphism;
no points or residue branches of that comparison are discarded.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.AffineEtaleIdentityGroundBase
open Approximation EtaleTranslationBranch
universe u
set_option backward.isDefEq.respectTransparency false
variable {R : Type u} [CommRing R] [Algebra.FiniteType ℤ R]
  (V : Over (Spec (.of R))) [IsAffine V.left] [Etale V.hom]

/-- The new coefficient ring is the actual global section ring of the translation. -/
theorem coefficient_finiteType : Algebra.FiniteType ℤ Γ(V.left, ⊤) := by
  let _ := affineBaseSectionAlgebra V.hom
  let _ := sectionAlgebra_etale V.hom
  exact finiteType_integer_base (R := R)

/-- The ground-base map retains the original translation structural morphism. -/
def base : Spec (.of Γ(V.left, ⊤)) ⟶ Spec (.of R) := V.left.isoSpec.inv ≫ V.hom

instance base_etale : Etale (base V) := by
  unfold base
  infer_instance

/-- The new translation has precisely the new coefficient spectrum as its source. -/
def translation : Over (Spec (.of Γ(V.left, ⊤))) := Over.mk (𝟙 _)

instance translation_affine : IsAffine (translation V).left := inferInstanceAs (IsAffine (Spec _))
instance translation_etale : Etale (translation V).hom := inferInstanceAs (Etale (𝟙 _))
instance translation_finite : IsFinite (translation V).hom := inferInstanceAs (IsFinite (𝟙 _))
instance translation_surjective : Surjective (translation V).hom :=
  inferInstanceAs (Surjective (𝟙 _))
instance translation_mono : Mono (translation V).hom := inferInstanceAs (Mono (𝟙 _))

/-- The translation comparison retains every original point, through the affine spectrum iso. -/
def comparison : (Over.map (base V)).obj (translation V) ⟶ V :=
  Over.homMk V.left.isoSpec.inv (by
    change V.left.isoSpec.inv ≫ V.hom = 𝟙 _ ≫ (V.left.isoSpec.inv ≫ V.hom)
    rw [Category.id_comp])

instance comparison_left_isIso : IsIso (comparison V).left :=
  inferInstanceAs (IsIso V.left.isoSpec.inv)

omit [Algebra.FiniteType ℤ R] [Etale V.hom] in
/-- Every original translation point has an exact lift to the new identity translation. -/
theorem comparison_point (v : V.left) :
    (comparison V).left (V.left.isoSpec.hom v) = v := by
  exact congrArg (fun g : V.left ⟶ V.left ↦ g v) V.left.isoSpec.hom_inv_id

end FLT.Mazur.AffineEtaleIdentityGroundBase
