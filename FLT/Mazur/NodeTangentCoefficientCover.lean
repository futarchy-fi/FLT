/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.NodeTangentDepth
public import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent

/-!
# The actual quadratic tangent coefficient cover and its involution

The existing monic tangent root algebra gives a finite faithfully flat
cover. Its canonical root exchange is an involution over the original
coefficient spectrum, including in residue characteristic two.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur
set_option backward.isDefEq.respectTransparency false
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)
local notation "S" => AdjoinRoot (nodeTangentPolynomial W)

/-- The finite tangent algebra is a faithfully flat extension of the original coefficients. -/
theorem nodeTangentAlgebra_faithfullyFlat [Nontrivial R] :
    (algebraMap R S).FaithfullyFlat := by
  let _ : Nontrivial S :=
    Module.nontrivial_of_finrank_pos (by rw [nodeTangentAlgebra_finrank]; decide)
  let _ : Module.Free R S := (nodeTangentPolynomial_monic W).free_adjoinRoot
  rw [RingHom.faithfullyFlat_algebraMap_iff]
  infer_instance

/-- The original integral tangent algebra defines the splitting coefficient cover. -/
def nodeTangentCover : Spec (.of S) ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R S))

/-- The coefficient cover is flat and surjective as an actual scheme morphism. -/
theorem nodeTangentCover_flat_surjective [Nontrivial R] :
    Flat (nodeTangentCover W) ∧ Surjective (nodeTangentCover W) :=
  (flat_and_surjective_SpecMap_iff (CommRingCat.ofHom (algebraMap R S))).mpr
    (nodeTangentAlgebra_faithfullyFlat W)

/-- The distinguished tangent-root exchange on the original coefficient spectrum. -/
def nodeTangentCoverConjugation : Spec (.of S) ⟶ Spec (.of S) :=
  Spec.map (CommRingCat.ofHom (nodeTangentConjugation W).toRingHom)

/-- Conjugation keeps the original coefficient map, rather than a chosen replacement. -/
@[reassoc] theorem nodeTangentCoverConjugation_structure :
    nodeTangentCoverConjugation W ≫ nodeTangentCover W = nodeTangentCover W := by
  rw [nodeTangentCoverConjugation, nodeTangentCover, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp]
  congr 2
  exact (nodeTangentConjugation W).toAlgHom.comp_algebraMap

/-- The actual coefficient operation squares to the identity. -/
@[reassoc] theorem nodeTangentCoverConjugation_involutive :
    nodeTangentCoverConjugation W ≫ nodeTangentCoverConjugation W = 𝟙 _ := by
  rw [nodeTangentCoverConjugation, ← Spec.map_comp, ← Spec.map_id]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  exact nodeTangentConjugationHom_involutive W

/-- The root exchange is an automorphism of the actual coefficient cover. -/
def nodeTangentCoverConjugationIso : Over.mk (nodeTangentCover W) ≅
    Over.mk (nodeTangentCover W) :=
  Over.isoMk
    { hom := nodeTangentCoverConjugation W
      inv := nodeTangentCoverConjugation W
      hom_inv_id := nodeTangentCoverConjugation_involutive W
      inv_hom_id := nodeTangentCoverConjugation_involutive W }
    (nodeTangentCoverConjugation_structure W)

end FLT.Mazur
