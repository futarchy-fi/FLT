/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LaurentHopfRootsClassification
public import FLT.Mazur.RootsOfUnityScheme

/-!
# The original affine toric subgroup is the roots-of-unity scheme

Spectrum of the full Hopf comparison gives a group isomorphism over the field.
Its inclusion square uses the actual Laurent quotient, so the comparison does
not discard the infinitesimal structure of a nonetale subgroup.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry MonObj
open scoped LaurentPolynomial

namespace FLT.Mazur.LaurentHopfRootsScheme

universe u
variable {K A : Type u} [Field K] [CommRing A] [HopfAlgebra K A]
  (f : K[T;T⁻¹] →ₐc[K] A) (hf : Function.Surjective f)

/-- The actual spectrum of the original subgroup coordinate algebra. -/
abbrev model : Over (Spec (.of K)) := (Spec (.of A)).asOver (Spec (.of K))

/-- The given coordinate quotient defines the original toric inclusion. -/
def inclusion : model (K := K) (A := A) ⟶ MultiplicativeGroupScheme.gm K :=
  ((bialgSpec (.of K)).map (CommBialgCat.ofHom f).op).hom

instance inclusion_isMonHom : IsMonHom (inclusion f) := by
  unfold inclusion
  infer_instance

/-- The underlying inclusion is exactly the original quotient map on spectra. -/
theorem inclusion_left : (inclusion f).left =
    Spec.map (CommRingCat.ofHom f.toAlgHom.toRingHom) := rfl

/-- The roots comparison is an isomorphism of the full affine monoid schemes. -/
def monoidIso : Mon.mk (model (K := K) (A := A)) ≅
    Mon.mk (RootsOfUnityScheme.model K (Module.finrank K A)) :=
  (bialgSpec (.of K)).mapIso
    (CommBialgCat.isoMk (LaurentHopfRootsClassification.coordinatesEquiv f hf)).op

/-- Forgetting the bundled monoid retains an isomorphism over the original field. -/
def comparison : model (K := K) (A := A) ≅
    RootsOfUnityScheme.model K (Module.finrank K A) :=
  (Mon.forget _).mapIso (monoidIso f hf)

instance comparison_isMonHom : IsMonHom (comparison f hf).hom :=
  inferInstanceAs (IsMonHom (monoidIso f hf).hom.hom)

/-- The comparison preserves the entire original inclusion into the torus. -/
theorem comparison_inclusion :
    (comparison f hf).hom ≫ RootsOfUnityScheme.inclusion K (Module.finrank K A) =
      inclusion f := by
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom
    (LaurentHopfRootsClassification.coordinatesEquiv f hf).toAlgEquiv.toAlgHom.toRingHom) ≫
      Spec.map (CommRingCat.ofHom
        (RootsOfUnityAlgebra.restriction K (Module.finrank K A)).toAlgHom.toRingHom) = _
  rw [← Spec.map_comp]
  congr 1
  exact congrArg (fun g => CommRingCat.ofHom g.toAlgHom.toRingHom)
    (LaurentHopfRootsClassification.coordinatesEquiv_restriction f hf)

end FLT.Mazur.LaurentHopfRootsScheme
