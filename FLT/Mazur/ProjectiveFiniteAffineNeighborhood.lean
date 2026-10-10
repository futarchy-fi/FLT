/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProjectiveFiniteAvoidance
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Common affine neighborhoods in projective ambients

Positive homogeneous avoidance makes the basic open affine. Pulling it
back along a closed immersion gives a common affine neighborhood of any
finite set in the embedded scheme, over arbitrary coefficient rings.
-/

@[expose] public noncomputable section

open AlgebraicGeometry

universe u v

namespace FLT.Mazur.ProjectiveSpace

attribute [local instance] MvPolynomial.gradedAlgebra

variable {R : Type u} [CommRing R] {ι : Type v}

/-- Every finite set of projective points lies in one affine open. -/
theorem exists_affineOpen_of_finite (T : Set (space R ι)) (hT : T.Finite) :
    ∃ U : (space R ι).affineOpens, T ⊆ U.val := by
  obtain ⟨n, f, hn, hf, hTf⟩ := exists_homogeneous_avoiding_finite T hT
  exact ⟨⟨Proj.basicOpen (grading R ι) f,
    Proj.isAffineOpen_basicOpen _ f hf hn⟩, hTf⟩

/-- A closed projective embedding supplies common affine neighborhoods of finite sets. -/
theorem exists_affineOpen_of_closed_embedding {Z : Scheme.{max u v}}
    (e : Z ⟶ space R ι) [IsClosedImmersion e] (T : Set Z) (hT : T.Finite) :
    ∃ U : Z.affineOpens, T ⊆ U.val := by
  obtain ⟨U, hU⟩ := exists_affineOpen_of_finite (e '' T) (hT.image e)
  exact ⟨⟨e ⁻¹ᵁ U.val, U.property.preimage e⟩,
    fun x hx ↦ hU (Set.mem_image_of_mem e hx)⟩

end FLT.Mazur.ProjectiveSpace
