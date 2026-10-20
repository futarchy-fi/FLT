/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ToricFiniteSubgroupHopfPresentation

/-!
# The original toric subgroup gives a finite Hopf quotient of its prescribed rank

Closedness makes the constructed Laurent restriction surjective. Its coordinate
algebra is finite with dimension exactly the original scheme-theoretic degree.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry
open scoped LaurentPolynomial

namespace FLT.Mazur.ToricFiniteSubgroupHopfPresentation

open GeneralizedEllipticCurve

variable {K : Type} [Field K] {E : GeneralizedEllipticCurve (Spec (.of K))}
  {n : ℕ} (H : E.FiniteSubgroup n)

/-- The constructed Hopf coordinates retain the prescribed finite locally free degree. -/
theorem coordinates_degree : FCurve.FiniteLocallyFreeDegree
    (Spec.map (CommRingCat.ofHom (algebraMap K (coordinates H)))) n :=
  H.degree.of_overIso (carrierIso H).symm

/-- The original coordinate algebra is a finite module over the original field. -/
instance coordinates_finite : Module.Finite K (coordinates H) := by
  have h := (coordinates_degree H).1
  rw [IsFinite.SpecMap_iff] at h
  exact RingHom.finite_algebraMap.mp h

/-- Its vector-space dimension is the original subgroup rank, including inseparable length. -/
theorem coordinates_finrank : Module.finrank K (coordinates H) = n := by
  have h := (coordinates_degree H).2.2.2 (⊥ : PrimeSpectrum K)
  rw [FCurve.finrank_spec_algebraMap, Module.rankAtStalk_eq_finrank_of_free] at h
  exact h

variable (e : MultiplicativeGroupScheme.gm K ≅ E.group) [IsMonHom e.hom]

/-- The original toric inclusion remains a closed immersion in Hopf coordinates. -/
theorem restriction_closed : IsClosedImmersion
    (Spec.map (CommRingCat.ofHom (restriction H e).toAlgHom.toRingHom)) := by
  rw [restriction_spec]
  let _ : IsIso (carrierIso H).hom.left :=
    inferInstanceAs (IsIso ((Over.forget _).map (carrierIso H).hom))
  let _ : IsIso e.inv.left := inferInstanceAs (IsIso ((Over.forget _).map e.inv))
  change IsClosedImmersion ((carrierIso H).hom.left ≫ H.inclusion.left ≫ e.inv.left)
  infer_instance

/-- The actual original inclusion gives a surjective Laurent Hopf quotient. -/
theorem restriction_surjective : Function.Surjective (restriction H e) := by
  let φ := CommRingCat.ofHom (restriction H e).toAlgHom.toRingHom
  let _ : IsClosedImmersion (Spec.map φ) := restriction_closed H e
  have hs := (IsClosedImmersion.isAffine_surjective_of_isAffine (Spec.map φ)).2
  exact (RingHom.surjective_respectsIso.arrow_mk_iso_iff
    (arrowIsoΓSpecOfIsAffine φ)).mpr hs

end FLT.Mazur.ToricFiniteSubgroupHopfPresentation
