/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DenseGroundEnvelopeInterior
public import FLT.Mazur.CommonGroundEnvelopeCore

/-!
# A concrete coefficient equation supporting every remaining residual obstruction

The dense ground is exactly the principal open of the constructed nonzero
coefficient. At original full fibers, any failure of interior membership
forces that coefficient to vanish. On any etale common ground with a proper
core, the actual residual closure is supported over that same original
coefficient equation. No changed coefficient or branch is substituted.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.AffineEtaleDenseFiniteGround
open SchemeOpenEnvelope CommonGroundEnvelope
set_option backward.isDefEq.respectTransparency false
variable (R : Type) [CommRing R] [IsDomain R]
  (V : Over (Spec (.of R))) [IsAffine V.left] [Etale V.hom]

/-- The dense coefficient open has an explicit single nonzero defining denominator. -/
theorem groundOpen_coe :
    (groundOpen R V : Set (Spec (.of R))) =
      (PrimeSpectrum.basicOpen (coefficient R V) : Set (PrimeSpectrum R)) :=
  PrimeSpectrum.localization_away_comap_range (Localization.Away (coefficient R V)) _

/-- Membership can be checked in the actual original coefficient prime. -/
theorem mem_groundOpen_iff (s : Spec (.of R)) :
    s ∈ groundOpen R V ↔ coefficient R V ∉ s.asIdeal := by
  rw [← SetLike.mem_coe, groundOpen_coe]
  rfl

variable (A : Over (Spec (.of R))) (O : (prod A V).left.Opens)
local notation "π₀" => Over.Hom.left (prod.fst : prod A V ⟶ A)

/-- The remaining full-fiber boundary lies over the vanishing of one nonzero coefficient. -/
theorem coefficient_mem_of_not_interior (x : A.left)
    (hx : x ∈ SchemeOpenEnvelope.fullFiberLocus π₀ O)
    (hi : x ∉ SchemeOpenEnvelope.fullFiberInterior π₀ O) :
    coefficient R V ∈ (A.hom x).asIdeal := by
  by_contra h
  exact hi (original_interior_of_mem_groundOpen R V A O x hx
    ((mem_groundOpen_iff R V _).mpr h))

variable {U : Scheme} (q : U ⟶ Spec (.of R)) [Etale q]
  (T : (pullback V.hom q).Opens) [IsProper (T.ι ≫ pullback.snd V.hom q)]
local notation "B" => changed q A

/-- The residual closure on every common ground lies over the SAME original equation. -/
theorem coefficient_mem_of_residualClosure (x : (B).left)
    (hx : pullback.fst A.hom q x ∈ SchemeOpenEnvelope.fullFiberLocus π₀ O)
    (hr : x ∈ closure (residualImage q A V T O)) :
    coefficient R V ∈ (A.hom (pullback.fst A.hom q x)).asIdeal := by
  apply coefficient_mem_of_not_interior R V A O _ hx
  intro hi
  exact ((original_interior_iff q A V T O x hx).mp hi) hr

/-- Dense-ground full fibers exclude residual accumulation, even on independent refinements. -/
theorem not_mem_residualClosure_over_groundOpen (x : (B).left)
    (hx : pullback.fst A.hom q x ∈ SchemeOpenEnvelope.fullFiberLocus π₀ O)
    (hb : A.hom (pullback.fst A.hom q x) ∈ groundOpen R V) :
    x ∉ closure (residualImage q A V T O) := by
  intro hr
  exact (mem_groundOpen_iff R V _).mp hb
    (coefficient_mem_of_residualClosure R V A O q T x hx hr)

end FLT.Mazur.AffineEtaleDenseFiniteGround
