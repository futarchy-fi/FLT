/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Deformations.ContinuousTangentQuotient
public import FLT.Deformations.FiniteTangentSeparation
public import FLT.Deformations.ProartinianGenerators

/-!
# Finite continuous tangents imply the adic topology

Separate relative cotangent classes in every discrete open quotient. The
common tangent kernel is therefore contained in the closed relative-square
ideal. Compact Nakayama then gives finite maximal-ideal generation and adic
completeness, without assuming Noetherianity of the target.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory IsLocalRing
namespace Deformation.ProartinianCat

variable {O : Type} [CommRing O] [IsLocalRing O] [Finite (ResidueField O)]
  {A B : ProartinianCat O}

omit [Finite (ResidueField O)] in
/-- Relative-square relations commute with surjective coefficient morphisms. -/
theorem relativeSquareIdeal_map (f : A ⟶ B) (hf : Function.Surjective f.hom) :
    (relativeSquareIdeal A).map f.hom.toRingHom = relativeSquareIdeal B := by
  unfold relativeSquareIdeal coefficientMaximalIdeal
  rw [Ideal.map_sup, Ideal.map_map, Ideal.map_pow,
    map_maximalIdeal_of_surjective f.hom.toRingHom hf]
  congr 2
  exact f.hom.toAlgHom.comp_algebraMap

variable (A) [Finite (continuousTangent O A)]

/-- Elements of the common tangent kernel have zero value under every tangent. -/
theorem tangentOpenIdeal_tangent_zero {a : A}
    (ha : a ∈ OpenIdeal.ideal (tangentOpenIdeal A)) (d : continuousTangent O A) :
    d.1 a = 0 := by
  let := finite_dualNumberHom A
  have hz := parameterOpenIdeal_le_ker A (dualNumberTest O)
    (tangentToDualNumber O A d) ha
  exact congrArg TrivSqZeroExt.snd hz

/-- Continuous tangents separate the quotient by the closed relative-square ideal. -/
theorem tangentOpenIdeal_le_relativeSquare_closure :
    OpenIdeal.ideal (tangentOpenIdeal A) ≤ (relativeSquareIdeal A).closure := by
  intro a ha
  apply mem_closedIdeal_of_mem_sup_open A (relativeSquareIdeal A).closure isClosed_closure
  intro I
  let Q := openIdealQuotient A I
  let f := openIdealQuotientHom A I
  let : DiscreteTopology Q := inferInstanceAs (DiscreteTopology (A ⧸ OpenIdeal.ideal I))
  have ham : a ∈ maximalIdeal A := ha.2
  have hfm : f.hom a ∈ maximalIdeal Q := by
    rw [← map_maximalIdeal_of_surjective f.hom.toRingHom Ideal.Quotient.mk_surjective]
    exact Ideal.mem_map_of_mem _ ham
  have hq : f.hom a ∈ relativeSquareIdeal Q :=
    mem_relativeSquareIdeal_of_tangent_zero Q hfm (fun d ↦
      tangentOpenIdeal_tangent_zero A ha (continuousTangentPullback f d))
  rw [← relativeSquareIdeal_map f Ideal.Quotient.mk_surjective] at hq
  have hcom : a ∈ ((relativeSquareIdeal A).map f.hom.toRingHom).comap
      f.hom.toRingHom := hq
  rw [Ideal.comap_map_of_surjective f.hom.toRingHom Ideal.Quotient.mk_surjective] at hcom
  change a ∈ relativeSquareIdeal A ⊔ RingHom.ker (Ideal.Quotient.mk (OpenIdeal.ideal I))
    at hcom
  rw [Ideal.mk_ker] at hcom
  exact (sup_le_sup_right (show relativeSquareIdeal A ≤ (relativeSquareIdeal A).closure from
    subset_closure) _) hcom

variable [IsNoetherianRing O]

/-- Finite continuous relative tangents give actual finite maximal-ideal generators. -/
theorem maximalIdeal_fg_of_finite_continuousTangent : (maximalIdeal A).FG :=
  maximalIdeal_fg_of_open_le_closure A (coefficientMaximalIdeal A)
    ((maximalIdeal O).fg_of_isNoetherianRing.map (algebraMap O A))
    (coefficientMaximalIdeal_le A) (tangentOpenIdeal A)
    (tangentOpenIdeal_le_relativeSquare_closure A)

/-- The given topology is the maximal-ideal-adic topology. -/
theorem isAdicTopology_of_finite_continuousTangent : IsAdicTopology A :=
  isAdicTopology_of_maximalIdeal_fg A (maximalIdeal_fg_of_finite_continuousTangent A)

/-- The original ring is complete for its actual maximal ideal. -/
theorem isAdicComplete_of_finite_continuousTangent : IsAdicComplete (maximalIdeal A) A :=
  isAdicComplete_of_maximalIdeal_fg A (maximalIdeal_fg_of_finite_continuousTangent A)

end Deformation.ProartinianCat
