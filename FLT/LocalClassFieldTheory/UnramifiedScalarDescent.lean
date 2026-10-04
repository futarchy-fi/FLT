/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.UnramifiedParameterInvariant
public import FLT.GaloisRepresentation.Extensions.PeuRamifiedClass

/-!
# Scalar characters and the actual unramified quotient

Continuous scalar characters vanishing on the restriction kernel descend
continuously. This identifies the characters used by the independent
peu-ramification predicate with characters of the constructed quotient.
-/

@[expose] public noncomputable section

namespace LocalClassFieldTheory

open IsLocalRing GaloisRepresentation.Extensions

attribute [local instance] relativeBaseTower unramifiedUnionGalois fieldUnitAction
  unramifiedFieldUnitTopology unramifiedFieldUnitDiscrete
  separableClosureGalois separableClosureUnitTopology separableClosureUnitDiscrete

variable (R K C : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [Field C] [Algebra K C] [Algebra R C] [IsScalarTower R K C]
  [Algebra.IsSeparable K C] [Finite (ResidueField R)] [IsSepClosed C]
  [IsAdicComplete (maximalIdeal R) R]
  {q : ℕ} [Fact q.Prime]

local notation "U" => maximalUnramified R K C
local notation "I" => MonoidHom.ker (unramifiedRestriction R K C)

/-- Inflated scalar characters vanish on the actual unramified restriction kernel. -/
theorem inflatedUnramifiedScalarCharacter_unramified
    (χ : ContinuousScalarCharacter Gal(U/K) (ZMod q)) :
    IsUnramifiedAddCharacter I (inflatedUnramifiedScalarCharacter R K C χ) := by
  intro g hg
  have h0 : χ.val 1 = 0 := congrArg Multiplicative.toAdd (map_one (scalarCharacterHom χ))
  change χ.val (unramifiedRestriction R K C g) = 0
  rw [show unramifiedRestriction R K C g = 1 from hg, h0]

/-- Every inertia-trivial scalar character descends, with continuity proved by the quotient map. -/
theorem exists_unramifiedScalar_descent (χ : ContinuousScalarCharacter Gal(C/K) (ZMod q))
    (hχ : IsUnramifiedAddCharacter I χ) :
    ∃ ψ : ContinuousScalarCharacter Gal(U/K) (ZMod q),
      inflatedUnramifiedScalarCharacter R K C ψ = χ := by
  let r := unramifiedRestriction R K C
  have hr := unramifiedRestriction_surjective R K C
  let f := scalarCharacterHom χ
  have hk : r.ker ≤ f.toMonoidHom.ker := fun g hg => hχ g hg
  let d := r.liftOfSurjective hr ⟨f.toMonoidHom, hk⟩
  have hd (g : Gal(C/K)) : d (r g) = f g :=
    MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ g
  let : T2Space Gal(U/K) := krullTopology_t2
  have hq : Topology.IsQuotientMap r := .of_surjective_continuous hr
    (unramifiedRestriction_continuous R K C)
  have hc : Continuous d := hq.continuous_iff.mpr (by
    convert f.continuous using 1
    exact funext hd)
  let ψ : ContinuousScalarCharacter Gal(U/K) (ZMod q) :=
    ⟨⟨fun g => (d g).toAdd, hc⟩, fun g h => congrArg Multiplicative.toAdd (map_mul d g h)⟩
  refine ⟨ψ, ?_⟩
  apply Subtype.ext
  apply ContinuousMap.ext
  intro g
  exact congrArg Multiplicative.toAdd (hd g)

end LocalClassFieldTheory
