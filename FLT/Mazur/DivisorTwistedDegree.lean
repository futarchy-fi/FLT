/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DivisorTwistedSequence
public import FLT.Mazur.FiniteSchemeLineCohomology
public import FLT.Mazur.FiniteDivisorCohomology
public import FLT.Mazur.CartierTensorRank

/-!
# Euler characteristic after an effective divisor twist

For a proper scheme over a field and a finite effective Cartier divisor D,
tensoring any line sheaf by O(D) increases its curve Euler characteristic by
the length of D. The quotient is computed from the actual twisted sequence.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace FLT.Mazur.FCurve

open ModuleSheafTensor

variable {k : Type} [Field k] {X : Scheme}
  (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
  {I : X.IdealSheafData} (hI : EffectiveCartier I) [IsFinite (I.subschemeι ≫ f)]
  {L : X.Modules} (hL : LocallyFreeRankOne L)

include hL in
/-- The twisted quotient has no positive-degree cohomology. -/
theorem divisorTwistedQuotient_cohomology_subsingleton (n : ℕ) (hn : 0 < n) :
    Subsingleton (ModuleScalarH f (divisorTwistedComplex hI L).X₃ n) := by
  have : Subsingleton (ModuleScalarH f
      ((pushforward I.subschemeι).obj ((Scheme.Modules.pullback I.subschemeι).obj
        (tensor (divisorLineBundle I hI) L))) n) :=
    finiteClosed_line_cohomology_subsingleton I.subschemeι f
    ((hI.divisorLineBundle_locallyFreeRankOne.tensor hL).pullback I.subschemeι) n hn
  let e : ModuleScalarH f (divisorTwistedComplex hI L).X₃ n ≃ₗ[k]
      ModuleScalarH f ((pushforward I.subschemeι).obj
        ((Scheme.Modules.pullback I.subschemeι).obj
          (tensor (divisorLineBundle I hI) L))) n :=
    ((moduleScalarHFunctor f n).mapIso (divisorTwistedQuotientIso hI L hL)).toLinearEquiv
  exact e.injective.subsingleton

include hL in
/-- The canonical divisor transition is surjective on every positive cohomology group. -/
theorem divisorTwisted_transition_cohomology_surjective (n : ℕ) (hn : 0 < n) :
    Function.Surjective (moduleScalarHMap f (divisorTwistedComplex hI L).f n) := by
  let S := divisorTwistedComplex hI L
  have : Subsingleton (ModuleScalarH f S.X₃ n) :=
    divisorTwistedQuotient_cohomology_subsingleton f hI hL n hn
  intro y
  exact (moduleScalarH_exact₂ S
    (moduleAbelianComplex_shortExact (divisorTwistedComplex_shortExact hI L hL)) f n y).mp
      (Subsingleton.elim _ _)

include hL in
/-- The H⁰ dimension of the twisted quotient is independent of the line coefficient. -/
theorem divisorTwistedQuotient_h0_finrank :
    Module.finrank k (ModuleScalarH f (divisorTwistedComplex hI L).X₃ 0) =
      divisorFieldLength f I := by
  exact ((moduleScalarHFunctor f 0).mapIso
    (divisorTwistedQuotientIso hI L hL)).toLinearEquiv.finrank_eq.trans
      (finiteClosed_line_h0_finrank I.subschemeι f
        ((hI.divisorLineBundle_locallyFreeRankOne.tensor hL).pullback I.subschemeι))

include hL in
/-- The effective-divisor twist increases Euler characteristic by the finite divisor length. -/
theorem curveEulerCharacteristic_divisor_tensor :
    curveEulerCharacteristic f (tensor (divisorLineBundle I hI) L) =
      curveEulerCharacteristic f L + (divisorFieldLength f I : ℤ) := by
  have := Chow.source_isNoetherian f
  let S := divisorTwistedComplex hI L
  have h₁ := (structureModule_locallyFreeRankOne.tensor hL).isFinitePresentation
  have h₂ := (hI.divisorLineBundle_locallyFreeRankOne.tensor hL).isFinitePresentation
  have h₃ := ((hI.divisorLineBundle_locallyFreeRankOne.tensor hL).pullback
    I.subschemeι).isFinitePresentation
  have hclosed := CoherentDevissage.closedPushforward_isFinitePresentation I.subschemeι
    ((Scheme.Modules.pullback I.subschemeι).obj (tensor (divisorLineBundle I hI) L))
  have hfinite := proper_coherent_hasFiniteCohomology f
    ((pushforward I.subschemeι).obj
      ((Scheme.Modules.pullback I.subschemeι).obj (tensor (divisorLineBundle I hI) L)))
  have : Module.Finite k (ModuleScalarH f S.X₃ 0) := by
    have : Module.Finite k (ModuleScalarH f
        ((pushforward I.subschemeι).obj ((Scheme.Modules.pullback I.subschemeι).obj
          (tensor (divisorLineBundle I hI) L))) 0) := hfinite 0
    let e : ModuleScalarH f S.X₃ 0 ≃ₗ[k]
        ModuleScalarH f ((pushforward I.subschemeι).obj
          ((Scheme.Modules.pullback I.subschemeι).obj
            (tensor (divisorLineBundle I hI) L))) 0 :=
      ((moduleScalarHFunctor f 0).mapIso (divisorTwistedQuotientIso hI L hL)).toLinearEquiv
    exact Module.Finite.equiv e.symm
  have : Module.Finite k (ModuleScalarH f S.X₁ 0) :=
    proper_coherent_hasFiniteCohomology f (tensor (structureModule X) L) 0
  have : Module.Finite k (ModuleScalarH f S.X₁ 1) :=
    proper_coherent_hasFiniteCohomology f (tensor (structureModule X) L) 1
  have : Module.Finite k (ModuleScalarH f S.X₂ 0) :=
    proper_coherent_hasFiniteCohomology f (tensor (divisorLineBundle I hI) L) 0
  have : Module.Finite k (ModuleScalarH f S.X₂ 1) :=
    proper_coherent_hasFiniteCohomology f (tensor (divisorLineBundle I hI) L) 1
  have : Subsingleton (ModuleScalarH f S.X₃ 1) :=
    divisorTwistedQuotient_cohomology_subsingleton f hI hL 1 (by decide)
  have hadd := curveEulerCharacteristic_add_of_surjective f S
    (divisorTwistedComplex_shortExact hI L hL) (fun y ↦ ⟨0, Subsingleton.elim _ _⟩)
  change curveEulerCharacteristic f (tensor (divisorLineBundle I hI) L) =
    curveEulerCharacteristic f (tensor (structureModule X) L) +
      curveEulerCharacteristic f S.X₃ at hadd
  have hu : curveEulerCharacteristic f (tensor (structureModule X) L) =
      curveEulerCharacteristic f L := curveEulerCharacteristic_iso f (leftUnitor L)
  rw [hu] at hadd
  have hq : curveEulerCharacteristic f S.X₃ = (divisorFieldLength f I : ℤ) := by
    unfold curveEulerCharacteristic
    rw [Module.finrank_zero_of_subsingleton (M := ModuleScalarH f S.X₃ 1),
      Nat.cast_zero, sub_zero]
    exact congrArg (fun n : ℕ ↦ (n : ℤ)) (divisorTwistedQuotient_h0_finrank f hI hL)
  rwa [hq] at hadd

include hL in
/-- Cohomological degree is additive when one factor is the finite effective divisor line. -/
theorem curveSheafDegree_divisor_tensor :
    curveSheafDegree f (tensor (divisorLineBundle I hI) L) =
      (divisorFieldLength f I : ℤ) + curveSheafDegree f L := by
  unfold curveSheafDegree
  rw [curveEulerCharacteristic_divisor_tensor f hI hL]
  omega

end FLT.Mazur.FCurve
