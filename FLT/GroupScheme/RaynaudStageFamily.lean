/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudCommonStage
public import FLT.GroupScheme.RaynaudDirectedHenselian

/-!
# The directed family of embedded unramified stages

All finite unramified DVR subalgebras preserving a fixed base uniformizer
form a nonempty directed family. Its actual union is a Henselian DVR.
-/

@[expose] public noncomputable section

open IsLocalRing Polynomial

namespace RaynaudParameters

variable {R Ω : Type*} [CommRing R] [Field Ω] [Algebra R Ω]

/-- Embedded finite unramified DVR stages with the specified uniformizer. -/
def UnramifiedStage (π : R) :=
  {S : Subalgebra R Ω // IsDiscreteValuationRing S ∧ Module.Finite R S ∧
    Algebra.FormallyUnramified R S ∧ Irreducible (algebraMap R S π)}

namespace UnramifiedStage

variable {π : R}

instance dvr (S : UnramifiedStage (Ω := Ω) π) : IsDiscreteValuationRing S.1 := S.2.1
instance finite (S : UnramifiedStage (Ω := Ω) π) : Module.Finite R S.1 := S.2.2.1
instance unramified (S : UnramifiedStage (Ω := Ω) π) :
    Algebra.FormallyUnramified R S.1 := S.2.2.2.1

/-- The base uniformizer is a uniformizer in every stage. -/
theorem uniformizer (S : UnramifiedStage (Ω := Ω) π) :
    Irreducible (algebraMap R S.1 π) := S.2.2.2.2

/-- Stage inclusions are local because they preserve the common uniformizer. -/
instance local_inclusion (S T : UnramifiedStage (Ω := Ω) π) (hST : S.1 ≤ T.1) :
    IsLocalHom (Subalgebra.inclusion hST).toRingHom := by
  apply ((local_hom_TFAE _).out 3 1).mp
  rw [S.uniformizer.maximalIdeal_eq, T.uniformizer.maximalIdeal_eq,
    Ideal.map_span, Set.image_singleton]
  exact le_of_eq (congrArg (fun x ↦ Ideal.span {x}) ((Subalgebra.inclusion hST).commutes π))

variable [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
  [FaithfulSMul R Ω]

/-- The degree-one root stage supplies an actual member of the family. -/
theorem nonempty (hπ : Irreducible π) : Nonempty (UnramifiedStage (Ω := Ω) π) := by
  obtain ⟨hD, hF, hL, hU, hπS⟩ := adjoin_prescribed_root_unramified hπ
    (P := X) monic_X (by simpa using (separable_X : (X : (ResidueField R)[X]).Separable))
    (0 : Ω) (by simp)
  exact ⟨⟨Algebra.adjoin R {(0 : Ω)}, hD, hF, hU, hπS⟩⟩

/-- Common embedded stages make the family directed. -/
theorem directed : Directed (· ≤ ·) (fun S : UnramifiedStage (Ω := Ω) π ↦ S.1) := by
  intro S T
  obtain ⟨U, hD, hF, hU, hSU, hTU, hπU⟩ :=
    exists_common_unramified_stage S.1 T.1 S.uniformizer
  exact ⟨⟨U, hD, hF, hU, hπU⟩, hSU, hTU⟩

instance henselian (S : UnramifiedStage (Ω := Ω) π) : HenselianLocalRing S.1 :=
  HenselianLocalRing.of_finite (R := R)

end UnramifiedStage

/-- The union is taken inside the originally specified closure. -/
def unramifiedUnion (π : R) : Subalgebra R Ω :=
  ⨆ S : UnramifiedStage (Ω := Ω) π, S.1

variable [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
  [FaithfulSMul R Ω] {π : R}

/-- The constructed union is a DVR with its original uniformizer. -/
theorem unramifiedUnion_dvr (hπ : Irreducible π) :
    IsDiscreteValuationRing (unramifiedUnion (Ω := Ω) π) := by
  let := UnramifiedStage.nonempty (Ω := Ω) hπ
  exact isDiscreteValuationRing_iSup _ UnramifiedStage.directed π UnramifiedStage.uniformizer

/-- The constructed union is Henselian. -/
theorem unramifiedUnion_henselian (hπ : Irreducible π) :
    HenselianLocalRing (unramifiedUnion (Ω := Ω) π) := by
  let := UnramifiedStage.nonempty (Ω := Ω) hπ
  exact henselianLocalRing_iSup _ UnramifiedStage.directed π UnramifiedStage.uniformizer

/-- The stage maps into the constructed union are local. -/
theorem unramifiedUnion_local_inclusion (hπ : Irreducible π)
    (S : UnramifiedStage (Ω := Ω) π) :
    IsLocalHom (Subalgebra.inclusion (le_iSup (fun S : UnramifiedStage (Ω := Ω) π ↦ S.1) S)) := by
  let := UnramifiedStage.nonempty (Ω := Ω) hπ
  exact isLocalHom_inclusion_iSup _ UnramifiedStage.directed π UnramifiedStage.uniformizer S

end RaynaudParameters
