/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.GroupScheme.ConstantFiniteFlat
public import FLT.GroupScheme.DiagonalizableFiniteFlat
public import FLT.GroupScheme.FiniteFlatFiltration
public import FLT.GroupScheme.RaynaudSplitting

/-!
# The reverse extension hypothesis and swapping split factors

The global reverse Ext assertion is an explicit proposition about integral
extensions over `ℤ[1/2]`. It is an explicit hypothesis. A splitting supplies integral
maps in the opposite order, and these maps form an exact sequence on points.
The faithfully-flat quotient and torsor comparison for the swapped sequence
are separate integral obligations; this file does not assert them.
-/

@[expose] public noncomputable section

namespace ThreeAdicPlan

variable {R : Type} [CommRing R] [Algebra R ℚ]

/-- Integral composition induces composition on the chosen geometric point groups. -/
theorem FiniteFlatObject.pointMap_comp {A H Q : FiniteFlatObject R}
    (i : A.Hom H) (q : H.Hom Q) (a : A.points) :
    FiniteFlatObject.pointMap (i.comp q) a =
      FiniteFlatObject.pointMap q (FiniteFlatObject.pointMap i a) :=
  genericHom_comp (X := A.toFF) (Y := H.toFF) (Z := Q.toFF) i q a

/-- An integral splitting of the specified maps of a finite-flat extension. -/
abbrev FiniteFlatExtension.Splitting [IsFractionRing R ℚ] {A H Q : FiniteFlatObject R}
    (E : FiniteFlatExtension A H Q) :=
  ModelSplitting (S := A.toFF) (X := H.toFF) (Q := Q.toFF) E.inclusion E.quotient

/-- Hypothesis: every integral extension `0 → ℤ/3 → H → μ₃ → 0` over
`ℤ[1/2]` splits. This is the global reverse Ext input to R12, not an assumed constant
or a consequence of the local three-adic splitting theorem. -/
def ReverseExtVanishing : Prop :=
  ∀ (H : FiniteFlatObject ZInvTwo)
    (E : FiniteFlatExtension constantThree H muThree), Nonempty E.Splitting

/-- Interchange the two summands of a split generic sequence. -/
def GenericSplitSequence.swap {K : Type} [Field K] [Algebra R K]
    {S X Q : FF R K} (E : GenericSplitSequence S X Q) : GenericSplitSequence Q X S where
  inclusion := E.sectionMap
  retraction := E.projection
  projection := E.retraction
  sectionMap := E.inclusion
  retract := E.sectionProjection
  sectionProjection := E.retract
  decomposition x := (add_comm _ _).trans (E.decomposition x)

/-- The integral section and retraction of a splitting give a short exact
sequence of geometric points in the opposite order. -/
theorem ModelSplitting.swappedPointsExact [IsFractionRing R ℚ]
    {A H Q : FiniteFlatObject R} {i : A.Hom H} {q : H.Hom Q}
    (s : ModelSplitting (S := A.toFF) (X := H.toFF) (Q := Q.toFF) i q) :
    Function.Injective (FiniteFlatObject.pointMap s.sectionMap) ∧
      Function.Surjective (FiniteFlatObject.pointMap s.retraction) ∧
      ∀ h : H.points, FiniteFlatObject.pointMap s.retraction h = 0 ↔
        ∃ a : Q.points, FiniteFlatObject.pointMap s.sectionMap a = h := by
  let T := s.toGenericSplitSequence.swap
  exact ⟨T.inclusion_injective, T.projection_surjective, T.exact⟩

/-- The swapped inclusion and projection compose to zero on integral coordinate rings. -/
theorem ModelSplitting.swappedCompositionZero [IsFractionRing R ℚ]
    {A H Q : FiniteFlatObject R} {i : A.Hom H} {q : H.Hom Q}
    (s : ModelSplitting (S := A.toFF) (X := H.toFF) (Q := Q.toFF) i q) :
    s.sectionMap.comp s.retraction = ModelHom.zero Q.toFF A.toFF := by
  apply genericHom_injective Q.toFF A.toFF
  ext x
  rw [genericHom_comp, ModelHom.genericHom_zero]
  exact s.toGenericSplitSequence.swap.projection_inclusion x

/-- Under reverse Ext vanishing, a reversed pair admits integral maps in the
desired order `μ₃ → H → ℤ/3`, exact on points and with zero integral composite. -/
theorem ReverseExtVanishing.existsSwappedMaps (hExt : ReverseExtVanishing)
    {H : FiniteFlatObject ZInvTwo} (E : FiniteFlatExtension constantThree H muThree) :
    ∃ (i : muThree.Hom H) (q : H.Hom constantThree),
      i.comp q = ModelHom.zero muThree.toFF constantThree.toFF ∧
      Function.Injective (FiniteFlatObject.pointMap i) ∧
      Function.Surjective (FiniteFlatObject.pointMap q) ∧
      ∀ h : H.points, FiniteFlatObject.pointMap q h = 0 ↔
        ∃ a : muThree.points, FiniteFlatObject.pointMap i a = h := by
  obtain ⟨s⟩ := hExt H E
  exact ⟨s.sectionMap, s.retraction, s.swappedCompositionZero, s.swappedPointsExact⟩

/-- An annihilator of the middle point group also kills its subobject. -/
theorem FiniteFlatExtension.killedByLeft {A H Q : FiniteFlatObject R}
    (E : FiniteFlatExtension A H Q) {n : ℕ} (hH : KilledByQ n H) : KilledByQ n A := by
  intro a
  apply E.pointsInjective
  rw [map_nsmul, map_zero, hH]

/-- An annihilator of the middle point group also kills its quotient. -/
theorem FiniteFlatExtension.killedByRight {A H Q : FiniteFlatObject R}
    (E : FiniteFlatExtension A H Q) {n : ℕ} (hH : KilledByQ n H) : KilledByQ n Q := by
  intro q
  obtain ⟨h, rfl⟩ := E.pointsSurjective q
  rw [← map_nsmul, hH, map_zero]

end ThreeAdicPlan
