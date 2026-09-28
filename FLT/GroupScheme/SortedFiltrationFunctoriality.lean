/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.GaloisRepresentation.HardlyRamified.Chebotarev.FrobeniusTraces
public import FLT.GroupScheme.MultiplicativeFiltrationPurity
public import FLT.GroupScheme.ReverseExtHypothesis

/-!
# Functoriality of sorted finite-flat filtrations

For objects killed by three, the multiplicative part of a sorted integral
extension is preserved by every equivariant point endomorphism, hence by
integral endomorphisms and coefficient scalars. The proof separates the two
actions using arithmetic Frobenius at two: it acts by two on a multiplicative
filtration and by one on a constant filtration. In particular the
multiplicative point subgroup is unique whenever a sorted extension exists.

Existence of a sorted extension is not asserted here. It still requires the
integral composition-series and adjacent-swap constructions.
-/

@[expose] public noncomputable section

attribute [local instance 2000] IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
  IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion

namespace ThreeAdicPlan

local notation "Γ" => AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ

/-- A rational Galois element obtained from an arithmetic Frobenius at two. -/
def sortingFrobenius : Γ :=
  Field.absoluteGaloisGroup.map
    (algebraMap ℚ (Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat.adicCompletion ℚ))
    (Field.AbsoluteGaloisGroup.adicArithFrob
      Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat)

/-- The three-adic cyclotomic value of the chosen Frobenius is two. -/
theorem sortingFrobenius_cyclotomic :
    (cyclotomicCharacter (AlgebraicClosure ℚ) 3 sortingFrobenius.toRingEquiv).val = 2 :=
  GaloisRepresentation.B5Inputs.cyclotomicCharacter_adicArithFrob 3 2
    Nat.prime_two (by decide)

/-- Frobenius at two acts by doubling on a multiplicative filtration killed by three. -/
theorem HasFiltration.muThree_frobeniusTwo {A : FiniteFlatObject ZInvTwo}
    (hA : HasFiltration A muThree) (hkill : KilledByQ 3 A) (a : A.points) :
    sortingFrobenius • a = (2 : ℕ) • a := by
  have h := A.points.cyclotomic_nsmul_of_characterDual_trivial 3 1
    (fun w ↦ by simpa only [pow_one] using hkill w)
    (pure_one_characterDual_of_muThree_filtration A hA) sortingFrobenius a
  rw [sortingFrobenius_cyclotomic] at h
  simpa only [map_ofNat, show (2 : ZMod (3 ^ 1)).val = 2 from rfl] using h

/-- Every equivariant point map from a multiplicative filtration killed by three
to a constant filtration is zero. This concerns full actions, not just constituents. -/
theorem HasFiltration.pointHom_eq_zero {A Q : FiniteFlatObject ZInvTwo}
    (hA : HasFiltration A muThree) (hQ : HasFiltration Q constantThree)
    (hkill : KilledByQ 3 A) (f : A.points →+[Γ] Q.points) (a : A.points) : f a = 0 := by
  have hfix : sortingFrobenius • f a = f a := by
    simpa using pure_one_of_constantThree_filtration Q hQ sortingFrobenius (f a)
  have hdouble : (2 : ℕ) • f a = f a := by
    rw [← map_nsmul, ← hA.muThree_frobeniusTwo hkill a, map_smul, hfix]
  exact add_right_cancel (show f a + f a = 0 + f a by simpa [two_nsmul] using hdouble)

/-- Every integral morphism from such a multiplicative object to such a constant
object is the zero morphism on the actual coordinate Hopf algebras. -/
theorem HasFiltration.modelHom_eq_zero {A Q : FiniteFlatObject ZInvTwo}
    (hA : HasFiltration A muThree) (hQ : HasFiltration Q constantThree)
    (hkill : KilledByQ 3 A) (f : A.Hom Q) :
    f = ModelHom.zero A.toFF Q.toFF := by
  apply FiniteFlatObject.pointMap_injective A Q
  ext a
  exact (hA.pointHom_eq_zero hQ hkill (FiniteFlatObject.pointMap f) a).trans
    (ModelHom.genericHom_zero A.toFF Q.toFF a).symm

/-- A sorted integral extension has a multiplicative-filtered subobject and a
constant-filtered quotient. Every step in each filtration retains integral
exactness and the quotient torsor comparison through `HasFiltration`. -/
structure SortedFiniteFlatExtension (H : FiniteFlatObject ZInvTwo) where
  /-- The multiplicative-filtered subobject. -/
  left : FiniteFlatObject ZInvTwo
  /-- The constant-filtered quotient. -/
  right : FiniteFlatObject ZInvTwo
  /-- The integral short exact sequence with the specified middle object. -/
  extension : FiniteFlatExtension left H right
  /-- A filtration of the subobject by cube-root groups. -/
  leftFiltration : HasFiltration left muThree
  /-- A filtration of the quotient by constant groups of order three. -/
  rightFiltration : HasFiltration right constantThree

/-- The actual subgroup of middle points belonging to the multiplicative part. -/
def SortedFiniteFlatExtension.pointSubgroup {H : FiniteFlatObject ZInvTwo}
    (S : SortedFiniteFlatExtension H) : AddSubgroup H.points :=
  (FiniteFlatObject.pointMap S.extension.inclusion).toAddMonoidHom.range

/-- Every integral endomorphism of the middle model preserves the specified
subobject on points. The condition is sufficient for coefficient stability. -/
def FiniteFlatExtension.PreservedByAllEndomorphisms
    {A H Q : FiniteFlatObject ZInvTwo} (E : FiniteFlatExtension A H Q) : Prop :=
  ∀ (f : H.Hom H) (a : A.points), ∃ b : A.points,
    FiniteFlatObject.pointMap E.inclusion b =
      FiniteFlatObject.pointMap f (FiniteFlatObject.pointMap E.inclusion a)

/-- Every equivariant map between sorted middle objects preserves their
multiplicative point subgroups; no extension of the point map to models is needed. -/
theorem SortedFiniteFlatExtension.mapPreservesLeft
    {H J : FiniteFlatObject ZInvTwo} (S : SortedFiniteFlatExtension H)
    (T : SortedFiniteFlatExtension J) (hkill : KilledByQ 3 H)
    (f : H.points →+[Γ] J.points) (a : S.left.points) :
    ∃ b : T.left.points, FiniteFlatObject.pointMap T.extension.inclusion b =
      f (FiniteFlatObject.pointMap S.extension.inclusion a) := by
  apply (T.extension.pointsExact _).mp
  exact S.leftFiltration.pointHom_eq_zero T.rightFiltration
    (S.extension.killedByLeft hkill)
    ((FiniteFlatObject.pointMap T.extension.quotient).comp
      (f.comp (FiniteFlatObject.pointMap S.extension.inclusion))) a

/-- In particular, all integral endomorphisms preserve the multiplicative part. -/
theorem SortedFiniteFlatExtension.preservedByAllEndomorphisms
    {H : FiniteFlatObject ZInvTwo} (S : SortedFiniteFlatExtension H)
    (hkill : KilledByQ 3 H) : S.extension.PreservedByAllEndomorphisms :=
  fun f a ↦ S.mapPreservesLeft S hkill (FiniteFlatObject.pointMap f) a

/-- A point belonging to the multiplicative part stays there under every
equivariant map of sorted objects. -/
theorem SortedFiniteFlatExtension.map_mem_pointSubgroup
    {H J : FiniteFlatObject ZInvTwo} (S : SortedFiniteFlatExtension H)
    (T : SortedFiniteFlatExtension J) (hkill : KilledByQ 3 H)
    (f : H.points →+[Γ] J.points) {x : H.points} (hx : x ∈ S.pointSubgroup) :
    f x ∈ T.pointSubgroup := by
  obtain ⟨a, rfl⟩ := hx
  exact S.mapPreservesLeft T hkill f a

/-- Any two sorted extensions of the same object killed by three have the
same multiplicative point subgroup. -/
theorem SortedFiniteFlatExtension.pointSubgroup_unique
    {H : FiniteFlatObject ZInvTwo} (S T : SortedFiniteFlatExtension H)
    (hkill : KilledByQ 3 H) : S.pointSubgroup = T.pointSubgroup := by
  ext x
  exact ⟨fun hx ↦ S.map_mem_pointSubgroup T hkill (DistribMulActionHom.id Γ) hx,
    fun hx ↦ T.map_mem_pointSubgroup S hkill (DistribMulActionHom.id Γ) hx⟩

/-- Coefficient scalars commuting with Galois preserve the multiplicative point
subgroup, even when no integral coefficient action has been chosen. -/
theorem SortedFiniteFlatExtension.smul_mem_pointSubgroup
    {H : FiniteFlatObject ZInvTwo} (S : SortedFiniteFlatExtension H)
    (hkill : KilledByQ 3 H) {k : Type*} [Semiring k] [Module k H.points]
    [SMulCommClass Γ k H.points] (c : k) {x : H.points} (hx : x ∈ S.pointSubgroup) :
    c • x ∈ S.pointSubgroup := by
  let f : H.points →+[Γ] H.points :=
    { toFun := fun y ↦ c • y
      map_zero' := smul_zero c
      map_add' := smul_add c
      map_smul' := fun σ y ↦ (smul_comm σ c y).symm }
  exact S.map_mem_pointSubgroup S hkill f hx

end ThreeAdicPlan
