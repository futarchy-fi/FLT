/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.IntegralCartierConstantPoints
public import FLT.GaloisRepresentation.HardlyRamified.FiniteCharacterMaps
public import FLT.GaloisRepresentation.HardlyRamified.TrivialPrimeFiltrationCoextension

/-!
# The full dual point filtration of an integral cube-root filtration

Contravariant character exactness reverses each given geometric point
sequence. Prepending the constant-three kernel constructs a trivial-three
filtration of the entire character module and of the actual integral dual's
points. This does not assert étaleness or exactness of the dual integral models.
-/

@[expose] public noncomputable section

namespace ThreeAdicPlan

open FiniteContinuousGaloisModule

local notation "Γ" => AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ

/-- An integral cube-root filtration induces a trivial-three filtration on
all geometric characters, in the reversed filtration order. -/
theorem HasFiltration.characterDualTrivialThreePoints {H : FiniteFlatObject ZInvTwo}
    (hF : HasFiltration H muThree) :
    Nonempty (TrivialPrimeFiltration 3 Γ H.points.characterDual) := by
  generalize hQ : muThree = Q at hF
  induction hF with
  | @zero H Q e =>
    let := HasFiniteFlatModel.subsingleton_of_coordinateEquiv _ e
    let : Subsingleton H.points.characterDual := inferInstance
    exact ⟨TrivialPrimeFiltration.ofTrivial (fun _ ↦ Subsingleton.elim _ _)
      (fun _ _ ↦ Subsingleton.elim _ _)⟩
  | single Q =>
    subst Q
    exact ⟨TrivialPrimeFiltration.ofTrivial muThree_characterDual_nsmul
      muThree_characterDual_smul⟩
  | @extension A H Q E hA ih =>
    subst Q
    obtain ⟨F⟩ := ih rfl
    exact ⟨F.coextension (characterMap (FiniteFlatObject.pointMap E.quotient))
      (characterMap (FiniteFlatObject.pointMap E.inclusion))
      (characterMap_exact _ _ E.pointsSurjective E.pointsExact)
      muThree_characterDual_nsmul muThree_characterDual_smul⟩

/-- The actual integral Cartier dual's full point group inherits the
trivial-three filtration of geometric characters. -/
theorem HasFiltration.cartierDualTrivialThreePoints {H : FiniteFlatObject ZInvTwo}
    (hF : HasFiltration H muThree) :
    Nonempty (TrivialPrimeFiltration 3 Γ H.cartierDual.points) := by
  obtain ⟨F⟩ := hF.characterDualTrivialThreePoints
  exact ⟨F.comap H.cartierDualPoints H.cartierDualPoints_bijective.1⟩

/-- The complete Galois action image on the dual points is a three-group. -/
theorem HasFiltration.cartierDual_isPGroup {H : FiniteFlatObject ZInvTwo}
    (hF : HasFiltration H muThree) :
    IsPGroup 3 (MulAction.toPermHom Γ H.cartierDual.points).range := by
  obtain ⟨F⟩ := hF.cartierDualTrivialThreePoints
  exact F.isPGroup_range

end ThreeAdicPlan
