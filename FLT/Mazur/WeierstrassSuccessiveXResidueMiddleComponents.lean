/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveXResidueMiddle
public import FLT.Mazur.WeierstrassSuccessiveXMiddleComponents

/-!
# The conic and ordered lines inside the actual tensor residue fiber

Transport the constructed closed components along the full tensor algebra
comparison. The middle coefficient and all original generators are retained.
-/

@[expose] public noncomputable section
open IsLocalRing AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassSuccessiveX
open WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {n : ℕ} (D : SplitNodeDepth W π n)
  (k : ℕ) (hk0 : 0 < k) (hk : 2 * (k + 1) ≤ n) (b3 b4 b6 : R)
  (h3 : W.a₃ = π ^ (k + 1) * b3) (h4 : W.a₄ = π ^ (k + 1) * b4)
local notation "K" => ResidueField R
local notation "W₀" => W.map (residue R)
local notation "c" => residue R b6
local notation "T" => ScalarExtension W (π ^ k) π b3 b4 b6 K
local notation "e" => residueRetainedFiberEquiv D k hk0 hk b3 b4 b6 h3 h4

/-- The full middle-normal-form scheme is the actual tensor residue fiber. -/
def residueRetainedIso : Spec (.of (Coordinate W₀ 0 0 0 0 c)) ≅ Spec (.of T) :=
  Scheme.Spec.mapIso (e).toRingEquiv.toCommRingCatIso.op

/-- The actual tensor fiber restricts to the conic, retaining its middle coefficient. -/
def residueSuccessiveConicMap : T →ₐ[K] ConicCoordinate (residue R W.a₁) c :=
  (middleConicMap W₀ c ((residue_eq_zero_iff _).mpr D.a₂_mem)).comp (e).toAlgHom

/-- The conic restriction retains t and v and kills the retained horizontal coordinate. -/
@[simp] theorem residueSuccessiveConicMap_coord (i : Fin 3) :
    residueSuccessiveConicMap D k hk0 hk b3 b4 b6 h3 h4
      (tensorCoord W (π ^ k) π b3 b4 b6 K i) =
        ![conicT (residue R W.a₁) c, conicV (residue R W.a₁) c, 0] i := by
  change middleConicMap W₀ c ((residue_eq_zero_iff _).mpr D.a₂_mem)
    (e (tensorCoord W (π ^ k) π b3 b4 b6 K i)) = _
  rw [residueRetainedFiberEquiv_coord, middleConicMap_coord]
  rfl

/-- Every actual conic function comes from the tensor fiber. -/
theorem residueSuccessiveConicMap_surjective :
    Function.Surjective (residueSuccessiveConicMap D k hk0 hk b3 b4 b6 h3 h4) :=
  (middleConicMap_surjective W₀ c ((residue_eq_zero_iff _).mpr D.a₂_mem)).comp (e).surjective

/-- The conic is a closed subscheme of the actual tensor fiber. -/
def residueSuccessiveConicImmersion : Spec (.of (ConicCoordinate (residue R W.a₁) c)) ⟶
    Spec (.of T) :=
  middleConicImmersion W₀ c ((residue_eq_zero_iff _).mpr D.a₂_mem) ≫
    (residueRetainedIso D k hk0 hk b3 b4 b6 h3 h4).hom

instance residueSuccessiveConicImmersion_isClosedImmersion :
    IsClosedImmersion (residueSuccessiveConicImmersion D k hk0 hk b3 b4 b6 h3 h4) :=
  inferInstanceAs (IsClosedImmersion (_ ≫ _))

/-- Each original tangent root gives a closed horizontal line in the actual tensor fiber. -/
def residueSuccessiveLineImmersion (r : K) (hr : r * (r + residue R W.a₁) = 0) :
    Spec (.of (Polynomial K)) ⟶ Spec (.of T) :=
  middleLineImmersion W₀ c ((residue_eq_zero_iff _).mpr D.a₂_mem) r hr ≫
    (residueRetainedIso D k hk0 hk b3 b4 b6 h3 h4).hom

instance residueSuccessiveLineImmersion_isClosedImmersion
    (r : K) (hr : r * (r + residue R W.a₁) = 0) :
    IsClosedImmersion (residueSuccessiveLineImmersion D k hk0 hk b3 b4 b6 h3 h4 r hr) :=
  inferInstanceAs (IsClosedImmersion (_ ≫ _))

/-- The actual tensor fiber is covered by its retained conic and ordered horizontal lines. -/
theorem residue_successive_components_cover (p : Spec (.of T)) :
    p ∈ Set.range (residueSuccessiveConicImmersion D k hk0 hk b3 b4 b6 h3 h4) ∨
    p ∈ Set.range (residueSuccessiveLineImmersion D k hk0 hk b3 b4 b6 h3 h4
      0 (middle_first_root W₀)) ∨
    p ∈ Set.range (residueSuccessiveLineImmersion D k hk0 hk b3 b4 b6 h3 h4
      (-residue R W.a₁) (middle_second_root W₀)) := by
  let E := residueRetainedIso D k hk0 hk b3 b4 b6 h3 h4
  have hp : E.hom (E.inv p) = p := by
    rw [← Scheme.Hom.comp_apply, E.inv_hom_id]
    rfl
  rcases middle_components_cover W₀ c ((residue_eq_zero_iff _).mpr D.a₂_mem) (E.inv p) with
     ⟨z, hz⟩ | ⟨z, hz⟩ | ⟨z, hz⟩
  · exact Or.inl ⟨z, (congrArg E.hom hz).trans hp⟩
  · exact Or.inr (Or.inl ⟨z, (congrArg E.hom hz).trans hp⟩)
  · exact Or.inr (Or.inr ⟨z, (congrArg E.hom hz).trans hp⟩)

end FLT.Mazur.WeierstrassSuccessiveX
