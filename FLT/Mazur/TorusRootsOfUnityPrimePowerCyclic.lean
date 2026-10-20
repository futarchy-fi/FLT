/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RootsOfUnityPrimePowerIdeal
public import FLT.Mazur.SupportedIdealPowerComparison
public import FLT.Mazur.TorusRootsOfUnityCartier
public import FLT.Mazur.GeneralizedCurveCyclicSubgroup

/-!
# Cartier cyclicity of prime-power toric subgroups in characteristic p

The identity section is a Cartier generator: its coincident powers recover
the entire subgroup divisor on the whole generalized curve. Thus these
nonetale subgroups are cyclic in the actual fppf-local sense.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonObj MonoidalCategory

namespace FLT.Mazur.GeneralizedEllipticCurve

variable {R : Type} [CommRing R] (E : GeneralizedEllipticCurve (Spec (.of R)))
  (e : MultiplicativeGroupScheme.gm R ≅ E.group) [IsMonHom e.hom]
  (p : ℕ) [Fact p.Prime] [CharP R p]

/-- The torus identity is the original identity section of the entire curve. -/
theorem torusIdentity_curveMap :
    η[MultiplicativeGroupScheme.gm R].left ≫ e.hom.left ≫ E.inclusion.left =
      E.identitySection.left := by
  change (η[MultiplicativeGroupScheme.gm R] ≫ e.hom ≫ E.inclusion).left = _
  rw [← Category.assoc, IsMonHom.one_hom]
  rfl

/-- The full prime-power subgroup ideal equals the power of the whole-curve identity ideal. -/
theorem torusRootsOfUnitySubgroup_primePower_ideal (r : ℕ) :
    (E.torusRootsOfUnitySubgroup e (p ^ r)).ideal = E.identitySection.left.ker ^ p ^ r := by
  let j := e.hom.left ≫ E.inclusion.left
  let i := η[MultiplicativeGroupScheme.gm R].left
  let _ : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget _).map e.hom))
  let _ : IsOpenImmersion j := inferInstanceAs (IsOpenImmersion (e.hom.left ≫ E.inclusion.left))
  have hi : i ≫ j = E.identitySection.left := E.torusIdentity_curveMap e
  let _ : IsProper E.curve.hom := E.family.family.1
  let _ : IsClosedImmersion (i ≫ j) := by
    rw [hi]
    exact FCurve.isClosedImmersion_section E.curve.hom E.identitySection.left E.identitySection.w
  rw [← hi]
  refine OpenIdealCover.eq_ker_comp_power j _ ?_ i (p ^ r) (NeZero.ne (p ^ r)) ?_
  · rw [Scheme.IdealSheafData.range_subschemeι, FiniteSubgroup.ideal,
      Scheme.Hom.support_ker]
    have hc :=
      (E.torusRootsOfUnitySubgroup e (p ^ r)).curveMap.left.isClosedEmbedding.isClosed_range
    rw [hc.closure_eq]
    rintro _ ⟨z, rfl⟩
    exact ⟨(RootsOfUnityScheme.inclusion R (p ^ r)).left z, rfl⟩
  · rw [torusRootsOfUnitySubgroup_ideal_on_torus, RootsOfUnityPrimePowerIdeal.ideal]

/-- The subgroup identity maps to the original curve identity. -/
theorem torusRootsOfUnitySubgroup_one_curveMap (n : ℕ) [NeZero n] :
    (1 : 𝟙_ (Over (Spec (.of R))) ⟶ (E.torusRootsOfUnitySubgroup e n).carrier) ≫
      (E.torusRootsOfUnitySubgroup e n).curveMap = E.identitySection := by
  rw [FiniteSubgroup.curveMap, ← Category.assoc, one_comp]
  rfl

/-- Coincident identity powers supply a Cartier generator with all multiplicities. -/
theorem torusRootsOfUnitySubgroup_primePower_generator (r : ℕ) :
    (E.torusRootsOfUnitySubgroup e (p ^ r)).IsCartierGenerator 1 := by
  refine ⟨one_pow _, E.torusRootsOfUnitySubgroup_relativeCartier e _, ?_⟩
  simp only [one_pow, torusRootsOfUnitySubgroup_one_curveMap, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]
  exact E.torusRootsOfUnitySubgroup_primePower_ideal e p r

/-- The actual characteristic-p prime-power subgroup is fppf locally cyclic. -/
theorem torusRootsOfUnitySubgroup_primePower_isCyclic (r : ℕ) :
    (E.torusRootsOfUnitySubgroup e (p ^ r)).IsCyclic :=
  (E.torusRootsOfUnitySubgroup_primePower_generator e p r).isCyclic _

end FLT.Mazur.GeneralizedEllipticCurve
