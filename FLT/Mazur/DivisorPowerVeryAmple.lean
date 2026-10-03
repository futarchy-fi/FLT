/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DivisorLineBundlePower
public import FLT.Mazur.RelativeVeryAmpleLineBundle

/-!
# Very ample presentations for powers of divisor sheaves

The existing relative very-ampleness predicate is invariant under coefficient
isomorphisms. Thus presenting O(nD) presents the actual tensor power of O(D).
The final criterion still requires an immersion and its hyperplane coefficient
isomorphism; it does not construct either from the divisor support.
-/

open CategoryTheory AlgebraicGeometry
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.ProjectiveSpace
open FCurve FCurve.ModuleLineBundleTensorPullback
variable {X Y : Scheme} {f : X ⟶ Y} {L M : X.Modules}

/-- Transport all affine-open presentations along a coefficient isomorphism. -/
lemma RelativeVeryAmple.of_iso (h : RelativeVeryAmple f L) (e : M ≅ L) :
    RelativeVeryAmple f M := by
  intro U hU
  exact ⟨(h U hU).some.ofIso ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι).mapIso e)⟩

/-- Isomorphic module sheaves have the same relative very-ampleness predicate. -/
lemma relativeVeryAmple_iff_of_iso (e : L ≅ M) :
    RelativeVeryAmple f L ↔ RelativeVeryAmple f M :=
  ⟨fun h ↦ h.of_iso e.symm, fun h ↦ h.of_iso e⟩

/-- Presenting O(nD) is equivalent to presenting the n-fold tensor power of O(D). -/
lemma relativeVeryAmple_divisorPower_iff (I : X.IdealSheafData)
    (hI : EffectiveCartier I) (n : ℕ) :
    RelativeVeryAmple f (tensorPower (divisorLineBundle I hI) n) ↔
      RelativeVeryAmple f (divisorLineBundle (I ^ n) (hI.pow n)) :=
  relativeVeryAmple_iff_of_iso (divisorLineBundlePowerIso hI n)

/-- The positive-power existence targets agree without changing the ampleness predicate. -/
lemma exists_relativeVeryAmple_divisorPower_iff (I : X.IdealSheafData)
    (hI : EffectiveCartier I) :
    (∃ n > 0, RelativeVeryAmple f (tensorPower (divisorLineBundle I hI) n)) ↔
      ∃ n > 0, RelativeVeryAmple f (divisorLineBundle (I ^ n) (hI.pow n)) := by
  simp_rw [relativeVeryAmple_divisorPower_iff]

/-- An actual projective immersion with O(nD) coefficients presents the tensor power. -/
lemma relativeVeryAmple_divisorPower_of_embedding {A : Type} [CommRing A]
    [IsProper f] (q : Y ⟶ Spec (.of A)) (I : X.IdealSheafData)
    (hI : EffectiveCartier I) (n d : ℕ) (i : X ⟶ space A (Fin (d + 1)))
    [IsImmersion i] (hi : i ≫ baseProjection A _ = f ≫ q)
    (e : divisorLineBundle (I ^ n) (hI.pow n) ≅
      (Scheme.Modules.pullback i).obj (O A d 1)) :
    RelativeVeryAmple f (tensorPower (divisorLineBundle I hI) n) :=
  (relativeVeryAmple_pullbackOOne f q i hi).of_iso (divisorLineBundlePowerIso hI n ≪≫ e)

end FLT.Mazur.ProjectiveSpace
