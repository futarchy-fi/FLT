/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalFanRestrictionCoordinates

/-!
# Rigidity of finite overlap restrictions

For surjective coordinates, an ambient path equation determines the entire
restriction map. This identifies separately constructed restrictions whenever
they are transported to a common target and satisfy the same ambient equation.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.FiniteTypeRelationModel

universe u v w

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
  [Algebra.FiniteType R A] {ι : Type v}
  {B : ι → Type u} [∀ i, CommRing (B i)] [∀ i, Algebra R (B i)]
  [∀ i, Algebra.FiniteType R (B i)]
  {a : ι → A} {b : ∀ i, B i}
  {f : ∀ i, Localization.Away (a i) →ₐ[R] Localization.Away (b i)}

/-- The actual localization map into the canonical double-open target. -/
def principalFanRestrictionInclusion (x : PrincipalFanStage a b f) (i j : ι) :
    PrincipalStage R (B j) (b j) (x.target j) →ₐ[R] PrincipalFanRestrictionTarget x i j :=
  Algebra.algHom R _ _

/-- Full ambient equations determine restrictions out of a surjective chart coordinate. -/
theorem principalFan_restriction_ext (x : PrincipalFanStage a b f) (i : ι)
    (hx : Function.Surjective (x.hom i)) {D : Type w} [CommRing D] [Algebra R D]
    (g h : PrincipalStage R (B i) (b i) (x.target i) →ₐ[R] D)
    (he : g.comp (principalFanAmbient x i) = h.comp (principalFanAmbient x i)) : g = h := by
  apply (AlgHom.cancel_right hx).mp
  apply IsLocalization.algHom_ext (Submonoid.powers
    (Ideal.Quotient.mk (FiniteRelationModel.relations (relationIdeal R A) x.source)
      (principalRepresentative R A (a i))))
  simpa only [principalFanAmbient, AlgHom.comp_assoc] using he

/-- Restrictions transported to a common target agree once their ambient maps agree. -/
theorem principalFan_restriction_transport (x : PrincipalFanStage a b f) (i : ι)
    (hx : Function.Surjective (x.hom i))
    {D E F : Type w} [CommRing D] [CommRing E] [CommRing F]
    [Algebra R D] [Algebra R E] [Algebra R F]
    (g : PrincipalStage R (B i) (b i) (x.target i) →ₐ[R] D)
    (h : PrincipalStage R (B i) (b i) (x.target i) →ₐ[R] E)
    (p : D →ₐ[R] F) (q : E →ₐ[R] F)
    (he : p.comp (g.comp (principalFanAmbient x i)) =
      q.comp (h.comp (principalFanAmbient x i))) : p.comp g = q.comp h := by
  apply principalFan_restriction_ext x i hx
  simpa only [AlgHom.comp_assoc] using he

end FLT.Mazur.FiniteTypeRelationModel
