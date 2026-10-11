/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteTypeAcyclicDivisorMap

/-!
# The intrinsic full-divisor presheaf on all test schemes

Functoriality follows on the entire ideal, using actual comap identity and
composition. Values consist of actual relative Cartier divisors with acyclic
rank-one positive line, not classes of divisors modulo a relation.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
namespace FLT.Mazur.CartierAbel
open SchemePicard
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R]
  {X : Scheme.{0}} (f : X ⟶ Spec (.of R))
  [IsProper f] [Flat f] [GeometricallyIntegral f]

/-- Identity test maps fix the entire original divisor. -/
theorem finiteTypeAcyclicDivisorMap_id (T : Over (Spec (.of R)))
    (D : AcyclicRankOneRelativeDivisor (Limits.pullback.snd f T.hom)) :
    finiteTypeAcyclicDivisorMap f (𝟙 T) D = D := by
  apply acyclicRankOneRelativeDivisor_ext
  rw [finiteTypeAcyclicDivisorMap_ideal, relativeTotalMap_id, Scheme.IdealSheafData.comap_id]

/-- Composed test maps compose actual full-divisor pullbacks. -/
theorem finiteTypeAcyclicDivisorMap_comp {T U V : Over (Spec (.of R))}
    (g : T ⟶ U) (h : U ⟶ V)
    (D : AcyclicRankOneRelativeDivisor (Limits.pullback.snd f V.hom)) :
    finiteTypeAcyclicDivisorMap f (g ≫ h) D =
      finiteTypeAcyclicDivisorMap f g (finiteTypeAcyclicDivisorMap f h D) := by
  apply acyclicRankOneRelativeDivisor_ext
  simp only [finiteTypeAcyclicDivisorMap_ideal, relativeTotalMap_comp,
    Scheme.IdealSheafData.comap_comp]

/-- The full acyclic divisor presheaf with unrestricted test schemes and test maps. -/
def finiteTypeAcyclicDivisorPresheaf : (Over (Spec (.of R)))ᵒᵖ ⥤ Type where
  obj T := AcyclicRankOneRelativeDivisor (Limits.pullback.snd f T.unop.hom)
  map g := ↾(finiteTypeAcyclicDivisorMap f g.unop)
  map_id T := by
    apply ConcreteCategory.hom_ext
    intro D
    exact finiteTypeAcyclicDivisorMap_id f T.unop D
  map_comp g h := by
    apply ConcreteCategory.hom_ext
    intro D
    exact finiteTypeAcyclicDivisorMap_comp f h.unop g.unop D

end FLT.Mazur.CartierAbel
