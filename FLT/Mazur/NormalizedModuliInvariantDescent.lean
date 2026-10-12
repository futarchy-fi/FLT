/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.NormalizedModuliParameterOverlap
public import FLT.Mazur.SchemeFppfFamilyCover

/-!
# Scheme-valued descent of invariants of the original modular class

Invariance here forgets auxiliary labels and cyclic generators. For a proved
fppf family representing one original modular class, subcanonicity produces a
unique actual scheme morphism from its base.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.UniversalWeierstrass
open GeneralizedEllipticCurve.FiniteSubgroup
variable (n : ℕ) [NeZero n] {Y : Scheme} (v : cyclicNormalizedSlice n ⟶ Y)

/-- Scheme-valued invariance under equality of the original ample cyclic class. -/
def CyclicModuliInvariant : Prop :=
  ∀ (T : Scheme) (p q : T ⟶ cyclicNormalizedSlice n),
    (cyclicNormalizedSliceModuliMap n).app (Opposite.op T) (ULift.up p) =
      (cyclicNormalizedSliceModuliMap n).app (Opposite.op T) (ULift.up q) →
        p ≫ v = q ≫ v

/-- Invariants descend uniquely along any actual normalized fppf presentation. -/
theorem cyclicModuliInvariant_cover_descent (hv : CyclicModuliInvariant n v)
    {S : Scheme} (c : ampleCyclicClasses S n)
    (C : Scheme.Cover.{0} Scheme.fppfPrecoverage S)
    (p : ∀ i : C.I₀, C.X i ⟶ cyclicNormalizedSlice n)
    (hp : ∀ i, (cyclicNormalizedSliceModuliMap n).app (Opposite.op (C.X i))
      (ULift.up (p i)) = ampleCyclicClassesPullback (C.f i) n c) :
    ∃! d : S ⟶ Y, ∀ i, C.f i ≫ d = p i ≫ v := by
  have hcompat : Presieve.Arrows.Compatible (yoneda.obj Y) C.f (fun i ↦ p i ≫ v) := by
    intro i j T a b hab
    change a ≫ p i ≫ v = b ≫ p j ≫ v
    simpa only [Category.assoc] using hv T (a ≫ p i) (b ≫ p j)
      (cyclicNormalizedSliceModuliMap_overlap n c (C.f i) (C.f j)
        (p i) (p j) (hp i) (hp j) a b hab)
  have hy : Presieve.IsSheafFor (yoneda.obj Y) C.presieve₀ :=
    (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable
      (J := Scheme.fppfTopology) _).isSheafFor _
        (Precoverage.generate_mem_toGrothendieck C.mem₀)
  exact (Presieve.isSheafFor_arrows_iff _ _).mp hy _ hcompat

end FLT.Mazur.UniversalWeierstrass
