/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassIntegralDomain
public import FLT.Mazur.WeierstrassSmoothZeroSection

/-!
# Connectedness of the actual smooth Weierstrass locus

Over a domain the relative smooth open is nonempty and irreducible: it is
an open in the integral cubic and contains the original zero section.
Consequently its connected component at zero is the whole smooth locus.
In particular this applies to every residue-field cubic, including singular ones.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassIntegralChart

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) [IsDomain R]

/-- The original zero section supplies a point of the smooth open over a domain. -/
instance integralSmoothOpen_nonempty : Nonempty (integralSmoothOpen W).toScheme :=
  ⟨integralSmoothZero W (⟨⊥, inferInstance⟩ : PrimeSpectrum R)⟩

/-- The actual relative smooth open is irreducible over any domain. -/
instance integralSmoothOpen_irreducibleSpace :
    IrreducibleSpace (integralSmoothOpen W).toScheme :=
  (integralSmoothOpen W).ι.isOpenEmbedding.irreducibleSpace

/-- In particular the smooth locus of every special-fiber cubic is connected. -/
theorem integralSmoothOpen_connectedSpace :
    ConnectedSpace (integralSmoothOpen W).toScheme := inferInstance

/-- The connected component of the original zero point is the entire actual smooth locus. -/
theorem integralSmoothZero_connectedComponent (s : Spec (.of R)) :
    connectedComponent (integralSmoothZero W s) = Set.univ :=
  PreconnectedSpace.connectedComponent_eq_univ _

/-- Inside the cubic, the image of the zero component is exactly the smooth open. -/
theorem integralSmoothZero_component_image (s : Spec (.of R)) :
    (integralSmoothOpen W).ι '' connectedComponent (integralSmoothZero W s) =
      (integralSmoothOpen W : Set (integralCurve W)) := by
  rw [integralSmoothZero_connectedComponent, Set.image_univ, Scheme.Opens.range_ι]

end FLT.Mazur.WeierstrassIntegralChart
