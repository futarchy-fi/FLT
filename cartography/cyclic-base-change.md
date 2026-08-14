# Map: cyclic base change for `GL(2)`

Scope: FLT-on-Lean, bead hub-lsb1u.5.  The FLT repository is treated as
read-only; all paths below point into `/Users/kas/FLT`, while this map is the
working-directory deliverable.  “S/M/L/XL” means, respectively, a short local
lemma, a several-page package, a substantial theorem, or a deep theorem plus
infrastructure.  A citation followed by `(literature-verify)` is from memory
and needs a bibliography/theorem-number check before being used as a formal
reference.

## 1. What FLT needs

### Evidence in the blueprint and assumptions

The route is explicit about what is being assumed:

* The introduction says that the project assumes Galois representations of
  weight-2 Hilbert forms and “Langlands' cyclic base change theorem for
  `GL_2`” (`/Users/kas/FLT/blueprint/src/chapter/ch01introduction.tex:49-52`).
* Modularity is deliberately restricted to the units of the totally definite
  quaternion algebra over a totally real field of even degree, with trivial
  infinity type (`/Users/kas/FLT/blueprint/src/chapter/ch04overview.tex:12-19`).
* The Skinner--Wiles reduction explicitly needs cyclic base change, a
  characterization of its image, multiplicity one, and (because modularity is
  quaternionic) Jacquet--Langlands
  (`/Users/kas/FLT/blueprint/src/chapter/ch04overview.tex:84-90`, especially
  `:86-88`).
* The potential-modularity paragraph uses a representation induced from a
  character, then Jacquet--Langlands
  (`/Users/kas/FLT/blueprint/src/chapter/ch04overview.tex:93-98`).
* The bestiary names “cyclic base change plus classification of image” for
  totally definite quaternion algebras and automorphic induction
  `GL_1(K) -> GL_2(F)` for a degree-2 totally imaginary extension
  (`/Users/kas/FLT/blueprint/src/chapter/chtopbestiary.tex:210-214`).
* The assumptions README puts automorphic induction, cyclic base change plus
  image classification, and Jacquet--Langlands in the forthcoming list, and
  warns that image classification may also need multiplicity one
  (`/Users/kas/FLT/FLT/Assumptions/README.md:42-60`).
* The chosen FLT route avoids Langlands--Tunnell: the 3-switch is postponed
  until after a conductor-2 compatible family, avoiding the non-Galois cubic
  cyclic base change required by Langlands--Tunnell
  (`/Users/kas/FLT/FLT/Assumptions/Odlyzko.lean:30-41`).
* The `knownin1980s` policy explicitly lists Langlands' cyclic base change
  among the pre-1990 results it may stand for, while requiring comments that
  explain the historical route (`/Users/kas/FLT/FLT/Assumptions/KnownIn1980s.lean:60-77`).

Verbatim route anchors (the requested file:line quotations):

> “we will assume Langlands' cyclic base change theorem for `GL_2`”
> (`blueprint/src/chapter/ch01introduction.tex:49-52`).

> “this needs cyclic base change for `GL(2)` and also a characterisation of the
> image of the base change construction; this seems to need a multiplicity one
> result” (`blueprint/src/chapter/ch04overview.tex:86-88`).

> “We also need cyclic base change plus classification of image ... and we need
> automorphic induction from `GL_1(K)` to `GL_2(F)` when `K/F` is a degree 2
> totally imaginary extension” (`blueprint/src/chapter/chtopbestiary.tex:212-214`).

> “Automorphic induction from GL_1 to GL_2 ... Cyclic base change for GL_2 and
> classification of image ... The Jacquet-Langlands correspondence ...”
> (`FLT/Assumptions/README.md:51-60`).

> “The advantage of this is that it avoids the Langlands-Tunnell theorem
> (which needs non-Galois cubic cyclic base change)”
> (`FLT/Assumptions/Odlyzko.lean:30-36`).

> “This stretches from ... Taylor's theorem attaching Galois representations
> ... [and] Langlands' work on cyclic base change”
> (`FLT/Assumptions/KnownIn1980s.lean:60-70`).

### The strongest formal placeholder currently in the repo

`FLT/GaloisRepresentation/Automorphic.lean` gives the most useful exact
formal anchor.  Its docstring assumes a finite solvable extension of totally
real fields, an odd prime, irreducibility after restriction, an integral flat
rank-2 model at primes above the prime, tame rank-one quotients at the bad
places, and cyclotomic determinant (`:109-126`).  The theorem interface then
spells this out (`:127-183`) and concludes

> `rho.IsAutomorphicOfLevel ... S` iff the restriction to `E` is automorphic at
> the pulled-back level (`:179-183`),

but the proof is still `sorry` (`:184`).  This is a Galois-representation
formulation of the needed comparison, not a proof of Langlands' theorem.

The exact formal hypotheses, by line, are:

| Lines | Interface hypothesis |
|---|---|
| `:128-130` | `F` totally real and `Even (finrank ℚ F)`. |
| `:131-134` | `E` totally real, an `F`-algebra, Galois over `F`, and solvable. |
| `:134-136` | `p` prime, with cyclotomic-field rank side conditions over both `F` and `E`. |
| `:137-143` | Continuous `Q_p-bar` representation on a finite free rank-2 space, irreducible after restriction to `G_E`. |
| `:144-146` | Determinant is the cyclotomic character. |
| `:147-163` | Integral finite-free rank-2 model whose scalar extension is `rho`, flat at every `v | p`. |
| `:164-168` | Finite `S`, disjoint from `p`, and unramified away from `S union {v|p}`. |
| `:169-178` | At every `w in S`, a surjective rank-one quotient with tame inertia in its kernel. |
| `:179-184` | Automorphic-at-`S` iff automorphic after restriction at the pulled-back level `S_E`; proof is `sorry`. |

### Weakest sufficient FLT statement

The primitive assumption should be split as follows.

1. **Prime-cyclic Galois base change + descent.**  For every cyclic Galois
   extension `E/F` of prime degree (including degree 2), with `F` totally real
   of even degree and `E` totally real, and every weight-2, trivial-central-
   character automorphic object in the FLT level class, assume:
   `pi` is automorphic over `F` iff `BC_E/F(pi)` is automorphic over `E`.
   Also assume the image criterion and fibers: a cuspidal `Pi` over `E` is in
   the image exactly when it is `Gal(E/F)`-invariant (with the standard local
   hypotheses), and two descents differ by a Hecke character of
   `F` trivial on norms, equivalently a character of `Gal(E/F)` via class field
   theory.  A theorem for arbitrary cyclic degree implies this; the repo gives
   no evidence that one fixed prime degree is enough, so do **not** reduce to
   quadratic base change alone.  Iterating a normal series with prime-cyclic
   quotients supplies the finite-solvable version used by the placeholder.
   The exact Skinner--Wiles choice of degrees is `(literature-verify)`.

2. **Local hypotheses (weakest version visible in the formal anchor).**  Keep
   only what the FLT automorphy predicate uses: a continuous 2-dimensional
   `p`-adic representation with cyclotomic determinant; an integral finite-free
   rank-2 model flat at every `v | p`; unramified outside `S union {v|p}`; and,
   for each `v in S`, a one-dimensional tame quotient.  Require restriction to
   `G_E` to be irreducible (absolute irreducibility is the safe field-valued
   formulation).  `S_E` is the pullback of `S`.  The signature does not impose
   an extra ramification condition on `E/F`; if a proof needs `E/F` unramified
   or prescribed at `p`, state that as an auxiliary local condition rather than
   hiding it.  Preservation of flatness/tameness under the chosen tower is
   `(literature-verify)`.

3. **Automorphic induction, only in the quadratic CM case.**  For a quadratic
   totally imaginary (CM) extension `K/F`, automorphic induction of the
   algebraic Hecke characters used by Moret--Bailly/converse-theorem steps
   produces the required weight-2 `GL_2/F` object, with the expected local
   factors and central character.  This is degree 2 for induction, not a claim
   that degree 2 suffices for base change.

4. **No Langlands--Tunnell node.**  The route needs no non-Galois cubic base
   change; the Odlyzko assumption records this design choice exactly.

## 2. Numbered statement inventory

The order follows the usual Langlands 1980 proof architecture (local transfer,
matching functions, twisted trace formula, descent) with the shared nodes that
modern trace-formula expositions make explicit.  “Shared [JL]” means that the
node belongs in the Jacquet--Langlands hub (hub-lsb1u.4) and is linked here,
not re-proved here.

| # | Node and informal statement | Size | Citation / repo anchor |
|---|---|---|---|
| 1 | **Adelic automorphic objects.** Define admissible local representations, restricted tensor products, cuspidality, central character, weight 2, level `U_1(S)`, and base change of an object. | L | Blueprint definitions are explicitly unfinished (`chtopbestiary.tex:144-205`); Langlands, *Base Change for GL(2)* (1980), Ch. 1 `(literature-verify)`; Gelbart, *Automorphic Forms on Adele Groups* `(literature-verify)`. |
| 2 | **Adeles, measures, and quotient finiteness [JL].** Fix Haar/Tamagawa normalizations, adelic quotient conventions, and finite double-coset models for definite quaternionic forms. | M | `FLT/NumberField/AdeleRing.lean:28-45,96-126,187-197`; `FLT/AutomorphicForm/QuaternionAlgebra/FiniteDimensional.lean:15-24,51-70`; Arthur, *An Introduction to the Trace Formula* (2005) `(literature-verify)`. |
| 3 | **Local `GL_2` representation theory.** Classify principal series, special, and supercuspidal types sufficiently to define local Langlands parameters and Satake data. | L | Langlands 1980, local chapters `(literature-verify)`; a modern LLC exposition such as Bushnell--Henniart `(literature-verify)`. |
| 4 | **Local cyclic base change.** For every place `v` and `w|v`, restrict the local parameter from `W_{F_v}` to `W_{E_w}`; preserve central character and the standard/local `L`- and epsilon-factors. | L | Langlands 1980, local base-change theorem `(literature-verify)`; modern LLC compatibility exposition `(literature-verify)`. |
| 5 | **Orbital integrals and matching functions [JL].** Define the norm correspondence on regular semisimple conjugacy classes and match test functions on `GL_2(F_v)` and `GL_2(E_w)`. | XL | Langlands 1980, Chs. 2--3 `(literature-verify)`; Arthur, “The trace formula in invariant form” (1981) and *An Introduction to the Trace Formula* (2005) `(literature-verify)`. |
| 6 | **Twisted trace formula [JL].** State the trace formula for `GL_2(E)` twisted by a generator of `Gal(E/F)`, including geometric and spectral sides and convergence/truncation. | XL | Langlands 1980, trace-formula chapters `(literature-verify)`; Arthur, “The trace formula in invariant form” and *An Introduction to the Trace Formula* `(literature-verify)`. |
| 7 | **Transfer/fundamental lemma for cyclic `GL_2` [JL].** Matching orbital integrals make the twisted geometric side over `E` equal to the ordinary side over `F`; include ramified and archimedean places needed by the weight-2 class. | L/XL | Langlands 1980 `(literature-verify)`; Labesse, *Cohomologie, stabilisation et changement de base* (Astérisque 257) `(literature-verify)`. |
| 8 | **Spectral comparison and existence of base change.** Equality of the two trace formulas produces `BC_{E/F}(pi)`, with the expected local components, central character, and unramified Satake parameters. | XL | Langlands 1980, main base-change theorem `(literature-verify)`; Arthur 2005 and Labesse 1999 modern expositions `(literature-verify)`. |
| 9 | **Preservation of cuspidality, level, weight, and local type.** Record when `BC(pi)` is cuspidal and that the FLT `U_1(S)`/tame-rank-one conditions pull back to `S_E`; handle the exceptional induced/non-cuspidal cases. | L | Langlands 1980 `(literature-verify)`; formal FLT target and hypotheses `FLT/GaloisRepresentation/Automorphic.lean:109-126,164-183`. |
| 10 | **Strong multiplicity one [JL].** Equality of almost all local components (or Hecke eigenvalues) identifies an automorphic representation; this makes the descended object unique up to the expected twist. | L | Jacquet--Shalika, strong multiplicity one `(literature-verify)`; the FLT need is identified at `ch04overview.tex:86-88` and `Assumptions/README.md:51-53`. |
| 11 | **Image classification/descent.** A cuspidal `Pi` over `E` lies in the cyclic base-change image iff it is Galois invariant (with the standard central-character condition); the fiber over `Pi` is a torsor under characters of `Gal(E/F)`. | L | Langlands 1980, descent/image theorem `(literature-verify)`; FLT explicitly calls for “characterisation of the image” (`ch04overview.tex:86-88`) and “classification of image” (`chtopbestiary.tex:212-214`). |
| 12 | **Prime-cyclic tower.** Refine a finite solvable Galois extension by normal subgroups with cyclic prime quotients and iterate nodes 8--11; check irreducibility and local hypotheses at each stage. | M | Elementary solvable-group argument plus global CFT; the repo’s stronger finite-solvable placeholder is `FLT/GaloisRepresentation/Automorphic.lean:131-134`; exact tower use in Skinner--Wiles `(literature-verify)`. |
| 13 | **Quadratic automorphic induction.** For `K/F` quadratic totally imaginary and an algebraic Hecke character `chi` of `K`, construct `AI_{K/F}(chi)` on `GL_2/F`; state cuspidality unless `chi` is Galois invariant and specialize to weight 2/trivial central character. | XL | The required degree-2 CM case is named at `chtopbestiary.tex:212-214`; Langlands/Arthur--Clozel automorphic induction references `(literature-verify)`. |
| 14 | **AI local/global compatibility.** Local induction agrees with the restriction/induction of Weil parameters and gives the expected standard `L`-factor identity; Hecke eigenvalues match the induced Galois representation. | L | Langlands local theory and automorphic-induction expositions `(literature-verify)`; the FLT use of “induced from a character” is `ch04overview.tex:93-96`. |
| 15 | **Jacquet--Langlands transfer and multiplicity one [JL].** Transfer the relevant `GL_2/F` objects to the totally definite quaternion algebra and back, preserving the weight-2 finite-place data; use quaternionic multiplicity one. | XL | Shared with hub-lsb1u.4; blueprint requirement `chtopbestiary.tex:212-214`, Skinner--Wiles dependency `ch04overview.tex:86-88`; Jacquet--Langlands `(literature-verify)`. |
| 16 | **Galois realization/compatibility [Galois].** Attach a compatible 2-dimensional family to a weight-2 quaternionic automorphic form, and identify restriction/base change through Frobenius polynomials; compare “automorphic” with the FLT Galois predicate. | XL | Blueprint theorem (not ready) `chtopbestiary.tex:216-229`; concrete FLT predicate `FLT/GaloisRepresentation/Automorphic.lean:56-95`; its BC target is `:179-184`. |
| 17 | **Class field theory and characters [CFT].** Use local/global reciprocity to build the cyclic extensions and norm-trivial Hecke characters that describe fibers and AI; impose prescribed local behavior and linear disjointness. | L | Blueprint global CFT and solvable-extension consequence `chtopbestiary.tex:79-94`; CFT hub-lsb1u.9; exact pre-1990 reference `(literature-verify)`. |

## 3. Dependency edges and hub ownership

The compact dependency DAG is:

```text
17 [CFT] ──► 12 ──► 8 ──► 9 ──► 11 ──► FLT Skinner–Wiles MLT
  │                    ▲       │
  └────────► 13 ──► 14 ┘       └──► 16 [Galois]

1 ─► 3 ─► 4 ─► 8
1 ─► 2 ─► 5 ─► 6 ─► 7 ─► 8
2,5,6,7,10,15 are shared trace-formula/JL infrastructure [JL]
15 ─► 16; 10 ─► 11
```

* **Jacquet--Langlands hub-lsb1u.4 (shared, do not duplicate):** nodes 2, 5,
  6, 7, 10, and 15.  The base-change chapter consumes adelic quotients,
  Haar/Tamagawa measures, orbital-integral matching, twisted/ordinary trace
  formulas, transfer, and multiplicity one.  Its BC-specific additions are
  the cyclic norm correspondence (4), spectral comparison (8), and image
  criterion (11).
* **Galois-representations hub-lsb1u.10:** node 16 owns compatible families,
  Frobenius/Satake comparison, restriction maps, irreducibility, and flat
  integral models.  The present chapter only states the compatibility edge.
* **CFT hub-lsb1u.9:** node 17 owns reciprocity, solvable extensions with
  prescribed local completions, norm characters, and the character group of
  `Gal(E/F)`.  Node 12 must consume this rather than restating CFT.
* **FLT overview edges:** `ch04overview.tex:86-90` consumes 8, 9, 10, and 15;
  `ch04overview.tex:93-98` consumes 13, 14, and 15.  The bestiary’s list at
  `chtopbestiary.tex:212-214` is the same interface at the automorphic level.

## 4. Mathlib/repo anchors (inspection only)

These are implementation anchors, not evidence that the analytic theorems are
already proved.

| Anchor | What exists | What is still absent |
|---|---|---|
| `FLT/GaloisRepresentation/Automorphic.lean:56-95` | Narrow `IsAutomorphicOfLevel`: quaternion algebra of discriminant 1, weight 2, Hecke-algebra eigenvalue map, Frobenius determinant/trace conditions. | No general `GL_2` automorphic-representation type. |
| `FLT/GaloisRepresentation/Automorphic.lean:109-126,127-184` | A precise finite-solvable BC-shaped axiom with `S`, flatness, tame rank-one quotient, determinant, irreducibility, and `S_E`; proof ends in `sorry`. | Trace-formula proof, descent/image theorem, and local transfer. |
| `FLT/Deformations/RepresentationTheory/GaloisRep.lean:47-83,96-116` | Continuous Galois reps, field restriction (`GaloisRep.map`), conjugacy, and kernels. | Automorphic-to-Galois comparison. |
| `FLT/Deformations/RepresentationTheory/GaloisRep.lean:203-246` | Determinant and scalar base change of Galois reps; restriction/base-change commute. | Arithmetic BC of automorphic representations. |
| `FLT/Deformations/RepresentationTheory/GaloisRep.lean:387-409` | Flat-prolongation predicate, `IsFlatAt`, and irreducibility predicate. | Proof that these local conditions survive a chosen cyclic tower. |
| `FLT/NumberField/AdeleRing.lean:28-45,96-126,187-197` | Adelic base-change map and `L tensor_K A_K ≃ A_L` algebra/homeomorphism. | Haar measures, orbital integrals, trace formula. |
| `FLT/AutomorphicForm/QuaternionAlgebra/Basic.lean:109-155,228-271,397-540` | Weight-2 quaternionic forms, adelic action, levels, and level-form submodules. | `GL_2` representations and BC operators. |
| `FLT/AutomorphicForm/QuaternionAlgebra/FiniteDimensional.lean:15-24,51-70` | Finite double-coset and module-finiteness infrastructure for definite quaternionic forms. | Spectral trace identity and multiplicity one. |
| `FLT/AutomorphicForm/QuaternionAlgebra/HeckeOperators/Concrete.lean:15-57,645-665,846-943` | Explicit `T_v`, `U_{v,a}`, and Hecke algebra generators for `U_1(S,Q)`. | Hecke eigenpacket transfer under cyclic BC. |
| `blueprint/src/chapter/chtopbestiary.tex:144-214` | Blueprint definitions/sketches for automorphic forms, representations, local decomposition, and the exact list of needed theorems. | The text itself says the definitions are not ready. |
| `FLT/Assumptions/README.md:42-63` | Records AI, cyclic BC + image classification, and JL as forthcoming assumptions because automorphic-representation definitions are missing. | No assumption file/axiom yet for any of those three. |

## 5. Route risks and total-size verdict

* **Statement/proof mismatch.** The formal `cyclic_base_change` theorem is a
  `sorry`; it is a useful interface, not a completed result.  The blueprint
  still says that even the automorphic-representation definitions are not ready
  (`chtopbestiary.tex:146`, `:210-214`).
* **Quaternionic versus `GL_2`.** FLT calls the theorem “cyclic base change for
  `GL_2`”, but its automorphy predicate is quaternionic.  Nodes 10 and 15 are
  therefore unavoidable shared JL infrastructure, exactly as the overview
  warns (`ch04overview.tex:86-88`).
* **Prime-cyclic reduction is conditional.** A prime-cyclic tower is the
  smallest safe primitive, but one must check normal-subgroup towers,
  irreducibility at each restriction, and preservation of flat/tame local
  conditions.  The exact Skinner--Wiles tower and any required ramification
  restrictions are `(literature-verify)`.
* **Image classification is not optional.** Existence of `BC` alone does not
  descend automorphy; the invariant-image criterion and character-torsor fiber
  (node 11), plus multiplicity one (node 10), are required by the repo text.
* **Automorphic induction has a narrower domain.** The repo asks for the CM
  degree-2 case.  A general solvable induction theorem would be unnecessary
  overreach; the exact algebraicity, infinity type, and central-character
  normalization for the auxiliary character are `(literature-verify)`.
* **No Langlands--Tunnell dependency.** Do not add a non-Galois cubic BC node;
  `Odlyzko.lean:30-41` records that the chosen route avoids it.
* **Size verdict.** As an assumption-only interface (prime-cyclic BC + image
  classification, AI in the quadratic CM case, and links to JL/CFT/Galois
  hubs), this chapter is **M/L**.  Proving the inventory from the twisted trace
  formula, matching, and local transfer is **XL**: 17 nodes, with 5--7 XL
  nodes, and the dominant cost is shared with hub-lsb1u.4 rather than local
  Lean algebra.
