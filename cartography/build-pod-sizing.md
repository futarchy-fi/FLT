# FLT build-pod sizing

Measurement for `hub-r7qdn.8`, 2026-09-08.  The purpose is to set a practical
worker floor from the heaviest files in the current build, not to predict every
future Mathlib module.

## Method

- Host: `farol`, 48 logical CPUs, 187 GiB RAM.
- Toolchain: Lean `4.34.0-rc1` (`3447a668`), Lake `5.0.0`.
- Candidate files were selected by current `.olean` size.
- Each source was then compiled independently with `lake env lean -o /tmp/...`.
  Dependencies remained cached; elapsed time and child-process maximum RSS came
  from Python's standard-library `resource.getrusage`.

This measures the marginal elaboration/type-checking peak of one heavy module.
It does not measure a cold download or a maximally parallel clean build.

## Results

| module | source | `.olean` | elapsed | peak RSS |
|---|---:|---:|---:|---:|
| `GroupScheme.FiniteFlat` | 108.2 KiB | 2.19 MiB | 56.72 s | 1.95 GiB |
| `AutomorphicForm.QuaternionAlgebra.Basic` | 53.6 KiB | 2.55 MiB | 70.60 s | 2.17 GiB |
| `AutomorphicForm.QuaternionAlgebra.HeckeOperators.Concrete` | 53.1 KiB | 1.55 MiB | 56.71 s | 2.23 GiB |
| `Mathlib.RepresentationTheory.Homological.ContCohomology.CupProduct` | 29.8 KiB | 1.64 MiB | 70.09 s | **3.80 GiB** |
| `Mathlib.Topology.Algebra.RestrictedProduct.Equiv` | 29.0 KiB | 1.23 MiB | 10.12 s | **3.80 GiB** |

The local `.lake` tree occupies 8.8 GiB with dependencies and build products.

## Sizing decision

- **Ordinary proof worker:** request 4 vCPU / 8 GiB RAM; 20 GiB ephemeral disk.
- **Clean full-build worker:** request 8 vCPU / 16 GiB RAM; 30 GiB ephemeral disk.
- **Hard floor:** never schedule these heavy modules below 6 GiB RAM.
- Run at most one measured heavy module per 8-GiB worker.  Parallel heavy-file
  builds require the 16-GiB class.

Eight GiB gives slightly more than 2x headroom over the observed 3.80-GiB
single-module peak.  There is no evidence here supporting a 32-GiB default;
promote an individual packet only after an observed out-of-memory failure.
