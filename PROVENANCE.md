# Provenance

Every file in `OperatorFirst/` is a byte-identical copy of the source in the
private research repository `dicipler-pixel/operator-first`, taken from branch
`formal/rice-mele-odd-symmetry-2026-09-12` at commit
`936cf1e8fe014c00a25bf508773f78328ba287c0` (13 September 2026). Across all
branches of that repository, each of these nine files exists in exactly one
version, so there is no choice of copy.

## Where each module was first checked

| Module | Theorems | First checked in | Earlier recorded evidence |
| :--- | :-: | :--- | :--- |
| `Offset`, `OffsetFock` | 45 + 8 | PR #2 (Offset core) | Actions run 33976842609, pass |
| `OffsetEndpoint` | 30 | PR #5 (endpoint extension) | Actions run 33991660104, pass |
| `EndpointProgress` | 8 | PR #6 | report at commit `824fa79f`, source hash below |
| `EndpointTransfer`, `FiniteCovariance`, `BandObstruction` | 17 + 9 + 2 | PR #6 (finite proof completion) | report at commit `88fc1f35`, source hashes below |
| `LaurentBoundary` | 20 | PR #6 (Laurent boundary) | runs 34041125969 / 34041636870, report at commit `6ab87323` |
| `RiceMeleOddSymmetry` | 4 | PR #31 | no extracted green run on record; this repository's check is its first clean record |

Earlier evidence belongs to those runs and commits. The verdict for this
repository is the proof check in `.github/workflows/build.yml`, run on the
exact commit shown with each run.

## SHA-256 of the proof sources

```
bc768c64118cfd7ce0c9bea3204cffe5ec4fb917aa87763a57565a551a3d47b3  OperatorFirst/Offset.lean
fa64b4a7540aca4da4765b507050d34e1ea1d67ddd88ff5c973ea630f987c277  OperatorFirst/OffsetFock.lean
a3846481d89505858c40bd918f404513ec230a9aa28ec60d7bbe4131d2f84799  OperatorFirst/OffsetEndpoint.lean
d543af190e4377c92d540922e58bdf865a0ea81d3c9d582b929751232ec522cc  OperatorFirst/EndpointProgress.lean
95663f7098c60f0848a24249b826850a94a332a8d9e80f3ba22ecf81bf73d5f9  OperatorFirst/EndpointTransfer.lean
e22c5877d26bea1ac1423eb61216ac09ccd9b64d373400be452167c7f74c4e56  OperatorFirst/FiniteCovariance.lean
51c6696358a5c372a3330c3b8bc4a304ab5453c5d2477fc5849a4d03b22c732f  OperatorFirst/BandObstruction.lean
ee5a646e558a6c4c62005e1b20d4e4bf21144c0ccdaaffc8a49f3c738199f05f  OperatorFirst/LaurentBoundary.lean
ac77d42dd610479a95c300bf29a4059927436bf0e51f25e584bb81d9f45a9d73  OperatorFirst/RiceMeleOddSymmetry.lean
```

The hashes of `EndpointProgress`, `EndpointTransfer`, `FiniteCovariance`,
`BandObstruction` and `LaurentBoundary` equal the hashes recorded in the
earlier verification reports.

## Files new in this repository

- `OperatorFirst.lean`: imports the nine modules so `lake build` compiles all
  of them. It replaces nothing; the research repository's root file of the same
  name holds different, unrelated core theorems and is not included here.
- `OffsetLean/Headline.lean`: the seven headline statements.
- `FalseControls/`: the 13 negative controls, extracted unchanged from the
  earlier verifier scripts (`verify_offset.py`, `verify_endpoint.py`,
  `verify_endpoint_progress.py`, `verify_offset_completion.py`,
  `verify_laurent_boundary.py`) and `rice_mele_formal/FalseControl.lean`.
- `OperatorFirst/BoundaryModel.lean` (13 theorems) and its two controls
  `FalseControls/false_dispersion_growth.lean`, `false_onsite_sign.lean`: copied
  unchanged from the `lean_boundary/` folder of the v31 reproduction archive of the
  paper (also in `offset_proofs.zip`), pinned there to the same Mathlib commit as
  the modules above. SHA-256
  `f1d686fbfc6837d97d5675bf40fefa0fa0b330010e37243a3e9c4f0d15503c77`.
  This repository's proof check is its first public record.
- `scripts/verify.py`: one audit replacing those five scripts.
