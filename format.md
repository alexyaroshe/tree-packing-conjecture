# Residual-graph certificates

This source release supports the certificate-checked results through n=13. The [software 2.0.0 DOI](https://doi.org/10.5281/zenodo.24293386) and [certificate 1.0.0 DOI](https://doi.org/10.5281/zenodo.24293356) are reserved for unpublished review drafts.

The earlier n=12 software release, v1.0.0, and its [software DOI](https://doi.org/10.5281/zenodo.23557604) remain historical records; the [n=12 ledger DOI](https://doi.org/10.5281/zenodo.23537606) identifies the earlier sequence campaign. Neither historical DOI identifies these new certificates.

## Search and verification

The parallel solver shares completed winning and losing residual states across workers. Checkpoints retain completed states and the completed root prefix. A new campaign produces a state certificate; a saved checkpoint or successful search does not establish acceptance.

Reconstruction produces a proof stream containing tree placements, residual graphs, child references and vertex relabellings. The C++ checker and independent C checker validate that stream, including the tree catalog, every required tree obligation and the assigned root coverage. Both complete verdicts must agree. The checkers are unchanged from the completed n=13 verification; they are separate executable implementations, not formally verified programs.

The release verifier's `--check-only` option compares source and build identities without proof replay. It does not produce checker verdicts.

## Certificate formats

| Archives | Stored | Reconstruction |
|---|---|---|
| `n11_placement_only.zip`, `n12_placement_only.zip` | Tree catalog, root coverage, residual states & ranked tree embeddings | Child references & vertex relabellings |
| `n13_state_only.zip` | Tree catalog, root coverage & winning residual states | Tree placements, child references & vertex relabellings |

Placement-only reconstruction uses the recorded embeddings. It does not search for tree placements, although graph canonicalization may search graph labellings. State-only reconstruction searches for placements against retained lower-level states. It does not repeat the original search campaign. Neither checker performs placement search.

The n=11/n=12 downloads remain manageable with placements retained. State-only keeps the n=13 download smaller at the cost of placement reconstruction. Both formats produce the same proof-stream format for the same two checkers. [certificates.json](certificates.json) records the archive identities and verification scope. Each certificate ZIP includes its own verification sources and dependencies; the large certificate files are distributed separately from this source release. The ZIPs use the same checker and reconstruction paths as this source release. The release verifier checks their source files and compiled identities before proof verification.

## Requirements

Linux or macOS, Python 3.9 or newer, C++17 and C17 compilers, make and the zstd command are required. The bundled nauty 2.9.3 source is built with thread-local storage; no dependency download is needed. Build output paths must contain no whitespace because the upstream nauty installation rules do not support it.

The completed n=13 reconstruction and both checker passes took 14 hours 8 minutes with eight reconstruction workers on the recorded Linux host. Sampled peak aggregate memory was 119.7 GiB. Allow at least 160 GiB system RAM and 20 GB additional working disk for that configuration; the 80 GiB reconstruction limit excludes checker memory. These measurements are not performance guarantees on other machines. The 1.94 TB proof is streamed rather than saved, and the n=13 archive requires ZIP64 support.
