# RTL sources

TRACE does not ship third-party RTL. `fetch_rtl.py` rebuilds, bit for bit, the sources that each design's proof was
imported from: it fetches the upstream repository at the pinned commit, copies the used files, applies our fix
patches, adds our wrapper files and checks every sha256 against `designs.json`.

```
python3 rtl/fetch_rtl.py                  # all designs into rtl/src/<design>/
python3 rtl/fetch_rtl.py --design kronos  # one design
```

Requirements: python3 and git (network access to GitHub). Each `rtl/src/<design>/verilator.f` lists the Verilator
options, top module and files used for elaboration (Verilator 4.028, `--xml-only`).

| design | upstream | commit | license | our changes |
|---|---|---|---|---|
| darkriscv | [darklife/darkriscv](https://github.com/darklife/darkriscv) | `4aa4379` | BSD-3-Clause | JALR clears target bit 0 |
| steel | [riscv-steel/riscv-steel](https://github.com/riscv-steel/riscv-steel) | `7af8290` | MIT | environment wrapper only |
| srv32 | [kuopinghsu/srv32](https://github.com/kuopinghsu/srv32) | `7129bdc` | MIT | environment wrapper only |
| nerv | [YosysHQ/nerv](https://github.com/YosysHQ/nerv) | `6de2a41` | ISC | environment wrapper only |
| a5 | [AngeloJacobo/RISC-V](https://github.com/AngeloJacobo/RISC-V) | `b0ab055` | MIT | JALR clears target bit 0; misaligned-target trap uses that target; wrapper |
| bzeeno | [bzeeno/riscv-cpu](https://github.com/bzeeno/riscv-cpu) | `c190c1f` | none stated | see below |
| picorv32 | [YosysHQ/picorv32](https://github.com/YosysHQ/picorv32) | `87c89ac` | ISC | Verilator top-level wrapper only |
| tinyriscv | [liangkangnan/tinyriscv](https://github.com/liangkangnan/tinyriscv) | `7cb8c8a` | Apache-2.0 | JALR clears target bit 0 |
| kronos | [SonalPinto/kronos](https://github.com/SonalPinto/kronos) | `13678d4` | Apache-2.0 | WAW interlock in the hazard unit |
| ultraembedded | [ultraembedded/riscv](https://github.com/ultraembedded/riscv) | `7ae6f80` | BSD-3-Clause | none |

Bzeeno: the proofs use a re-expression of the upstream design kept as module quotations in the TRACE Coq library
(`src/Ex/External/Bzeeno{Pipeline,Control,FullCore,CPU}.v`; it also fixes the upstream comparator). `fetch_rtl.py`
exports it with `tools/export_quoted_rtl.py` (nothing is downloaded) and applies two patches: the AUIPC immediate
case, and the control-unit fixes for negative JAL offsets (sign extension) and redirects during a load-use stall.
Use `--coq-dir` if the Coq library is not at `../coq`.

Layout: `designs.json` (per design: repository, commit, license, files with sha256, patches, wrappers, Verilator
arguments), `patches/<design>/` (unified diffs, first line says what they fix), `wrappers/<design>/` (our files).
