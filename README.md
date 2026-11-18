# TRACE

TRACE proves, in Coq, that the real Verilog of a pipelined RISC-V CPU refines the RISC-V ISA specification,
starting from the actual reset state and for unbounded executions with the SystemVerilog constructs that real cores use,
and adds a framework that turns RTL into proof obligations, generates most proofs from templates, and checks the
result with `coqc` and `coqchk`.

## Layout

| path | content |
|---|---|
| `src/Lang/` | Verilog/SystemVerilog semantics: signal state, combinational logic as a least fixed point, clock-edge transitions, ITree lifting |
| `src/Lib/` | shared helpers (finite maps, bit vectors) |
| `src/Ex/RvCore/` | ISA reference (`FormalSpec.run1`: fetch, decode, execute) on `riscv-coq` |
| `src/Ex/External/`, `src/Ex/Generated/` | shared proof library: state relations, per-instruction-family obligations (data-op, load, store, branch, jump), pipeline and cycle-composition lemmas |
| `tools/` | Python framework: RTL frontends, design contracts, obligation and template generators, proof replay and checking, fault injection |
| `framework/` | design contracts, contract profiles, pipeline skeletons, rule library and template sources used by the generators |
| `rtl/` | script that fetches the evaluated CPUs at pinned commits and applies our bug-fix patches|
| `dep-patches/`, `scripts/` | Coq 8.18 compatibility patches for the dependencies and the setup script |

## Requirements

* OCaml 4.14 and Coq 8.18.0 with `coq-itree` 5.2.1, `coq-paco` 4.2.3, `coq-ext-lib` 0.13.1, and FreeSim
  (installed by `scripts/setup_deps.sh` from the VerilRocq repository).
* Python 3.10 and `pip install -r requirements.txt`.
* Optional: Verilator 4.028 for the Verilator-XML frontend (`tools/cpu_array_frontend.py`).

The tools call `coqc`/`coqchk` from a local opam switch in the repository root (`_opam/bin`):

```sh
git clone https://github.com/ErosSph/TRACE.git && cd TRACE
opam switch create . ocaml-base-compiler.4.14.2 --no-install
eval $(opam env)
opam repo add coq-released https://coq.inria.fr/opam/released
opam install -y coq.8.18.0 coq-itree.5.2.1 coq-paco.4.2.3 coq-ext-lib.0.13.1
pip install -r requirements.txt
scripts/setup_deps.sh     # pinned submodules coqutil, riscv-coq, VerilRocq (+ patches); installs FreeSim
make -j8                  # builds dep/ and the framework in src/
```

## Tests

```sh
python -m unittest discover -s tools -p 'test_*.py'
```
