#!/usr/bin/env python3
"""Import the actual Pico internal RF writer from full, unmodified elaboration.

This is a selected-process certificate, NOT a whole CPU import.  In particular,
unknown constants elsewhere are recorded and never replaced with zero.
"""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import xml.etree.ElementTree as ET
from cpu_array_frontend import ArrayTranslator
from cv32e40p_extended_frontend import SignalInfo, loc_line, write_coq

ROOT = Path(__file__).resolve().parents[1]

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    out = args.output.resolve()
    out.mkdir(parents=True, exist_ok=True)
    rtl = ROOT.parent/'datasets/picorv32/picorv32.v'
    wrapper = ROOT/'experiments/framework/pico_transfer_top.v'
    xml = out/'elaborated.xml'
    command = ['verilator', '--xml-only', '--xml-output', str(xml), '--Mdir',
               str(out), '--top-module', 'pico_transfer_top', '-Wno-fatal',
               '-Wno-PINMISSING', str(wrapper), str(rtl)]
    result = subprocess.run(command, capture_output=True, text=True)
    (out/'elaboration.log').write_text(result.stdout+result.stderr)
    if result.returncode:
        raise SystemExit(result.returncode)
    root = ET.parse(xml).getroot()
    tr = ArrayTranslator(root, 'pico_transfer_top')
    candidates = []
    for module in tr.modules.values():
        for proc in module.iter('always'):
            writers = [n[-1] for n in proc.iter() if n.tag in {'assign','assigndly'} and len(n)==2]
            if any(any(v.get('name')=='cpuregs' for v in lhs.iter('varref')) for lhs in writers):
                candidates.append((module,proc))
    if len(candidates)!=1:
        raise ValueError(f'expected one actual internal RF writer; found {len(candidates)}')
    module,proc = candidates[0]
    names = ['clk','resetn','cpuregs_write','latched_rd','cpuregs_wrdata','cpuregs']
    referenced = {v.get('name') for v in proc.iter('varref')}
    if referenced != set(names):
        raise ValueError(f'RF writer structure changed: {sorted(referenced)}')
    variables = {v.get('name'):v for v in module.iter('var')}
    env = {}
    for name in names:
        var = variables[name]
        info = SignalInfo(len(tr.signals),tr.width(var),f'pico_transfer_top.cpu.{name}',
                          loc_line(var),var.get('dir','internal'))
        tr.signals.append(info)
        env[name]=info
    # A five-bit index must span the original, unmodified 32-word bank.
    if (env['latched_rd'].width,env['cpuregs'].width)!=(5,1024):
        raise ValueError('configuration is not the existing 32-register Pico configuration')
    container = ET.Element('begin')
    container.append(proc)
    tr.module_items(container, env, 'pico_transfer_top.cpu')
    if len(tr.processes)!=1 or tr.unsupported:
        raise ValueError('selected writer failed exact translation')
    tr.reorder_combinational()
    unknowns = [{'value':n.get('name'),'loc':n.get('loc')} for n in root.iter('const')
                if any(c in n.get('name','').split("'",1)[-1].lower() for c in 'xz')]
    source_hashes=[{'path':str(p),'sha256':sha(p)} for p in (rtl,wrapper)]
    digest=hashlib.sha256(json.dumps(source_hashes,sort_keys=True).encode()).hexdigest()
    write_coq(out/'PicoRFWriterAST.v',tr,digest,sha(xml),{},'PicoRFWriterAST','pico_rf')
    report={'status':'actual_selected_rf_writer_not_full_cpu',
            'translation_equivalence':'not_mechanized_from_original_rtl',
            'source_hashes':source_hashes,'xml_sha256':sha(xml),'verilator_command':command,
            'actual_module':module.get('name'),'process_source_line':loc_line(proc),
            'selected_process_xml_sha256':hashlib.sha256(ET.tostring(proc)).hexdigest(),
            'signal_table':[vars(s) for s in tr.signals],
            'unknown_constants_elsewhere':unknowns,
            'rf_initialization':'REGS_INIT_ZERO defaults to 0; nonzero registers are unconstrained, not reset to zero',
            'whole_cpu_import':'pending X semantics / definedness proof'}
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({'status':report['status'],'unknown_constants':len(unknowns),
                      'rf_writer_line':loc_line(proc)}))

if __name__=='__main__':
    main()
